import CubicTenVariables.FixedLeadingSurfaceFiniteFieldCount
import CubicTenVariables.FixedLeadingSurfaceCoordinateTransport
import CubicTenVariables.FixedLeadingFormCoefficientReduction
import TranslatedDepthSeven.HypersurfaceOccupiedSmoothResidues
import Mathlib.Data.Nat.Prime.Factorial

/-!
# Uniform prime counts for the actual varying affine equations

For a fixed integral leading form k, select one nonzero coefficient a.
For each varying g with rational leading scalar, let b be its corresponding
top coefficient. Cross multiplication gives a*top(g)=b*k integrally, so at
every prime avoiding a*b the actual reduced top is (b/a)*k. The uniform
finite-field theorem therefore applies to the actual homogenization of g.

One positive integer D is chosen before g and its scalar. The only varying
excluded factor is the actual coefficient b, bounded by height(g). No bound
depending on the remaining coefficients is hidden in D or the field-size
threshold. The two literature premises remain explicit.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace CubicTenVariables.FixedLeadingSurfacePrimeCountUniform

open MvPolynomial TranslatedDepthSeven Published
open HessianTheorem11.PolynomialRestriction
open FixedBoundaryPencilUniformity FixedLeadingFormIntegralShear
open FixedLeadingFormCoefficientReduction
open FixedLeadingSurfaceCoordinateTransport

theorem restrict_zero_homogenize
    {R : Type*} [CommRing R] (d : ℕ) (g : MvPolynomial (Fin 3) R) :
    restrict (pencilFrame (0 : R)) (homogenize d g) = homogeneousComponent d g := by
  have heq : (aeval (linearForms (pencilFrame (0 : R)))).toRingHom =
      FixedLeadingSurfaceCoordinateTransport.boundaryHom R := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [FixedLeadingSurfaceCoordinateTransport.boundaryHom]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [FixedLeadingSurfaceCoordinateTransport.boundaryHom,
          linearForms, pencilFrame, graphFrame]
      · simp [FixedLeadingSurfaceCoordinateTransport.boundaryHom,
          linearForms, pencilFrame, graphFrame, Matrix.one_apply]
  change (aeval (linearForms (pencilFrame (0 : R)))).toRingHom (homogenize d g) = _
  rw [heq]
  exact boundaryHom_homogenize d g

/-- A fixed integer controls the primes for the entire lower-coefficient
family. The displayed varying coefficient remains bounded by the original
equation's literal maximum absolute coefficient. -/
theorem exists_fixed_leading_prime_count
    (integralityOpen : Literature.HomogeneousHypersurfaceIntegralityOpen)
    (curveWeil : Literature.AffinePlaneCurveWeil)
    {d : ℕ} (hd : 2 ≤ d)
    (k : MvPolynomial (Fin 3) ℤ) (hk : k.IsHomogeneous d)
    (hirr : IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) k))
    (K₀ : ℝ) (hK₀ : 1 < K₀) :
    ∃ (μ : Fin 3 →₀ ℕ) (D : ℕ), 0 < D ∧ k.coeff μ ≠ 0 ∧
      ∀ (g : MvPolynomial (Fin 3) ℤ) (c : ℚ), c ≠ 0 →
        g.totalDegree ≤ d →
        map (Int.castRingHom ℚ) (homogeneousComponent d g) =
          C c * map (Int.castRingHom ℚ) k →
        (homogeneousComponent d g).coeff μ ≠ 0 ∧
        ((homogeneousComponent d g).coeff μ).natAbs ≤ mvPolynomialCoefficientNatAbsMax g ∧
        ∀ p : ℕ, p.Prime →
          ¬ p ∣ D * ((homogeneousComponent d g).coeff μ).natAbs →
          (Nat.card (SurfaceReductionZeroPoint p g) : ℝ) ≤ K₀ * (p : ℝ) ^ 2 := by
  classical
  obtain ⟨N, hN, T, _hT, hcount⟩ :=
    FixedLeadingSurfaceFiniteFieldCount.exists_uniform_count
      integralityOpen curveWeil hd k hk hirr K₀ hK₀
  have hk0 : k ≠ 0 := by
    intro hz
    exact hirr.ne_zero (by rw [hz, map_zero])
  obtain ⟨μ, ha⟩ := MvPolynomial.exists_coeff_ne_zero hk0
  let A : ℕ := (k.coeff μ).natAbs
  let threshold : ℕ := Nat.ceil T
  let D : ℕ := N * A * threshold.factorial
  have hA : 0 < A := Int.natAbs_pos.mpr ha
  have hD : 0 < D := Nat.mul_pos (Nat.mul_pos hN hA) (Nat.factorial_pos threshold)
  have hND : N ∣ D := ⟨A * threshold.factorial, by simp [D, mul_assoc]⟩
  have hAD : A ∣ D := ⟨N * threshold.factorial, by dsimp only [D]; ring⟩
  have hTD : threshold.factorial ∣ D := ⟨N * A, by dsimp only [D]; ring⟩
  refine ⟨μ, D, hD, ha, ?_⟩
  intro g c hc hdegree htop
  obtain ⟨hb, _hcross, hheight⟩ := top_coefficient_certificate μ htop hc ha
  refine ⟨hb, hheight, ?_⟩
  intro p hp hpDb
  letI : Fact p.Prime := ⟨hp⟩
  have hpD : ¬ p ∣ D := fun h => hpDb (dvd_mul_of_dvd_left h _)
  have hpN : ¬ p ∣ N := fun h => hpD (h.trans hND)
  have hpFact : ¬ p ∣ threshold.factorial := fun h => hpD (h.trans hTD)
  have hTp : threshold < p := by
    rw [hp.dvd_factorial] at hpFact
    exact lt_of_not_ge hpFact
  have hthreshold : T ≤ (Fintype.card (ZMod p) : ℝ) := by
    rw [ZMod.card]
    exact (Nat.le_ceil T).trans (by exact_mod_cast hTp.le)
  have hab : ¬ (p : ℤ) ∣ k.coeff μ * (homogeneousComponent d g).coeff μ := by
    intro hab
    have habNat : p ∣ A * ((homogeneousComponent d g).coeff μ).natAbs := by
      simpa only [A, Int.natAbs_mul] using (Int.natCast_dvd.mp hab)
    exact hpDb (habNat.trans (Nat.mul_dvd_mul hAD (dvd_refl _)))
  obtain ⟨hscalar, htopK⟩ := top_reduction_zmod_of_not_dvd_coeff_product μ htop hab
  let gK := map (Int.castRingHom (ZMod p)) g
  have hdegreeK : gK.totalDegree ≤ d :=
    (Finset.sup_mono (support_map_subset _ _)).trans hdegree
  have hNK : (N : ZMod p) ≠ 0 := fun hz => hpN ((ZMod.natCast_eq_zero_iff N p).mp hz)
  have hboundary : restrict (pencilFrame (0 : ZMod p)) (homogenize d gK) =
      C ((((homogeneousComponent d g).coeff μ : ℤ) : ZMod p) /
        ((k.coeff μ : ℤ) : ZMod p)) * map (Int.castRingHom (ZMod p)) k := by
    rw [restrict_zero_homogenize]
    exact htopK
  have hresult := hcount (ZMod p) (homogenize d gK) _
    (homogenize_isHomogeneous d gK) hboundary hNK hscalar hthreshold
  rw [standardDehomogenizationHom_homogenize d gK hdegreeK] at hresult
  simpa only [gK, ZMod.card, SurfaceReductionZeroPoint] using hresult

end CubicTenVariables.FixedLeadingSurfacePrimeCountUniform
