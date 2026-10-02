import CubicTenVariables.SmallDegreeConeOpenTraceBound
import CubicTenVariables.HomogeneousPrincipalOpen
import CubicTenVariables.HomogeneousComponentOpen
import CubicTenVariables.HomogeneousConeReduction
import CubicTenVariables.FourierScalarInvariance

/-! Homogeneous principal opens carrying the actual small-degree cone trace
bounds. The proper-hyperplane weight literature premise supplies an
initial open. A homogeneous component and finite-field scalar substitution
then give a homogeneous open without any additional literature input.
The actual reduced generators are made scalar-stable by proved denominator
clearing. Constants precede the good prime, finite field and character.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace CubicTenVariables.HomogeneousConeTraceBound
open MvPolynomial HessianTheorem11 ProjectiveFourierIdentity
open TranslatedDepthSeven FiniteFieldTraceCharacter PolynomialExponentialFamily
open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A homogeneous dense principal open in the actual rational cone, with
positive degree excluding the vertex, supports the literal all-extension
trace bound. The documented hypotheses and proved integrality inputs remain explicit. -/
theorem exists_bound
    (degreeSpan : StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (smooth : Literature.SmoothInfinityGeometricIntegrality)
    (spread : CubicGenericIntegralityUniform.Uniform)
    (weil : Literature.AffinePlaneCubicWeil)
    (dichotomy : Literature.ProperHyperplaneWeightDichotomy)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    {t : ℕ} (G : Fin t → MvPolynomial (Fin 10) ℤ) (r d w : ℕ)
    (hprime : (baseIdeal G).IsPrime)
    (hgeometric : ((baseIdeal G).map (MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime)
    (hhom : (baseIdeal G).IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ))
    (hdegree : Published.HasProjectiveDimensionDegree (baseIdeal G) r d)
    (hsmall : r+d ≤ 8) (hweight : r+1+w+1 = 18) :
    ∃ (h : ParameterPolynomial 10) (j N C : ℕ),
      0 < j ∧ h.IsHomogeneous j ∧ map (Int.castRingHom ℚ) h ∉ baseIdeal G ∧
      1 ≤ N ∧ 1 ≤ C ∧
      ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ N →
        ∀ (ψ : AddChar (ZMod p) ℂ), ψ ≠ 1 →
        ∀ (K : Type) [Field K] [Fintype K] [CharP K p]
          (v : Fin 10 → K), v ∈ parameterPoints G h K →
          ‖normalizedFourierSum (primeTraceCharacter p K ψ)
            (map (Int.castRingHom K) F) v‖ ≤
              (C : ℝ) * (Fintype.card K : ℝ)^((w : ℝ)/2) := by
  obtain ⟨i,hi⟩ := ConePrincipalOpen.exists_coordinate_not_mem 9 r
    (baseIdeal G) hprime hdegree.1
  obtain ⟨g,N,C,hg,hig,hN,hC,hbound⟩ := SmallDegreeConeOpenTraceBound.exists_open_bound
    degreeSpan smooth spread weil dichotomy F hF hAn G r d w
    hprime hgeometric hhom hdegree hsmall hweight i hi
  obtain ⟨j,hj,_hjdeg,hjI,hjhom⟩ :=
    HomogeneousComponentOpen.exists_positive_component (baseIdeal G) g i hg hig
  obtain ⟨D,hD,hstable⟩ := HomogeneousConeReduction.exists_scalar_stability G hhom
  refine ⟨homogeneousComponent j g,j,(N*D)*(g.totalDegree+1).factorial,C,
    hj,hjhom,hjI,?_,hC,?_⟩
  · exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hN hD) (Nat.factorial_pos _)
  intro p _ hp ψ hψ K _ _ _ v hv
  have hpN : ¬ p ∣ N := fun h =>
    hp (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h D) _)
  have hpD : ¬ p ∣ D := fun h =>
    hp (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h N) _)
  have hpf : ¬ p ∣ (g.totalDegree+1).factorial := fun h =>
    hp (dvd_mul_of_dvd_right h (N*D))
  obtain ⟨hvG,hvh⟩ := (mem_parameterPoints G (homogeneousComponent j g) K v).mp hv
  obtain ⟨a,ha,hag⟩ := HomogeneousComponentOpen.exists_nonzero_scalar_integer g v j hvh
    (HomogeneousPrincipalOpen.cutoff_lt_card (g.totalDegree+1) p hpf K)
  have hav : a • v ∈ parameterPoints G g K :=
    (mem_parameterPoints G g K _).mpr ⟨hstable p hpD K v hvG a,hag⟩
  have hb := hbound p hpN ψ hψ K (a • v) hav
  rw [FourierScalarInvariance.normalizedFourierSum_map_smul _ F hF v a ha] at hb
  exact hb

/-- The homogeneous open also carries the literal prime complete-sum
estimate. Its complementary ideal is homogeneous and its actual closed
residual is proper of dimension at most r. -/
theorem exists_complete_sum_bound
    (degreeSpan : StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (smooth : Literature.SmoothInfinityGeometricIntegrality)
    (spread : CubicGenericIntegralityUniform.Uniform)
    (weil : Literature.AffinePlaneCubicWeil)
    (dichotomy : Literature.ProperHyperplaneWeightDichotomy)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    {t : ℕ} (G : Fin t → MvPolynomial (Fin 10) ℤ) (r d w : ℕ)
    (hprime : (baseIdeal G).IsPrime)
    (hgeometric : ((baseIdeal G).map (MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime)
    (hhom : (baseIdeal G).IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ))
    (hdegree : Published.HasProjectiveDimensionDegree (baseIdeal G) r d)
    (hsmall : r+d ≤ 8) (hweight : r+1+w+1 = 18) :
    ∃ (h : ParameterPolynomial 10) (j N C : ℕ),
      0 < j ∧ h.IsHomogeneous j ∧ map (Int.castRingHom ℚ) h ∉ baseIdeal G ∧
      1 ≤ N ∧ 1 ≤ C ∧
      (ConePrincipalOpen.residualIdeal (baseIdeal G) (map (Int.castRingHom ℚ) h)).IsHomogeneous
        (homogeneousSubmodule (Fin 10) ℚ) ∧
      ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸
        ConePrincipalOpen.residualIdeal (baseIdeal G) (map (Int.castRingHom ℚ) h)) ≤
          (r : WithBot ℕ∞) ∧
      PrimeSpectrum.zeroLocus (ConePrincipalOpen.residualIdeal (baseIdeal G)
        (map (Int.castRingHom ℚ) h) : Set (MvPolynomial (Fin 10) ℚ)) ⊂
          PrimeSpectrum.zeroLocus (baseIdeal G : Set (MvPolynomial (Fin 10) ℚ)) ∧
      ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ N →
        ∀ v : Fin 10 → ℤ,
          (fun i => (v i : ZMod p)) ∈ parameterPoints G h (ZMod p) →
          ‖completeCubicSum F p v‖ ≤ (C : ℝ)*(p : ℝ)^((w : ℝ)/2+1) := by
  obtain ⟨h,j,N,C,hj,hh,hI,hN,hC,hbound⟩ := exists_bound
    degreeSpan smooth spread weil dichotomy F hF hAn G r d w
    hprime hgeometric hhom hdegree hsmall hweight
  refine ⟨h,j,N,C,hj,hh,hI,hN,hC,
    HomogeneousPrincipalOpen.residual_isHomogeneous _ hhom _ j (hh.map _),
    ConePrincipalOpen.residual_dimension_le _ hprime _ hI r hdegree.1,
    ConePrincipalOpen.residual_zeroLocus_ssubset _ hprime _ hI,?_⟩
  intro p _ hpN v hv
  have hb := hbound p hpN ZMod.stdAddChar (PrimeSumAdapter.stdAddChar_ne_one p)
    (ZMod p) (fun i => (v i : ZMod p)) hv
  rw [ZMod.card] at hb
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [SmallDegreeConeTraceCharacters.completeCubicSum_eq_prime_mul_normalized
    (by omega : 1 ≤ 10), norm_mul, Complex.norm_natCast]
  calc
    (p : ℝ)*_ ≤ (p : ℝ)*((C : ℝ)*(p : ℝ)^((w : ℝ)/2)) :=
      mul_le_mul_of_nonneg_left hb hp.le
    _ = (C : ℝ)*(p : ℝ)^((w : ℝ)/2+1) := by
      rw [Real.rpow_add hp, Real.rpow_one]
      ring

end CubicTenVariables.HomogeneousConeTraceBound
