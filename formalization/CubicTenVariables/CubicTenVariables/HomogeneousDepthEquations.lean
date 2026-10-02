import CubicTenVariables.UniversalLinearCutDeterminant
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.Noetherian.Defs

/-! A finite equation list for the large-dimensional fibers of a fixed
homogeneous polynomial family over a Noetherian coefficient ring. The list
is chosen before every infinite target field and coefficient specialization.
The equations need not be reduced or homogeneous in any parameter grading;
no reduced model or good-characteristic spreading assertion is made here. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.HomogeneousDepthEquations
open MvPolynomial HomogeneousMacaulayCertificates UniversalHomogeneousCombinations
open UniversalLinearCutDeterminant

/-- Over an infinite field, vanishing at every assignment is exactly
vanishing of all specialized coefficients. -/
theorem forall_eval₂_eq_zero_iff {R K σ : Type*} [CommRing R] [Field K] [Infinite K]
    (ρ : R →+* K) (P : MvPolynomial σ R) :
    (∀ a : σ → K, eval₂Hom ρ a P = 0) ↔ ∀ d, ρ (coeff d P) = 0 := by
  constructor
  · intro h
    have heq : map ρ P = 0 := MvPolynomial.funext (fun a => by
      simpa only [eval_zero, ← eval₂_eq_eval_map] using h a)
    intro d
    have hd := congrArg (coeff d) heq
    simpa only [coeff_map, coeff_zero] using hd
  · intro h a
    have heq : map ρ P = 0 := by
      ext d
      simpa only [coeff_map, coeff_zero] using h d
    simpa only [← eval₂_eq_eval_map, eval_zero] using congrArg (eval a) heq

/-- Two layers of auxiliary variables are eliminated by literal iterated
coefficients, without changing the original coefficient ring. -/
theorem forall_iterated_eval₂_eq_zero_iff {R K α β : Type*}
    [CommRing R] [Field K] [Infinite K]
    (ρ : R →+* K) (P : MvPolynomial α (MvPolynomial β R)) :
    (∀ (b : β → K) (a : α → K), eval₂Hom (eval₂Hom ρ b) a P = 0) ↔
      ∀ u v, ρ (coeff v (coeff u P)) = 0 := by
  constructor
  · intro h u
    apply (forall_eval₂_eq_zero_iff ρ (coeff u P)).mp
    intro b
    exact (forall_eval₂_eq_zero_iff (eval₂Hom ρ b) P).mp (h b) u
  · intro h b
    apply (forall_eval₂_eq_zero_iff (eval₂Hom ρ b) P).mpr
    intro u
    exact (forall_eval₂_eq_zero_iff ρ (coeff u P)).mpr (h u) b

variable {R : Type*} [CommRing R] {n : ℕ} {ι : Type*} [Fintype ι]

/-- All iterated coefficients of the actual positive-degree cut determinants. -/
def coefficientSet (f : ι → MvPolynomial (Fin n) R) (e : ι → ℕ) (t : ℕ) : Set R :=
  {z | ∃ N : ℕ, 0 < N ∧
    ∃ u : CoefficientVariable n N (cutDegrees e t) →₀ ℕ,
    ∃ v : CutVariable n t →₀ ℕ,
      z = coeff v (coeff u (cutDeterminant f e t N))}

/-- The coefficient ideal is formed over the original base ring. -/
def depthIdeal (f : ι → MvPolynomial (Fin n) R) (e : ι → ℕ) (t : ℕ) : Ideal R :=
  Ideal.span (coefficientSet f e t)

/-- Exact fieldwise vanishing criterion for this one base-ring ideal. -/
theorem depthIdeal_le_ker_iff {K : Type*} [Field K] [Infinite K]
    (ρ : R →+* K) (f : ι → MvPolynomial (Fin n) R) (e : ι → ℕ)
    (hf : ∀ j, (f j).IsHomogeneous (e j)) (t : ℕ) :
    depthIdeal f e t ≤ RingHom.ker ρ ↔
      (t : WithBot ℕ∞) < ringKrullDim (MvPolynomial (Fin n) K ⧸
        Ideal.span (Set.range (fun j => map ρ (f j)))) := by
  rw [depthIdeal, Ideal.span_le]
  constructor
  · intro h
    apply lt_of_not_ge
    intro hdim
    obtain ⟨N, hN, b, a, ha⟩ :=
      (dimension_le_iff_exists_determinant ρ f e hf).mp hdim
    apply ha
    have hz : ∀ u v, ρ (coeff v (coeff u (cutDeterminant f e t N))) = 0 :=
      fun u v => h ⟨N, hN, u, v, rfl⟩
    exact (forall_iterated_eval₂_eq_zero_iff ρ (cutDeterminant f e t N)).mpr hz b a
  · intro hdim z hz
    obtain ⟨N, hN, u, v, rfl⟩ := hz
    change ρ (coeff v (coeff u (cutDeterminant f e t N))) = 0
    apply (forall_iterated_eval₂_eq_zero_iff ρ (cutDeterminant f e t N)).mp ?_ u v
    intro b a
    by_contra hne
    exact (not_le_of_gt hdim)
      (dimension_le_of_determinant_ne_zero ρ f e hf hN b a hne)

/-- Noetherian finite generation gives one finite list of base-ring equations
before all infinite-field specializations. Its zeros are exactly the fibers
whose actual homogeneous equation quotient has dimension greater than `t`. -/
theorem exists_equations [IsNoetherianRing R]
    (f : ι → MvPolynomial (Fin n) R) (e : ι → ℕ)
    (hf : ∀ j, (f j).IsHomogeneous (e j)) (t : ℕ) :
    ∃ r : ℕ, ∃ G : Fin r → R,
      Ideal.span (Set.range G) = depthIdeal f e t ∧
      ∀ (K : Type*) [Field K] [Infinite K] (ρ : R →+* K),
        (∀ i, ρ (G i) = 0) ↔
          (t : WithBot ℕ∞) < ringKrullDim (MvPolynomial (Fin n) K ⧸
            Ideal.span (Set.range (fun j => map ρ (f j)))) := by
  obtain ⟨r, G, hG⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (depthIdeal f e t))
  refine ⟨r, G, hG, ?_⟩
  intro K _ _ ρ
  rw [← depthIdeal_le_ker_iff ρ f e hf t, ← hG, Submodule.span_le]
  simp only [Set.range_subset_iff]
  rfl

end CubicTenVariables.HomogeneousDepthEquations
