import CubicTenVariables.GlobalSmithBound
import CubicTenVariables.CubeFullSmithProduct

/-! The selected weighted cube-full Smith bound in ten variables. -/

noncomputable section
namespace CubicTenVariables.CubeFullSmithBound
open MvPolynomial HessianTheorem11 CubeFullSmithParameters SmithProfileNumerics
open scoped BigOperators

instance parameterANeZero (r : ℕ) : NeZero (A r) := ⟨(A_pos r).ne'⟩
instance parameterTNeZero (r : ℕ) : NeZero (T r) := ⟨(T_pos r).ne'⟩

theorem prod_A_primeFactors (r : ℕ) (hc : CubeFull r) :
    (∏ p : r.primeFactors, (p : ℕ)^((A r).factorization p)) = A r := by
  rw [Finset.prod_coe_sort r.primeFactors (fun p : ℕ => p^((A r).factorization p)),
    ← primeFactors_A r hc]
  simpa only [Nat.prod_factorization_eq_prod_primeFactors] using
    Nat.factorization_prod_pow_eq_self (A_pos r).ne'

theorem prod_T_primeFactors (r : ℕ) (hc : CubeFull r) :
    (∏ p : r.primeFactors, (p : ℕ)^((T r).factorization p)) = T r := by
  rw [Finset.prod_coe_sort r.primeFactors (fun p : ℕ => p^((T r).factorization p)),
    ← primeFactors_T r hc]
  simpa only [Nat.prod_factorization_eq_prod_primeFactors] using
    Nat.factorization_prod_pow_eq_self (T_pos r).ne'

/-- The uniform threshold is chosen before the modulus and all weights. -/
theorem exists_uniform_global_bound 
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℕ, 3 ≤ P ∧ ∀ r : ℕ, 0 < r → CubeFull r →
      (∀ p ∈ r.primeFactors, P ≤ p) →
      ∀ (V : Finset (Fin 10 → ℤ)) (w : (Fin 10 → ℤ) → ℝ),
      (∀ v ∈ V, 0 ≤ w v) →
        (∑ v ∈ V, w v * ‖completeCubicSum F r v‖) ≤
          (r : ℝ)^ε * WeightedResidueMaximum.maximum (A r) V w *
            ∏ p ∈ r.primeFactors,
              (p : ℝ)^(localD ((A r).factorization p) ((T r).factorization p) : ℝ) := by
  obtain ⟨P,hP,hbound⟩ := SmithProfileMassBound.exists_uniform_bound  F hF hA ε hε
  refine ⟨P,hP,?_⟩
  intro r hr hc helig V w hw
  let p : r.primeFactors → ℕ := fun p => p.val
  let a : r.primeFactors → ℕ := fun p => (A r).factorization p
  let t : r.primeFactors → ℕ := fun p => (T r).factorization p
  letI : ∀ i : r.primeFactors, Fact (p i).Prime :=
    fun i => ⟨Nat.prime_of_mem_primeFactors i.property⟩
  have ha (i : r.primeFactors) : 1 ≤ a i := by
    dsimp [a]
    rw [factorization_A_of_mem r i i.property]
    have h := quotient_pos_of_mem r hc i i.property
    omega
  have hcase (i : r.primeFactors) : t i ≤ a i ∨ p i ≠ 2 := by
    right
    have hi := hP.trans (helig i i.property)
    dsimp [p]
    omega
  have hm (i : r.primeFactors) := hbound (p i) (helig i i.property) (a i) (ha i) (t i)
  have h := GlobalSmithBound.weighted_completeCubicSum_le F hF p
    (fun i j hij => Subtype.ext hij) a t hcase ε hε.le hm V w hw
  simpa only [p,a,t,prod_A_primeFactors r hc,prod_T_primeFactors r hc,
    ← eq_A_sq_mul_T r hr,
    Finset.prod_coe_sort r.primeFactors (fun p : ℕ =>
      (p : ℝ)^(localD ((A r).factorization p) ((T r).factorization p) : ℝ))] using h

/-- Literal source estimate, including the empty prime support r=1.
No unproved literature premise remains. -/
theorem exists_uniform_bound 
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℕ, 3 ≤ P ∧ ∀ r : ℕ, 0 < r → CubeFull r →
      (∀ p ∈ r.primeFactors, P ≤ p) →
      ∀ (V : Finset (Fin 10 → ℤ)) (w : (Fin 10 → ℤ) → ℝ),
      (∀ v ∈ V, 0 ≤ w v) →
        (∑ v ∈ V, w v * ‖completeCubicSum F r v‖) ≤
          (r : ℝ)^(10+ε) * (z r 0 : ℝ)^(-2 : ℝ) *
            (z r 1 : ℝ)^(-4 : ℝ) * (z r 2 : ℝ)^(-1 : ℝ) *
              WeightedResidueMaximum.maximum (A r) V w := by
  obtain ⟨P,hP,hbound⟩ := exists_uniform_global_bound  F hF hA ε hε
  refine ⟨P,hP,?_⟩
  intro r hr hc helig V w hw
  letI : NeZero (A r) := ⟨(A_pos r).ne'⟩
  have hE := WeightedResidueMaximum.maximum_nonneg (A r) V w hw
  calc
    _ ≤ (r : ℝ)^ε * WeightedResidueMaximum.maximum (A r) V w *
        ∏ p ∈ r.primeFactors,
          (p : ℝ)^(localD ((A r).factorization p) ((T r).factorization p) : ℝ) :=
      hbound r hr hc helig V w hw
    _ ≤ (r : ℝ)^ε * WeightedResidueMaximum.maximum (A r) V w *
        ((r : ℝ)^10 * (z r 0 : ℝ)^(-2 : ℝ) *
          (z r 1 : ℝ)^(-4 : ℝ) * (z r 2 : ℝ)^(-1 : ℝ)) :=
      mul_le_mul_of_nonneg_left (CubeFullSmithProduct.prod_localD_le r hr hc)
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg r) ε) hE)
    _ = _ := by
      rw [Real.rpow_add (by exact_mod_cast hr)]
      norm_num
      ring

end CubicTenVariables.CubeFullSmithBound
