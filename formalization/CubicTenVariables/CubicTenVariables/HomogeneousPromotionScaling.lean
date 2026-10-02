import CubicTenVariables.MicrolocalPromotionCover
import TranslatedDepthSeven.DepthSevenRankSevenPacketAssembly

/-! Nonzero rational scaling for the literal finite principal opens and
for the actual promoted frequency sets. This supplies divisor-transfer
compatibility without imposing smoothness or lisse sheaf structures. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.HomogeneousPromotionScaling
open MvPolynomial HessianTheorem11 TranslatedDepthSeven
open ProjectiveMicrolocalData RationalConeClosure
open MicrolocalPromotionCover MicrolocalPromotedPartition
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem mem_smul_iff_of_stable {n : ℕ} (S : Set (Fin n → ℚ))
    (hS : ∀ (a : ℚ), a ≠ 0 → ∀ x ∈ S, a • x ∈ S)
    (a : ℚ) (ha : a ≠ 0) (x : Fin n → ℚ) : a • x ∈ S ↔ x ∈ S := by
  constructor
  · intro hx
    simpa only [smul_smul,inv_mul_cancel₀ ha,one_smul] using
      hS a⁻¹ (inv_ne_zero ha) (a • x) hx
  · exact hS a ha x

/-- Every literal componentwise principal open is invariant under every
nonzero rational scalar. Degrees can vary with the finite table entry. -/
theorem promotionOpen_smul_mem_iff {n c : ℕ}
    (I : Fin c → Ideal (MvPolynomial (Fin n) ℚ))
    (hI : ∀ i, (I i).IsHomogeneous (homogeneousSubmodule (Fin n) ℚ))
    (g : Fin c → MvPolynomial (Fin n) ℚ) (d : Fin c → ℕ)
    (hg : ∀ i, (g i).IsHomogeneous (d i))
    (a : ℚ) (ha : a ≠ 0) (x : Fin n → ℚ) :
    a • x ∈ promotionOpen I g ↔ x ∈ promotionOpen I g := by
  refine mem_smul_iff_of_stable _ ?_ a ha x
  intro b hb y ⟨i,hi,hne⟩
  refine ⟨i,smul_mem_affineIdealZeroLocus_of_isHomogeneous (I i) (hI i) hi b,?_⟩
  have he : eval (b • y) (g i) = b^(d i)*eval y (g i) := by
    simpa only [eval₂_id] using CubicGradientScaling.homogeneous_eval₂_smul
      (g i) (hg i) (RingHom.id ℚ) y b
  rw [he]
  exact mul_ne_zero (pow_ne_zero _ hb) hne

variable {t : ℕ} {F : MvPolynomial (Fin 10) ℤ}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}

/-- The depth filtration is the actual one from the homogeneous incidence,
including level zero, which is all rational frequencies. -/
theorem filtration_smul_mem_iff (h : Geometry F f) (j : ℕ)
    (a : ℚ) (ha : a ≠ 0) (x : Fin 10 → ℚ) :
    a • x ∈ filtration f j ↔ x ∈ filtration f j := by
  refine mem_smul_iff_of_stable _ ?_ a ha x
  intro b _ y hy
  by_cases hj : j = 0
  · subst j
    rw [filtration_zero]
    trivial
  · simp only [filtration,if_neg hj] at hy ⊢
    change rationalEmbedding (b • y) ∈ ProjectiveMicrolocalDepth.depth f j
    rw [rationalEmbedding_smul]
    exact ProjectiveMicrolocalDepth.depth_cone h j _ _ hy

/-- If each supplied promotion set is stable under nonzero rational
scaling, then every actual part, including the terminal nonzero part, is
invariant. Compatibility with the layers is unnecessary for this fact. -/
theorem part_smul_mem_iff (h : Geometry F f)
    (U : ℕ → Set (Fin 10 → ℚ))
    (hU : ∀ j (a : ℚ), a ≠ 0 → ∀ x ∈ U j, a • x ∈ U j)
    (j : Fin 6) (a : ℚ) (ha : a ≠ 0) (x : Fin 10 → ℚ) :
    a • x ∈ part f U j ↔ x ∈ part f U j := by
  have hUiff (k : ℕ) : a • x ∈ U k ↔ x ∈ U k :=
    mem_smul_iff_of_stable (U k) (hU k) a ha x
  by_cases hj : j.val < 5
  · simp only [part,PromotedFrequencyPartition.part,PromotedFrequencyPartition.promoted,
      PromotedFrequencyPartition.layer,if_pos hj,Set.mem_diff,Set.mem_union,
      Set.mem_singleton_iff,filtration_smul_mem_iff h _ a ha x,hUiff,
      smul_eq_zero,ha,false_or]
  · simp only [part,PromotedFrequencyPartition.part,PromotedFrequencyPartition.promoted,
      if_neg hj,Set.mem_diff,Set.mem_singleton_iff,
      filtration_smul_mem_iff h _ a ha x,smul_eq_zero,ha,false_or]

end CubicTenVariables.HomogeneousPromotionScaling
