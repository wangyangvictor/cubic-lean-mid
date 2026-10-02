import CubicTenVariables.PlanAlphaModulusDecomposition
import CubicTenVariables.ComplementDyadicScales
import CubicTenVariables.FixedPrimeSupportCount

/-! Canonical mixed-modulus block indices and their actual finite cover.
The number of occupied blocks has a uniform subpower bound for a fixed
finite excluded prime set. No frequency grouping or analytic estimate is
assumed here. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PlanAlphaBlockIndices
open PlanAlphaModulusDecomposition ComplementDyadicScales
open scoped BigOperators

/-- The excluded factor and the two canonical dyadic exponents. -/
def blockIndex (s : Finset ℕ) (q : ℕ) : ℕ × ℕ × ℕ :=
  (g s q,Nat.log2 (d s q),Nat.log2 (r s q))

/-- The dyadic product differs from the actual modulus by a factor less
than four. All factors, including the unit factors, are retained. -/
theorem canonical_bounds (s : Finset ℕ) (q : ℕ) (hq : 0 < q) :
    let D : ℝ := 2^(blockIndex s q).2.1
    let C : ℝ := 2^(blockIndex s q).2.2
    1 ≤ D ∧ 1 ≤ C ∧ (g s q : ℝ)*D*C ≤ (q : ℝ) ∧
      (q : ℝ) < 4*(g s q : ℝ)*D*C := by
  dsimp only [blockIndex]
  rw [Nat.log2_eq_log_two,Nat.log2_eq_log_two]
  obtain ⟨hD,hDd,hdD⟩ := canonical_scale_bounds (d s q) (d_pos s q)
  obtain ⟨hC,hCr,hrC⟩ := canonical_scale_bounds (r s q) (r_pos s q)
  have hg0 : 0 < (g s q : ℝ) := by exact_mod_cast g_pos s q
  have hr0 : 0 < (r s q : ℝ) := by exact_mod_cast r_pos s q
  have hrec : (q : ℝ) = (g s q : ℝ)*(d s q : ℝ)*(r s q : ℝ) := by
    exact_mod_cast reconstruction s q hq
  refine ⟨hD,hC,?_,?_⟩
  · rw [hrec]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hDd hg0.le) hCr
      (by positivity) (by positivity)
  · rw [hrec]
    have hprod := mul_lt_mul hdD hrC.le hr0 (by positivity)
    have hh := mul_lt_mul_of_pos_left hprod hg0
    nlinarith

/-- Bounds in an actual dyadic modulus window, with an explicit finite
range for both canonical exponents. The factor eight is a permissible
weakening of the strict factor-four comparison. -/
theorem dyadic_bounds (s : Finset ℕ) (q : ℕ) (Q : ℝ)
    (hq : 0 < q) (hQ : 1 ≤ Q) (hlo : Q ≤ (q : ℝ)) (hhi : (q : ℝ) ≤ 2*Q) :
    let D : ℝ := 2^(blockIndex s q).2.1
    let C : ℝ := 2^(blockIndex s q).2.2
    1 ≤ D ∧ 1 ≤ C ∧ (g s q : ℝ)*D*C ≤ 2*Q ∧
      Q ≤ 8*(g s q : ℝ)*D*C ∧
      (blockIndex s q).2.1 < indexCount Q ∧ (blockIndex s q).2.2 < indexCount Q := by
  obtain ⟨hD,hC,hprod,hupper⟩ := canonical_bounds s q hq
  have hdq : (d s q : ℝ) ≤ 2*Q :=
    (by exact_mod_cast d_le s q hq : (d s q : ℝ) ≤ (q : ℝ)).trans hhi
  have hrq : (r s q : ℝ) ≤ 2*Q :=
    (by exact_mod_cast r_le s q hq : (r s q : ℝ) ≤ (q : ℝ)).trans hhi
  refine ⟨hD,hC,hprod.trans hhi,?_,?_,?_⟩
  · have hg : 0 ≤ (g s q : ℝ) := Nat.cast_nonneg _
    have hp : 0 ≤ (g s q : ℝ)*(2 : ℝ)^(blockIndex s q).2.1*
        (2 : ℝ)^(blockIndex s q).2.2 := by positivity
    nlinarith
  · simpa only [blockIndex,Nat.log2_eq_log_two] using canonical_index_lt Q (d s q) hdq
  · simpa only [blockIndex,Nat.log2_eq_log_two] using canonical_index_lt Q (r s q) hrq

/-- A literal product cover for the occupied indices. -/
def indexCover (s : Finset ℕ) (Q : ℝ) (U : Finset ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (U.image (g s)) ×ˢ ((Finset.range (indexCount Q)) ×ˢ (Finset.range (indexCount Q)))

theorem image_subset_cover (s : Finset ℕ) (Q : ℝ) (U : Finset ℕ)
    (hU : ∀ q ∈ U, 0 < q ∧ (q : ℝ) ≤ 2*Q) :
    U.image (blockIndex s) ⊆ indexCover s Q U := by
  classical
  intro x hx
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
  have hdq : (d s q : ℝ) ≤ 2*Q :=
    (by exact_mod_cast d_le s q (hU q hq).1 : (d s q : ℝ) ≤ (q : ℝ)).trans (hU q hq).2
  have hrq : (r s q : ℝ) ≤ 2*Q :=
    (by exact_mod_cast r_le s q (hU q hq).1 : (r s q : ℝ) ≤ (q : ℝ)).trans (hU q hq).2
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_image.mpr ⟨q,hq,rfl⟩,Finset.mem_product.mpr ⟨?_,?_⟩⟩
  · apply Finset.mem_range.mpr
    simpa only [blockIndex,Nat.log2_eq_log_two] using canonical_index_lt Q (d s q) hdq
  · apply Finset.mem_range.mpr
    simpa only [blockIndex,Nat.log2_eq_log_two] using canonical_index_lt Q (r s q) hrq

theorem card_cover (s : Finset ℕ) (Q : ℝ) (U : Finset ℕ) :
    (indexCover s Q U).card = (U.image (g s)).card*(indexCount Q)^2 := by
  simp [indexCover,Finset.card_product,pow_two]

/-- The actual occupied block set is uniformly bounded by any positive
power of Q. The excluded prime set is fixed before the bound constant. -/
theorem exists_count_bound (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ Q : ℝ, 1 ≤ Q → ∀ U : Finset ℕ,
      (∀ q ∈ U, 0 < q ∧ (q : ℝ) ≤ 2*Q) →
      ((U.image (blockIndex s)).card : ℝ) ≤ K*Q^ε := by
  classical
  have heps : 0 < ε/2 := by positivity
  obtain ⟨Cg,hCg,hg⟩ := FixedPrimeSupportCount.exists_bound s hprimes (ε/2) heps
  obtain ⟨Cd,hCd,hd⟩ := ComplementDyadicScales.exists_count_bound (ε/2) heps
  refine ⟨Cg*(2 : ℝ)^(ε/2)*Cd,
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hCg (Real.one_le_rpow (by norm_num) heps.le)) hCd,?_⟩
  intro Q hQ U hU
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hgf : ∀ z ∈ U.image (g s), 0 < z ∧ z.primeFactors ⊆ s ∧ (z : ℝ) ≤ 2*Q := by
    intro z hz
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
    refine ⟨g_pos s q,g_supported s q,?_⟩
    exact (by exact_mod_cast g_le s q (hU q hq).1 :
      (g s q : ℝ) ≤ (q : ℝ)).trans (hU q hq).2
  have hgb := hg (2*Q) (by linarith) (U.image (g s)) hgf
  have hib : (indexCount Q : ℝ)^2 ≤ Cd*Q^(ε/2) :=
    (pow_le_pow_right₀ (by exact_mod_cast indexCount_pos Q) (by norm_num : 2 ≤ 10)).trans (hd Q hQ)
  have hcard : ((U.image (blockIndex s)).card : ℝ) ≤
      ((U.image (g s)).card : ℝ)*(indexCount Q : ℝ)^2 := by
    have hc := Finset.card_le_card (image_subset_cover s Q U hU)
    rw [card_cover] at hc
    exact_mod_cast hc
  calc
    _ ≤ ((U.image (g s)).card : ℝ)*(indexCount Q : ℝ)^2 := hcard
    _ ≤ (Cg*(2*Q)^(ε/2))*(Cd*Q^(ε/2)) :=
      mul_le_mul hgb hib (by positivity) (by positivity)
    _ = (Cg*(2 : ℝ)^(ε/2)*Cd)*Q^ε := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hQ0.le]
      have hh : Q^(ε/2)*Q^(ε/2) = Q^ε := by
        rw [← Real.rpow_add hQ0]
        congr 1
        ring
      calc
        _ = (Cg*(2 : ℝ)^(ε/2)*Cd)*(Q^(ε/2)*Q^(ε/2)) := by ring
        _ = _ := by rw [hh]

end CubicTenVariables.PlanAlphaBlockIndices
