import CubicTenVariables.StratifiedLargeSlice
import CubicTenVariables.StratifiedSmallRangeNumerics
import CubicTenVariables.StratifiedLargeRangeNumerics

/-! Summation of the pivot-sieve bounds over actual tail modulus tuples.
This proves the required large-product term at any suitable pivot. -/
noncomputable section
namespace CubicTenVariables.StratifiedLargeRange
open MvPolynomial IntegralLinearNormalization StratifiedSieveData StratifiedModuli
open scoped BigOperators
variable {n s : ℕ}

theorem exists_bound (t d : Fin s → ℕ)
    (G : ∀ i, Fin (t i) → MvPolynomial (Fin n) ℤ)
    (hproper : ∀ i, IntegralModelDimension.rationalIdeal (G i) ≠ ⊤)
    (hdim : ∀ i, ringKrullDim (MvPolynomial (Fin n) ℚ ⧸
      IntegralModelDimension.rationalIdeal (G i)) ≤ (d i : WithBot ℕ∞))
    (j : Fin s) (D : Certificate (ideal t G j) (d j)) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ C : ℝ, c ≤ C → ∃ K : ℝ, 1 ≤ K ∧
      ∀ (R : Fin s → ℝ), (∀ i, 2*C ≤ R i) →
      ∀ (U : Set (Fin n → ℤ)) (u : Fin n → ℝ) (L : ℝ), 1 ≤ L →
      ∀ (m : ℕ), 0 < m → 1 < L/(m : ℝ) →
      StratifiedSieveNumerics.tailProduct R j ≤ 2*C*(L/(m : ℝ)) →
      C*(1+(L/(m : ℝ))/StratifiedSieveNumerics.tailProduct R j) ≤ R j →
      ∀ (b : Fin n → ℤ) (E : Finset ((Fin s → ℕ) × (Fin n → ℤ))),
      (∀ p ∈ E, ValidTuple t G U u L m b R p) →
      (E.card : ℝ) ≤ K*(L*(∏ i, R i)+‖u‖)^ε*(L/(m : ℝ))^((d j : ℝ)+1)/
        (∏ i, if j < i then (R i)^((d j : ℝ)-(d i : ℝ)) else 1) := by
  classical
  obtain ⟨c,B,hc,hB,hslice⟩ := StratifiedLargeSlice.exists_bound t d G hproper hdim j D
    (ε/3) (by positivity)
  refine ⟨c,hc,?_⟩
  intro C hC
  have hC1 : 1 ≤ C := hc.trans hC
  let α : ℝ := (d j : ℝ)+1
  let M : ℝ := (1+(2:ℝ)^s*(2*C))^α*
    (∏ i, 3*(2:ℝ)^(max ((d i : ℝ)+ε/3-α) 0))
  have hα : 0 ≤ α := by positivity
  have hM : 1 ≤ M := by
    apply one_le_mul_of_one_le_of_one_le
    · exact Real.one_le_rpow
        (by linarith [show 0 ≤ (2:ℝ)^s*(2*C) by positivity]) hα
    · simpa using Finset.prod_le_prod (s := Finset.univ) (f := fun _i : Fin s => (1:ℝ))
        (fun _ _ => zero_le_one) (fun i _ => DyadicPowerSum.coefficient_one_le _)
  refine ⟨B*M,one_le_mul_of_one_le_of_one_le hB hM,?_⟩
  intro R hR U u L hL m hm hT htailBound hpivot b E hE
  have hR1 (i) : 1 ≤ R i := by linarith [hR i]
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hT0 : 0 < L/(m : ℝ) := by linarith
  have htail1 : 1 ≤ StratifiedSieveNumerics.tailProduct R j := by
    rw [← tailScales_product]
    simpa using Finset.prod_le_prod (s := Finset.univ) (f := fun _i : Fin s => (1:ℝ))
      (fun _ _ => zero_le_one) (fun i _ => tailScales_one_le j R hR1 i)
  have htailpos : 0 < StratifiedSieveNumerics.tailProduct R j := by linarith
  let key (p : (Fin s → ℕ) × (Fin n → ℤ)) := tail j p.1
  let Q := E.image key
  have hratio (a : Fin s → ℕ) :
      1+L/(m*∏ i, a i : ℕ)=1+(L/(m : ℝ))/(∏ i, (a i : ℝ)) := by
    rw [div_div]
    push_cast
    rfl
  have hpow (a : Fin s → ℕ) :
      (1+L/(m*∏ i, a i : ℕ))^(d j+1)=
        (1+(L/(m : ℝ))/(∏ i, (a i : ℝ)))^α := by
    rw [hratio,← Real.rpow_natCast]
    simp only [Nat.cast_add,Nat.cast_one,α]
  have hdyadic : ∀ a ∈ Q, ∀ i,
      tailScales j R i ≤ (a i : ℝ) ∧ (a i : ℝ) ≤ 2*tailScales j R i := by
    intro a ha
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
    exact tail_dyadic j R p.1 (hE p hp).dyadic
  have hfiber (a) (ha : a ∈ Q) :
      ((E.filter fun p => key p=a).card : ℝ) ≤
        B*(L+‖u‖)^(ε/3)*(L*R j+‖u‖)^(ε/3)*
        ((1+(L/(m : ℝ))/(∏ i, (a i : ℝ)))^α*
          (∏ i, (a i : ℝ)^((d i : ℝ)+ε/3))) := by
    obtain ⟨p,hp,hpa⟩ := Finset.mem_image.mp ha
    have hlow : StratifiedSieveNumerics.tailProduct R j ≤ ∏ i, (a i : ℝ) := by
      rw [← hpa]
      exact (tail_product_bounds j R hR1 p.1 (hE p hp).dyadic).1
    have hthr : c*(1+L/(m*∏ i, a i : ℕ)) ≤ R j := by
      rw [hratio]
      have hdiv := div_le_div_of_nonneg_left hT0.le htailpos hlow
      have hbase : 0 ≤ 1+(L/(m : ℝ))/(∏ i, (a i : ℝ)) := by positivity
      exact ((mul_le_mul_of_nonneg_right hC hbase).trans
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl hdiv) (by linarith))).trans hpivot
    have he := hslice R hR1 U u L hL m hm b a hthr (E.filter fun p => key p=a)
      (fun p hp => hE p (Finset.mem_filter.mp hp).1)
      (fun p hp => (Finset.mem_filter.mp hp).2)
    rw [hpow] at he
    simpa only [mul_assoc] using he
  have hsum := StratifiedSmallRangeNumerics.sum_le (fun i => (d i : ℝ))
    (tailScales j R) (tailScales_one_le j R hR1) (L/(m : ℝ)) (2*C) α (ε/3)
    hT0 (by linarith) hα (by simpa only [tailScales_product] using htailBound) Q hdyadic
  have hP : 1 ≤ ∏ i, R i := by
    simpa using Finset.prod_le_prod (s := Finset.univ) (f := fun _i : Fin s => (1:ℝ))
      (fun _ _ => zero_le_one) (fun i _ => hR1 i)
  have hRj : 0 < R j := by linarith [hR1 j]
  have htaille : StratifiedSieveNumerics.tailProduct R j ≤ ∏ i, R i := by
    simpa only [tailScales_product] using tailScale_product_le_all j R hR1
  have hgrowth := StratifiedLargeRangeNumerics.growth_absorb L (∏ i, R i) (R j)
    (StratifiedSieveNumerics.tailProduct R j) ‖u‖ ε hL hP (norm_nonneg _)
    hRj (scale_le_product R hR1 j) htailpos htaille hε
  have hden : 0 < ∏ i, (tailScales j R i)^(α-(d i : ℝ)-1) :=
    Finset.prod_pos fun i _ => Real.rpow_pos_of_pos
      (lt_of_lt_of_le zero_lt_one (tailScales_one_le j R hR1 i)) _
  have hdeneq : (∏ i, (tailScales j R i)^(α-(d i : ℝ)-1)) =
      (∏ i, if j < i then (R i)^((d j : ℝ)-(d i : ℝ)) else 1) := by
    rw [tailScales_rpow_product]
    apply Finset.prod_congr rfl
    intro i _
    split_ifs
    · congr 1
      dsimp [α]
      ring
    · rfl
  have hRj1 : 1 ≤ R j := hR1 j
  calc
    (E.card : ℝ) = ∑ a ∈ Q, ((E.filter fun p => key p=a).card : ℝ) := by
      rw [Finset.card_eq_sum_card_image key E,Nat.cast_sum]
    _ ≤ ∑ a ∈ Q, B*(L+‖u‖)^(ε/3)*(L*R j+‖u‖)^(ε/3)*
        ((1+(L/(m : ℝ))/(∏ i, (a i : ℝ)))^α*
          (∏ i, (a i : ℝ)^((d i : ℝ)+ε/3))) := Finset.sum_le_sum hfiber
    _ = B*(L+‖u‖)^(ε/3)*(L*R j+‖u‖)^(ε/3)*
        (∑ a ∈ Q, (1+(L/(m : ℝ))/(∏ i, (a i : ℝ)))^α*
          (∏ i, (a i : ℝ)^((d i : ℝ)+ε/3))) := by rw [Finset.mul_sum]
    _ ≤ B*(L+‖u‖)^(ε/3)*(L*R j+‖u‖)^(ε/3)*
        (M*(L/(m : ℝ))^α*((∏ i, tailScales j R i)^(ε/3)/
          (∏ i, (tailScales j R i)^(α-(d i : ℝ)-1)))) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ((B*M)*(L/(m : ℝ))^α/(∏ i, (tailScales j R i)^(α-(d i : ℝ)-1)))*
        ((L+‖u‖)^(ε/3)*(L*R j+‖u‖)^(ε/3)*
          (StratifiedSieveNumerics.tailProduct R j)^(ε/3)) := by
      rw [tailScales_product]
      ring
    _ ≤ ((B*M)*(L/(m : ℝ))^α/(∏ i, (tailScales j R i)^(α-(d i : ℝ)-1)))*
        (L*(∏ i, R i)+‖u‖)^ε := mul_le_mul_of_nonneg_left hgrowth (by positivity)
    _ = _ := by rw [hdeneq]; ring

end CubicTenVariables.StratifiedLargeRange
