import CubicTenVariables.StratifiedSieveData
import CubicTenVariables.SimultaneousEquationBounds
import CubicTenVariables.StratifiedSmallRangeNumerics

/-! The complete small-product case of the stratified composite sieve,
with the source progression hypothesis and original integral equations. -/
noncomputable section
namespace CubicTenVariables.StratifiedSmallRange
open MvPolynomial StratifiedSieveData
open scoped BigOperators
variable {n s : ℕ}

theorem growth_absorb (L P U ε : ℝ) (hL : 1 ≤ L) (hP : 1 ≤ P)
    (hU : 0 ≤ U) (hε : 0 < ε) :
    (L+U)^(ε/2)*P^(ε/2) ≤ (L*P+U)^ε := by
  have hH : 0 < L*P+U := by nlinarith
  have h1 : (L+U)^(ε/2) ≤ (L*P+U)^(ε/2) :=
    Real.rpow_le_rpow (by linarith) (by nlinarith) (by positivity)
  have h2 : P^(ε/2) ≤ (L*P+U)^(ε/2) :=
    Real.rpow_le_rpow (by linarith) (by nlinarith) (by positivity)
  calc
    _ ≤ (L*P+U)^(ε/2)*(L*P+U)^(ε/2) :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add hH]; congr 1; ring

theorem exists_bound (t d : Fin s → ℕ)
    (G : ∀ i, Fin (t i) → MvPolynomial (Fin n) ℤ)
    (hproper : ∀ i, IntegralModelDimension.rationalIdeal (G i) ≠ ⊤)
    (hdim : ∀ i, ringKrullDim (MvPolynomial (Fin n) ℚ ⧸
      IntegralModelDimension.rationalIdeal (G i)) ≤ (d i : WithBot ℕ∞))
    (U : Set (Fin n → ℤ)) (α : ℝ) (hα : 0 ≤ α) (hU : ProgressionHypothesis U α)
    (ε c : ℝ) (hε : 0 < ε) (hc : 0 < c) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (R : Fin s → ℝ), (∀ i, 1 ≤ R i) →
      ∀ (u : Fin n → ℝ) (L : ℝ), 1 ≤ L → ∀ (m : ℕ), 0 < m →
      (∏ i, R i) ≤ c*(L/(m : ℝ)) → ∀ (b : Fin n → ℤ)
        (E : Finset ((Fin s → ℕ) × (Fin n → ℤ))),
      (∀ p ∈ E, ValidTuple t G U u L m b R p) →
      (E.card : ℝ) ≤ K*(L*(∏ i, R i)+‖u‖)^ε*(L/(m : ℝ))^α/
        (∏ i, (R i)^(α-(d i : ℝ)-1)) := by
  classical
  obtain ⟨A,hA,hprog⟩ := hU (ε/2) (by positivity)
  obtain ⟨B,hB,hbound⟩ := SimultaneousEquationBounds.exists_tuple_bound t d G hproper hdim
    (ε/2) (by positivity)
  let D : ℝ := (1+(2:ℝ)^s*c)^α*(∏ i, 3*(2:ℝ)^(max ((d i : ℝ)+ε/2-α) 0))
  have hD : 1 ≤ D := by
    apply one_le_mul_of_one_le_of_one_le
    · exact Real.one_le_rpow
        (by linarith [show 0 ≤ (2:ℝ)^s*c by positivity]) hα
    · simpa using Finset.prod_le_prod (s := Finset.univ) (f := fun _i : Fin s => (1:ℝ))
        (fun _ _ => zero_le_one) (fun i _ => DyadicPowerSum.coefficient_one_le _)
  refine ⟨A*B*D,one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hA hB) hD,?_⟩
  intro R hR u L hL m hm hprod b E hE
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hT : 0 < L/(m : ℝ) := div_pos (by linarith) hmR
  have hP : 1 ≤ ∏ i, R i := by
    simpa using Finset.prod_le_prod (s := Finset.univ) (f := fun _i : Fin s => (1:ℝ))
      (fun _ _ => zero_le_one) (fun i _ => hR i)
  have hcount := hbound m hm U α (ε/2) A (by linarith) hprog u L hL b E
    (fun p hp => (hE p hp).squarefree) (fun p hp => (hE p hp).coprime)
    (fun p hp => (hE p hp).base_coprime) (fun p hp => (hE p hp).mem)
    (fun p hp => (hE p hp).box) (fun p hp => (hE p hp).progression)
    (fun p hp => (hE p hp).generator_equations)
  have hratio (q : Fin s → ℕ) :
      1+L/(m*∏ i, q i : ℕ)=1+(L/(m : ℝ))/(∏ i, (q i : ℝ)) := by
    rw [div_div]
    push_cast
    rfl
  simp_rw [hratio] at hcount
  have hsum := StratifiedSmallRangeNumerics.sum_le (fun i => (d i : ℝ)) R hR
    (L/(m : ℝ)) c α (ε/2) hT hc hα hprod (E.image Prod.fst) (by
      intro q hq
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
      exact (hE p hp).dyadic)
  have hgrowth := growth_absorb L (∏ i, R i) ‖u‖ ε hL hP (norm_nonneg _) hε
  have hden : 0 < ∏ i, (R i)^(α-(d i : ℝ)-1) :=
    Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (by linarith [hR i]) _
  calc
    (E.card : ℝ) ≤ A*B*(L+‖u‖)^(ε/2)*
        (D*(L/(m : ℝ))^α*((∏ i, R i)^(ε/2)/(∏ i, (R i)^(α-(d i : ℝ)-1)))) :=
      hcount.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
    _ = ((A*B*D)*(L/(m : ℝ))^α/(∏ i, (R i)^(α-(d i : ℝ)-1)))*
        ((L+‖u‖)^(ε/2)*(∏ i, R i)^(ε/2)) := by ring
    _ ≤ ((A*B*D)*(L/(m : ℝ))^α/(∏ i, (R i)^(α-(d i : ℝ)-1)))*
        (L*(∏ i, R i)+‖u‖)^ε := mul_le_mul_of_nonneg_left hgrowth (by positivity)
    _ = _ := by ring

end CubicTenVariables.StratifiedSmallRange
