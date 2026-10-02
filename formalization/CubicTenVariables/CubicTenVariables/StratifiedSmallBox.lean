import CubicTenVariables.GeometricSieveTupleMultiplicity
import CubicTenVariables.StratifiedSieveData

/-! The small-box branch of the actual stratified sieve. Its sole counting
premise is the source's explicit progression hypothesis. Modulus tuple
multiplicity is proved from the original integral ideals. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.StratifiedSmallBox
open MvPolynomial StratifiedSieveData
open scoped BigOperators

theorem exists_uniform_bound {n s : ℕ} (t : Fin s → ℕ)
    (G : ∀i,Fin (t i) → MvPolynomial (Fin n) ℤ)
    (U : Set (Fin n → ℤ)) (α : ℝ) (hα : 0≤α)
    (hU : ProgressionHypothesis U α) (ε : ℝ) (hε : 0 < ε) :
    ∃K : ℝ,1≤K ∧ ∀R : Fin s → ℝ,(∀i,1≤R i) →
      ∀u : Fin n → ℝ,∀L : ℝ,1≤L → ∀m : ℕ,0 < m → L≤(m : ℝ) →
      ∀b : Fin n → ℤ,∀E : Finset ((Fin s → ℕ) × (Fin n → ℤ)),
      (∀a∈E,ValidTuple t G U u L m b R a) →
      (E.card : ℝ)≤K*(L*(∏i,R i)+‖u‖)^ε := by
  classical
  have hη : 0 < ε/2 := by positivity
  obtain ⟨B,hB,hb⟩ := GeometricSieveTupleMultiplicity.exists_uniform_bound (ideal t G) (ε/2) hη
  obtain ⟨A,hA,ha⟩ := hU (ε/2) hη
  have htwo : 1≤(2 : ℝ)^α := Real.one_le_rpow (by norm_num) hα
  have hK : 1≤B*A*(2 : ℝ)^α :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hB hA) htwo
  refine ⟨B*A*(2 : ℝ)^α,hK,?_⟩
  intro R hR u L hL m hm hLm b E hE
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hH : 1≤L+‖u‖ := by linarith [norm_nonneg u]
  have hprod : 1≤∏i,R i := by
    calc
      1 = ∏_i : Fin s,(1 : ℝ) := by simp
      _ ≤ ∏i,R i := Finset.prod_le_prod (by intros; norm_num) (fun i _ => hR i)
  have hscale : L+‖u‖≤L*(∏i,R i)+‖u‖ := by nlinarith
  have hpoints : ((E.image Prod.snd).card : ℝ)≤A*(L+‖u‖)^(ε/2)*(2 : ℝ)^α := by
    have hp : ((E.image Prod.snd).card : ℝ)≤A*(L+‖u‖)^(ε/2)*(1+L/(m : ℝ))^α := by
      apply ha u L hL m hm b
      · intro x hx
        obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
        exact (hE a ha).mem
      · intro x hx
        obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
        exact (hE a ha).box
      · intro x hx
        obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
        exact (hE a ha).progression
    apply hp.trans
    apply mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) ?_ hα)
      (mul_nonneg (zero_le_one.trans hA) (Real.rpow_nonneg (zero_le_one.trans hH) _))
    have hr : L/(m : ℝ)≤1 := (div_le_one hmR).mpr hLm
    linarith
  have htuple := hb u L hL E (fun a ha => (hE a ha).box)
    (fun a ha => (hE a ha).outside)
    (fun a ha i => Nat.pos_of_ne_zero ((hE a ha).squarefree i).ne_zero)
    (fun a ha => (hE a ha).equations)
  have he : (L+‖u‖)^(ε/2)*(L+‖u‖)^(ε/2)=(L+‖u‖)^ε := by
    rw [←Real.rpow_add (by linarith : 0 < L+‖u‖)]
    congr 1
    ring
  calc
    (E.card : ℝ) ≤ B*(L+‖u‖)^(ε/2)*((E.image Prod.snd).card : ℝ) := htuple
    _ ≤ B*(L+‖u‖)^(ε/2)*(A*(L+‖u‖)^(ε/2)*(2 : ℝ)^α) :=
      mul_le_mul_of_nonneg_left hpoints
        (mul_nonneg (zero_le_one.trans hB) (Real.rpow_nonneg (zero_le_one.trans hH) _))
    _ = (B*A*(2 : ℝ)^α)*(L+‖u‖)^ε := by rw [←he]; ring
    _ ≤ (B*A*(2 : ℝ)^α)*(L*(∏i,R i)+‖u‖)^ε :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (zero_le_one.trans hH) hscale hε.le) (zero_le_one.trans hK)

/-- The actual finite enumeration in the manuscript, without a supplied
finite-set validity premise. This is the L≤m branch only. -/
theorem exists_pairs_bound {n s : ℕ} (t : Fin s → ℕ)
    (G : ∀i,Fin (t i) → MvPolynomial (Fin n) ℤ)
    (U : Set (Fin n → ℤ)) (α : ℝ) (hα : 0≤α)
    (hU : ProgressionHypothesis U α) (ε : ℝ) (hε : 0 < ε) :
    ∃K : ℝ,1≤K ∧ ∀R : Fin s → ℝ,(∀i,1≤R i) →
      ∀u : Fin n → ℝ,∀L : ℝ,1≤L → ∀m : ℕ,0 < m → L≤(m : ℝ) →
      ∀b : Fin n → ℤ,
      ((pairs t G U u L m b R).card : ℝ)≤K*(L*(∏i,R i)+‖u‖)^ε := by
  classical
  obtain ⟨K,hK,hb⟩ := exists_uniform_bound t G U α hα hU ε hε
  refine ⟨K,hK,?_⟩
  intro R hR u L hL m hm hLm b
  apply hb R hR u L hL m hm hLm b
  intro a ha
  exact (Finset.mem_filter.mp ha).2

end CubicTenVariables.StratifiedSmallBox
