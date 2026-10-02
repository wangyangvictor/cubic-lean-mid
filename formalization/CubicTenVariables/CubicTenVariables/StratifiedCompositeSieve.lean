import CubicTenVariables.StratifiedSmallBox
import CubicTenVariables.StratifiedSmallRange
import CubicTenVariables.StratifiedLargeRange

/-! The stratified composite sieve for fixed integral models of proper
homogeneous rational cones. All three modulus ranges and every original
integral equation are included. The source progression hypothesis remains
an explicit hypothesis; normalization certificates are constructed internally. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.StratifiedCompositeSieve
open MvPolynomial StratifiedSieveData IntegralLinearNormalization
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n s : ℕ}

private theorem profile_bounds (d : Fin s → ℕ) (R : Fin s → ℝ)
    (hR : ∀ i, 0 ≤ R i) (T α : ℝ) (hT : 0 ≤ T) :
    1 ≤ profile d R T α ∧
    T^α/(∏ i, (R i)^(α-(d i : ℝ)-1)) ≤ profile d R T α ∧
    ∀ j, T^((d j : ℝ)+1)/
      (∏ i, if j < i then (R i)^((d j : ℝ)-(d i : ℝ)) else 1) ≤
      profile d R T α := by
  have hs : 0 ≤ T^α/(∏ i, (R i)^(α-(d i : ℝ)-1)) :=
    div_nonneg (Real.rpow_nonneg hT _) (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hR i) _)
  have hj (j : Fin s) : 0 ≤ T^((d j : ℝ)+1)/
      (∏ i, if j < i then (R i)^((d j : ℝ)-(d i : ℝ)) else 1) := by
    apply div_nonneg (Real.rpow_nonneg hT _)
    apply Finset.prod_nonneg
    intro i _
    split_ifs
    · exact Real.rpow_nonneg (hR i) _
    · exact zero_le_one
  have hsum := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin s))) => hj j)
  refine ⟨by unfold profile; linarith,by unfold profile; linarith,?_⟩
  intro j
  have hle := Finset.single_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin s))) => hj k)
    (Finset.mem_univ j)
  unfold profile
  linarith

private theorem enlarge {x A B H f P : ℝ} (hx : x ≤ A*H*f)
    (hAB : A ≤ B) (hB : 0 ≤ B) (hH : 0 ≤ H) (hf : 0 ≤ f) (hP : f ≤ P) :
    x ≤ B*H*P := by
  exact hx.trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hAB hH) hf).trans
      (mul_le_mul_of_nonneg_left hP (mul_nonneg hB hH)))

/-- The three proved ranges with fixed integral normalization certificates. -/
theorem exists_bound_of_certificates (t d : Fin s → ℕ)
    (G : ∀ i, Fin (t i) → MvPolynomial (Fin n) ℤ)
    (hproper : ∀ i, IntegralModelDimension.rationalIdeal (G i) ≠ ⊤)
    (hdim : ∀ i, ringKrullDim (MvPolynomial (Fin n) ℚ ⧸
      IntegralModelDimension.rationalIdeal (G i)) ≤ (d i : WithBot ℕ∞))
    (D : ∀ j, Certificate (ideal t G j) (d j))
    (U : Set (Fin n → ℤ)) (α : ℝ) (hα : 0 ≤ α) (hU : ProgressionHypothesis U α)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C K : ℝ, 1 ≤ C ∧ 1 ≤ K ∧ ∀ R : Fin s → ℝ, (∀ i, 2*C ≤ R i) →
      ∀ (u : Fin n → ℝ) (L : ℝ), 1 ≤ L → ∀ m : ℕ, 0 < m →
      ∀ (b : Fin n → ℤ) (E : Finset ((Fin s → ℕ) × (Fin n → ℤ))),
      (∀ p ∈ E, ValidTuple t G U u L m b R p) →
      (E.card : ℝ) ≤ K*(L*(∏ i, R i)+‖u‖)^ε*profile d R (L/(m : ℝ)) α := by
  classical
  choose c hc hlarge using fun j => StratifiedLargeRange.exists_bound t d G hproper hdim j (D j) ε hε
  let C : ℝ := 1+∑ j, c j
  have hc0 (j) : 0 ≤ c j := zero_le_one.trans (hc j)
  have hC : 1 ≤ C := by dsimp [C]; linarith [Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin s))) => hc0 j)]
  have hcle (j) : c j ≤ C := by
    have hs := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin s))) => hc0 i)
      (Finset.mem_univ j)
    dsimp [C]
    linarith
  choose Klarge hKlarge hbLarge using fun j => hlarge j C (hcle j)
  obtain ⟨Kbox,hKbox,hbBox⟩ := StratifiedSmallBox.exists_uniform_bound t G U α hα hU ε hε
  obtain ⟨Ksmall,hKsmall,hbSmall⟩ := StratifiedSmallRange.exists_bound t d G hproper hdim
    U α hα hU ε (2*C) hε (by linarith)
  let K : ℝ := Kbox+Ksmall+∑ j, Klarge j
  have hKL0 (j) : 0 ≤ Klarge j := zero_le_one.trans (hKlarge j)
  have hKsum : 0 ≤ ∑ j, Klarge j := Finset.sum_nonneg (fun j _ => hKL0 j)
  have hK : 1 ≤ K := by dsimp [K]; linarith
  have hKB : Kbox ≤ K := by dsimp [K]; linarith
  have hKS : Ksmall ≤ K := by dsimp [K]; linarith
  have hKL (j) : Klarge j ≤ K := by
    have hs := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin s))) => hKL0 i)
      (Finset.mem_univ j)
    dsimp [K]
    linarith
  refine ⟨C,K,hC,hK,?_⟩
  intro R hR u L hL m hm b E hE
  have hR1 (i) : 1 ≤ R i := by linarith [hR i]
  have hR0 (i) : 0 ≤ R i := zero_le_one.trans (hR1 i)
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hT : 0 ≤ L/(m : ℝ) := div_nonneg (by linarith) hmR.le
  have hP0 : 0 ≤ ∏ i, R i := Finset.prod_nonneg (fun i _ => hR0 i)
  have hH : 0 ≤ (L*(∏ i, R i)+‖u‖)^ε := Real.rpow_nonneg
    (add_nonneg (mul_nonneg (by linarith) hP0) (norm_nonneg _)) _
  have hprofile := profile_bounds d R hR0 (L/(m : ℝ)) α hT
  by_cases hbox : L ≤ (m : ℝ)
  · have h := hbBox R hR1 u L hL m hm hbox b E hE
    apply enlarge (by simpa only [mul_one] using h) hKB (zero_le_one.trans hK) hH
      zero_le_one hprofile.1
  have hT1 : 1 < L/(m : ℝ) := (one_lt_div hmR).mpr (lt_of_not_ge hbox)
  by_cases hsmall : (∏ i, R i) ≤ 2*C*(L/(m : ℝ))
  · have h := hbSmall R hR1 u L hL m hm hsmall b E hE
    apply enlarge (by convert h using 1; ring) hKS (zero_le_one.trans hK) hH
      (div_nonneg (Real.rpow_nonneg hT _) (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hR0 i) _))
      hprofile.2.1
  obtain ⟨j,htail,_hcross,hpivot⟩ := StratifiedSieveNumerics.exists_pivot C (L/(m : ℝ))
    hC hT1 R hR (lt_of_not_ge hsmall)
  have h := hbLarge j R hR U u L hL m hm hT1 htail hpivot b E hE
  apply enlarge (by convert h using 1; ring) (hKL j) (zero_le_one.trans hK) hH
    ?_ (hprofile.2.2 j)
  apply div_nonneg (Real.rpow_nonneg hT _)
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · exact Real.rpow_nonneg (hR0 i) _
  · exact zero_le_one

/-- Extension of the literal finitely generated ideal agrees with the
rational equation ideal used in the dimension hypotheses. -/
theorem rationalIdeal_ideal (t : Fin s → ℕ)
    (G : ∀ i, Fin (t i) → MvPolynomial (Fin n) ℤ) (j : Fin s) :
    IntegralLinearNormalization.rationalIdeal (ideal t G j) =
      IntegralModelDimension.rationalIdeal (G j) := by
  rw [IntegralLinearNormalization.rationalIdeal, ideal, IntegralModelDimension.rationalIdeal,
    Ideal.map_span, ← Set.range_comp]
  rfl

/-- Uniform composite sieve for the required homogeneous-cone setting.
No supplied coordinate certificate, point estimate, or literature proposition
occurs: only the explicitly assumed progression bound for U remains. -/
theorem exists_bound (t d : Fin s → ℕ)
    (G : ∀ i, Fin (t i) → MvPolynomial (Fin n) ℤ)
    (hproper : ∀ i, IntegralModelDimension.rationalIdeal (G i) ≠ ⊤)
    (hhom : ∀ i, (IntegralModelDimension.rationalIdeal (G i)).IsHomogeneous
      (homogeneousSubmodule (Fin n) ℚ))
    (hdim : ∀ i, ringKrullDim (MvPolynomial (Fin n) ℚ ⧸
      IntegralModelDimension.rationalIdeal (G i)) ≤ (d i : WithBot ℕ∞))
    (U : Set (Fin n → ℤ)) (α : ℝ) (hα : 0 ≤ α) (hU : ProgressionHypothesis U α)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C K : ℝ, 1 ≤ C ∧ 1 ≤ K ∧ ∀ R : Fin s → ℝ, (∀ i, 2*C ≤ R i) →
      ∀ (u : Fin n → ℝ) (L : ℝ), 1 ≤ L → ∀ m : ℕ, 0 < m →
      ∀ (b : Fin n → ℤ) (E : Finset ((Fin s → ℕ) × (Fin n → ℤ))),
      (∀ p ∈ E, ValidTuple t G U u L m b R p) →
      (E.card : ℝ) ≤ K*(L*(∏ i, R i)+‖u‖)^ε*profile d R (L/(m : ℝ)) α := by
  classical
  have hcert (j : Fin s) : Nonempty (Certificate (ideal t G j) (d j)) := by
    apply IntegralLinearNormalization.exists_certificate (ideal t G j)
    · simpa only [rationalIdeal_ideal] using hproper j
    · simpa only [rationalIdeal_ideal] using hhom j
    · rw [rationalIdeal_ideal t G j]
      exact hdim j
  let D (j : Fin s) := Classical.choice (hcert j)
  exact exists_bound_of_certificates t d G hproper hdim D U α hα hU ε hε

/-- The explicit finite enumeration contains exactly all valid tuples. -/
theorem mem_pairs (t : Fin s → ℕ)
    (G : ∀ i, Fin (t i) → MvPolynomial (Fin n) ℤ)
    (U : Set (Fin n → ℤ)) (u : Fin n → ℝ) (L : ℝ) (m : ℕ)
    (b : Fin n → ℤ) (R : Fin s → ℝ) (hR : ∀ i, 1 ≤ R i)
    (p : (Fin s → ℕ) × (Fin n → ℤ)) :
    p ∈ pairs t G U u L m b R ↔ ValidTuple t G U u L m b R p := by
  classical
  constructor
  · intro hp
    exact (Finset.mem_filter.mp hp).2
  · intro hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,hp⟩
    · apply Fintype.mem_piFinset.mpr
      intro i
      exact (DyadicPowerSum.mem_interval (R i) (hR i) _).mpr (hp.dyadic i)
    · exact (TranslatedIntegerBoxes.mem_box u L p.2).mpr hp.box

/-- The bound on the literal complete tuple--point enumeration. -/
theorem exists_pairs_bound (t d : Fin s → ℕ)
    (G : ∀ i, Fin (t i) → MvPolynomial (Fin n) ℤ)
    (hproper : ∀ i, IntegralModelDimension.rationalIdeal (G i) ≠ ⊤)
    (hhom : ∀ i, (IntegralModelDimension.rationalIdeal (G i)).IsHomogeneous
      (homogeneousSubmodule (Fin n) ℚ))
    (hdim : ∀ i, ringKrullDim (MvPolynomial (Fin n) ℚ ⧸
      IntegralModelDimension.rationalIdeal (G i)) ≤ (d i : WithBot ℕ∞))
    (U : Set (Fin n → ℤ)) (α : ℝ) (hα : 0 ≤ α) (hU : ProgressionHypothesis U α)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C K : ℝ, 1 ≤ C ∧ 1 ≤ K ∧ ∀ R : Fin s → ℝ, (∀ i, 2*C ≤ R i) →
      ∀ (u : Fin n → ℝ) (L : ℝ), 1 ≤ L → ∀ m : ℕ, 0 < m →
      ∀ b : Fin n → ℤ,
      ((pairs t G U u L m b R).card : ℝ) ≤
        K*(L*(∏ i, R i)+‖u‖)^ε*profile d R (L/(m : ℝ)) α := by
  classical
  obtain ⟨C,K,hC,hK,hbound⟩ := exists_bound t d G hproper hhom hdim U α hα hU ε hε
  refine ⟨C,K,hC,hK,?_⟩
  intro R hR u L hL m hm b
  apply hbound R hR u L hL m hm b
  intro p hp
  exact (Finset.mem_filter.mp hp).2

end CubicTenVariables.StratifiedCompositeSieve
