import CubicTenVariables.StratifiedSieveProfileRestriction

/-! The literal stratified composite sieve at every scale at least one.
Small scales are forgotten with bounded finite multiplicity; every retained
ordered subfamily uses the existing proved sieve. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CubicTenVariables.StratifiedCompositeSieveAllScales
open MvPolynomial StratifiedSieveData StratifiedSieveRestriction
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n s : ℕ}

/-- Removing the lower-scale threshold adds no arithmetic hypothesis.
The single constant precedes all scales, centers, progressions, and finite
sets of actual tuple--point pairs. -/
theorem exists_bound (t d : Fin s → ℕ)
    (G : ∀ i, Fin (t i) → MvPolynomial (Fin n) ℤ)
    (hproper : ∀ i, IntegralModelDimension.rationalIdeal (G i) ≠ ⊤)
    (hhom : ∀ i, (IntegralModelDimension.rationalIdeal (G i)).IsHomogeneous
      (homogeneousSubmodule (Fin n) ℚ))
    (hdim : ∀ i, ringKrullDim (MvPolynomial (Fin n) ℚ ⧸
      IntegralModelDimension.rationalIdeal (G i)) ≤ (d i : WithBot ℕ∞))
    (U : Set (Fin n → ℤ)) (α : ℝ) (hα : 0 ≤ α) (hU : ProgressionHypothesis U α)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ R : Fin s → ℝ, (∀ i, 1 ≤ R i) →
      ∀ (u : Fin n → ℝ) (L : ℝ), 1 ≤ L → ∀ m : ℕ, 0 < m →
      ∀ (b : Fin n → ℤ) (E : Finset ((Fin s → ℕ) × (Fin n → ℤ))),
      (∀ p ∈ E, ValidTuple t G U u L m b R p) →
      (E.card : ℝ) ≤ K*(L*(∏ i, R i)+‖u‖)^ε*profile d R (L/(m : ℝ)) α := by
  classical
  choose c k hc hk hbound using fun A : Finset (Fin s) =>
    StratifiedCompositeSieve.exists_bound (fun i => t (index A i))
      (fun i => d (index A i)) (fun i => G (index A i))
      (fun i => hproper (index A i)) (fun i => hhom (index A i))
      (fun i => hdim (index A i)) U α hα hU ε hε
  let C : ℝ := 1+∑ A, c A
  let K₀ : ℝ := 1+∑ A, k A
  have hc0 (A) : 0 ≤ c A := zero_le_one.trans (hc A)
  have hk0 (A) : 0 ≤ k A := zero_le_one.trans (hk A)
  have hC : 1 ≤ C := by
    dsimp [C]
    linarith [Finset.sum_nonneg (fun A (_ : A ∈ (Finset.univ : Finset (Finset (Fin s)))) => hc0 A)]
  have hK₀ : 1 ≤ K₀ := by
    dsimp [K₀]
    linarith [Finset.sum_nonneg (fun A (_ : A ∈ (Finset.univ : Finset (Finset (Fin s)))) => hk0 A)]
  have hcC (A) : c A ≤ C := by
    have hh := Finset.single_le_sum (fun B (_ : B ∈ (Finset.univ : Finset (Finset (Fin s)))) => hc0 B)
      (Finset.mem_univ A)
    dsimp [C]
    linarith
  have hkK (A) : k A ≤ K₀ := by
    have hh := Finset.single_le_sum (fun B (_ : B ∈ (Finset.univ : Finset (Finset (Fin s)))) => hk0 B)
      (Finset.mem_univ A)
    dsimp [K₀]
    linarith
  let M : ℕ := ⌈4*C⌉₊
  let W : ℝ := (2*C)^(α+2*(∑ i, (d i : ℝ))+1)
  have hW : 1 ≤ W := Real.one_le_rpow (by linarith)
    (by have := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin s))) =>
          (Nat.cast_nonneg (d i) : (0 : ℝ) ≤ d i)); linarith)
  let K : ℝ := ((M+1 : ℕ) : ℝ)^s*K₀*W^s
  have hM1 : (1 : ℝ) ≤ ((M+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le M)
  have hK : 1 ≤ K := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hM1) hK₀) (one_le_pow₀ hW)
  refine ⟨K,hK,?_⟩
  intro R hR u L hL m hm b E hE
  let A : Finset (Fin s) := Finset.univ.filter (fun i => 2*C ≤ R i)
  have hlarge (i : Fin A.card) : 2*c A ≤ R (index A i) := by
    have hh := (Finset.mem_filter.mp (index_mem A i)).2
    linarith [hcC A]
  have hsmall (i : Fin s) (hi : i ∉ A) : R i ≤ 2*C := by
    have hh : ¬ 2*C ≤ R i := by simpa only [A,Finset.mem_filter,Finset.mem_univ,true_and] using hi
    exact (lt_of_not_ge hh).le
  have hforgot (p) (hp : p ∈ E) (i : Fin s) (hi : i ∉ A) : p.1 i ≤ M := by
    have hq := ((hE p hp).dyadic i).2
    have hceil : 4*C ≤ (M : ℝ) := Nat.le_ceil _
    have hqM : (p.1 i : ℝ) ≤ M := by linarith [hsmall i hi]
    exact_mod_cast hqM
  let E' := E.image (restrict A)
  have hE' : ∀ p ∈ E', ValidTuple (fun i => t (index A i)) (fun i => G (index A i))
      U u L m b (fun i => R (index A i)) p := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact valid_restrict A t G U u L m b R q (hE q hq)
  have hcount := hbound A (fun i => R (index A i)) hlarge u L hL m hm b E' hE'
  have hcard : (E.card : ℝ) ≤ ((M+1 : ℕ) : ℝ)^s*(E'.card : ℝ) := by
    exact_mod_cast card_le_restricted_card A M E hforgot
  have hprod : (∏ i, R (index A i)) ≤ ∏ i, R i := by
    rw [prod_index]
    have hcompl : 1 ≤ ∏ i ∈ Aᶜ, R i := by
      calc
        (1 : ℝ) = ∏ i ∈ Aᶜ, (1 : ℝ) := by simp
        _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i _ => hR i)
    have hprod0 : 0 ≤ ∏ i ∈ A, R i := Finset.prod_nonneg (fun i _ => zero_le_one.trans (hR i))
    have hh := mul_le_mul_of_nonneg_left hcompl hprod0
    simpa only [mul_one,Finset.prod_mul_prod_compl] using hh
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hselprod0 : 0 ≤ ∏ i, R (index A i) :=
    Finset.prod_nonneg (fun i _ => zero_le_one.trans (hR (index A i)))
  have hfullprod0 : 0 ≤ ∏ i, R i :=
    Finset.prod_nonneg (fun i _ => zero_le_one.trans (hR i))
  have hheight : (L*(∏ i, R (index A i))+‖u‖)^ε ≤ (L*(∏ i, R i)+‖u‖)^ε :=
    Real.rpow_le_rpow (by positivity)
      (add_le_add (mul_le_mul_of_nonneg_left hprod hL0) le_rfl) hε.le
  have hT : 0 ≤ L/(m : ℝ) := by positivity
  have hprofile := StratifiedSieveProfileRestriction.profile_le d α (2*C) hα
    (by linarith) A R hR hsmall (L/(m : ℝ)) hT
  have hp0 : 0 ≤ profile d R (L/(m : ℝ)) α :=
    StratifiedSieveProfileRestriction.profile_nonneg d R
      (fun i => zero_le_one.trans (hR i)) _ _ hT
  have hs0 : 0 ≤ profile (fun i => d (index A i)) (fun i => R (index A i)) (L/(m : ℝ)) α :=
    StratifiedSieveProfileRestriction.profile_nonneg _ _
      (fun i => zero_le_one.trans (hR (index A i))) _ _ hT
  have hh0 : 0 ≤ (L*(∏ i, R i)+‖u‖)^ε := Real.rpow_nonneg (by positivity) _
  calc
    _ ≤ ((M+1 : ℕ) : ℝ)^s*(E'.card : ℝ) := hcard
    _ ≤ ((M+1 : ℕ) : ℝ)^s*
        (k A*(L*(∏ i, R (index A i))+‖u‖)^ε*
          profile (fun i => d (index A i)) (fun i => R (index A i)) (L/(m : ℝ)) α) :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ ≤ ((M+1 : ℕ) : ℝ)^s*(K₀*(L*(∏ i, R i)+‖u‖)^ε*(W^s*profile d R (L/(m : ℝ)) α)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul (mul_le_mul (hkK A) hheight (by positivity) (zero_le_one.trans hK₀))
        hprofile hs0 (mul_nonneg (zero_le_one.trans hK₀) hh0)
    _ = _ := by dsimp [K]; ring

end CubicTenVariables.StratifiedCompositeSieveAllScales
