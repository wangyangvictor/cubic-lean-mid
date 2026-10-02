import CubicTenVariables.FlexibleLifting
import CubicTenVariables.LocalizedFirstLiftVanishing

/-! Flexible lifting with the actual fixed congruence restriction retained
through both digit decompositions. The condition W divides A is explicit;
it implies that the common ambient modulus of the localized sum is A²T.
No estimate for root counts or terminal sums is assumed in the final bound. -/

noncomputable section
namespace CubicTenVariables.LocalizedFlexibleLifting
open MvPolynomial HessianTheorem11 FirstLiftPhase FirstLiftSum SecondLiftPhase
open SecondLiftSum MixedRadixLifting TerminalCubicSum
open LocalizedFirstLiftVanishing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

def lowDigitSum (F : MvPolynomial (Fin n) ℤ) (A M W : ℕ)
    (Ω : Set (Fin n → ZMod W)) (v : Fin n → ℤ) : ℂ :=
  ∑ a : Fin M, if Nat.Coprime a.val M then
    ∑ y : Fin n → Fin M,
      if integerResidue W (integerVector y) ∈ Ω then
        if supportCondition F A (a.val : ℤ) (integerVector y) v then
          residueExponential (A*M) (integerPhase F (a.val : ℤ) (integerVector y) v)
        else 0
      else 0
  else 0

theorem first_lift (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (A M W : ℕ) [NeZero A] [NeZero M] (hAM : A ∣ M) (hWM : W ∣ M)
    (Ω : Set (Fin n → ZMod W)) (v : Fin n → ℤ) :
    localizedCompleteCubicSum F (A*M) W Ω v =
      (A : ℂ)^(n+1) * lowDigitSum F A M W Ω v := by
  have hlcm : Nat.lcm (A*M) W = A*M :=
    Nat.lcm_eq_left_iff_dvd.mpr (hWM.trans (dvd_mul_left M A))
  unfold localizedCompleteCubicSum lowDigitSum
  rw [hlcm, sum_mixedRadix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [coprime_mixedRadix_iff A M hAM]
  by_cases ha : Nat.Coprime a.val M
  · simp_rw [if_pos ha, sum_mixedRadixVector n A M]
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    have hr (h : Fin n → Fin A) :
        integerResidue W (fun i => ((mixedRadixVectorEquiv n A M (y,h) i).val : ℤ)) =
          integerResidue W (integerVector y) := by
      rw [mixedRadixVectorEquiv_intCast]
      exact integerResidue_add_smul W M hWM _ _
    simp_rw [hr]
    by_cases hy : integerResidue W (integerVector y) ∈ Ω
    · simp_rw [if_pos hy, ← residueExponential_add]
      have he (e : Fin A) (h : Fin n → Fin A) :
          (mixedRadixEquiv A M (a,e)).val *
              eval (fun i => ((mixedRadixVectorEquiv n A M (y,h) i).val : ℤ)) F +
              ∑ i, v i * (mixedRadixVectorEquiv n A M (y,h) i).val =
            integerPhase F ((a.val : ℤ)+(M : ℤ)*e.val)
              (integerVector y+(M : ℤ) • integerVector h) v := by
        exact completeSumPhase_mixedRadix F A M a e y h v
      simp_rw [he]
      calc
        _ = if supportCondition F A (a.val : ℤ) (integerVector y) v then
              (A : ℂ)^(n+1) * residueExponential (A*M)
                (integerPhase F (a.val : ℤ) (integerVector y) v) else 0 :=
          sum_lifted_phase F hF A M hAM (integerVector y) v (a.val : ℤ)
        _ = _ := by split_ifs <;> simp
    · simp [hy]
  · simp [ha]

def inner (F : MvPolynomial (Fin n) ℤ) (A T W : ℕ)
    (Ω : Set (Fin n → ZMod W)) (a : ℤ) (v : Fin n → ℤ) : ℂ :=
  ∑ x : Fin n → Fin (A*T),
    if integerResidue W (integerVector x) ∈ Ω then
      if supportCondition F A a (integerVector x) v then
        residueExponential (A^2*T) (integerPhase F a (integerVector x) v)
      else 0
    else 0

theorem inner_eq_secondLift (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (A T W : ℕ) [NeZero A] [NeZero T] (hWA : W ∣ A)
    (Ω : Set (Fin n → ZMod W)) (a : ℤ) (v : Fin n → ℤ) :
    inner F A T W Ω a v =
      ∑ y : Fin n → Fin A,
        if integerResidue W (integerVector y) ∈ Ω then
          if supportCondition F A a (integerVector y) v then
            residueExponential (A^2*T) (integerPhase F a (integerVector y) v) *
              terminalSum T (map (Int.castRingHom (ZMod T)) F) (A : ZMod T)
                (fun i => (linearQuotient F A a (integerVector y) v i : ZMod T))
                (a : ZMod T) (fun i => ((y i).val : ZMod T))
          else 0
        else 0 := by
  unfold inner
  rw [sum_secondLiftVector]
  apply Finset.sum_congr rfl
  intro y _
  simp_rw [secondLiftVectorEquiv_intCast]
  have hr (z : Fin n → Fin T) :
      integerResidue W (integerVector y+(A : ℤ) • integerVector z) =
        integerResidue W (integerVector y) := integerResidue_add_smul W A hWA _ _
  have hs (z : Fin n → Fin T) :
      supportCondition F A a (integerVector y+(A : ℤ) • integerVector z) v ↔
        supportCondition F A a (integerVector y) v :=
    support_add_smul_iff F A a (integerVector y) (integerVector z) v
  simp_rw [hr, hs]
  by_cases hy : integerResidue W (integerVector y) ∈ Ω
  · simp_rw [if_pos hy]
    by_cases hsup : supportCondition F A a (integerVector y) v
    · simp_rw [if_pos hsup]
      simpa only [integerVector, Int.cast_natCast] using
        sum_secondLift_phase F hF A T a (integerVector y) v hsup.2
    · simp [hsup]
  · simp [hy]

def pointwiseBound (F : MvPolynomial (Fin n) ℤ) (A T W : ℕ) [NeZero T]
    (Ω : Set (Fin n → ZMod W)) (v : Fin n → ℤ) : ℝ :=
  ∑ a : Fin (A*T), if Nat.Coprime a.val (A*T) then
    ∑ y : Fin n → Fin A,
      if integerResidue W (integerVector y) ∈ Ω then
        if supportCondition F A (a.val : ℤ) (integerVector y) v then
          residueTerminalMax F A T y else 0
      else 0
  else 0

theorem norm_inner_le (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (A T W : ℕ) [NeZero A] [NeZero T] (hWA : W ∣ A)
    (Ω : Set (Fin n → ZMod W)) (a : ℕ) (ha : Nat.Coprime a (A*T))
    (v : Fin n → ℤ) :
    ‖inner F A T W Ω (a : ℤ) v‖ ≤
      ∑ y : Fin n → Fin A,
        if integerResidue W (integerVector y) ∈ Ω then
          if supportCondition F A (a : ℤ) (integerVector y) v then
            residueTerminalMax F A T y else 0
        else 0 := by
  rw [inner_eq_secondLift F hF A T W hWA]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro y _
  by_cases hy : integerResidue W (integerVector y) ∈ Ω
  · simp only [if_pos hy]
    by_cases hs : supportCondition F A (a : ℤ) (integerVector y) v
    · simp only [if_pos hs, norm_mul, norm_residueExponential, one_mul]
      have hu := norm_terminalSum_le_terminalMax T
        (map (Int.castRingHom (ZMod T)) F) (A : ZMod T)
        (fun i => (linearQuotient F A (a : ℤ) (integerVector y) v i : ZMod T))
        (ZMod.unitOfCoprime a (ha.of_dvd_right (dvd_mul_left T A)))
        (fun i => ((y i).val : ZMod T))
      simpa only [ZMod.coe_unitOfCoprime, Int.cast_natCast, residueTerminalMax] using hu
    · simp [hs]
  · simp [hy]

theorem norm_complete_sum_le (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (A T W : ℕ) [NeZero A] [NeZero T] (hWA : W ∣ A)
    (Ω : Set (Fin n → ZMod W)) (v : Fin n → ℤ) :
    ‖localizedCompleteCubicSum F (A^2*T) W Ω v‖ ≤
      (A : ℝ)^(n+1) * pointwiseBound F A T W Ω v := by
  have hf : localizedCompleteCubicSum F (A^2*T) W Ω v =
      (A : ℂ)^(n+1) * ∑ a : Fin (A*T), if Nat.Coprime a.val (A*T) then
        inner F A T W Ω (a.val : ℤ) v else 0 := by
    simpa only [pow_two, mul_assoc, lowDigitSum, inner] using
      first_lift F hF A (A*T) W (dvd_mul_right A T)
        (hWA.trans (dvd_mul_right A T)) Ω v
  rw [hf, norm_mul, norm_pow, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : Nat.Coprime a.val (A*T)
  · simp only [if_pos ha]
    exact norm_inner_le F hF A T W hWA Ω a.val ha v
  · simp [ha]

def zeroFiberTotal (F : MvPolynomial (Fin n) ℤ) (A T W : ℕ) [NeZero T]
    (Ω : Set (Fin n → ZMod W)) : ℝ :=
  ∑ y : Fin n → Fin A,
    if integerResidue W (integerVector y) ∈ Ω ∧ (A : ℤ) ∣ eval (integerVector y) F then
      residueTerminalMax F A T y else 0

theorem weighted_pointwise_le (F : MvPolynomial (Fin n) ℤ)
    (A T W : ℕ) [NeZero A] [NeZero T] (Ω : Set (Fin n → ZMod W))
    (V : Finset (Fin n → ℤ)) (w : (Fin n → ℤ) → ℝ) :
    (∑ v ∈ V, w v * pointwiseBound F A T W Ω v) ≤
      (Nat.totient (A*T) : ℝ) * WeightedResidueMaximum.maximum A V w *
        zeroFiberTotal F A T W Ω := by
  unfold pointwiseBound
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ a : Fin (A*T), if Nat.Coprime a.val (A*T) then
        WeightedResidueMaximum.maximum A V w * zeroFiberTotal F A T W Ω else 0 := by
      apply Finset.sum_le_sum
      intro a _
      by_cases ha : Nat.Coprime a.val (A*T)
      · simp_rw [if_pos ha, Finset.mul_sum]
        rw [Finset.sum_comm, zeroFiberTotal, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro y _
        by_cases hy : integerResidue W (integerVector y) ∈ Ω
        · simp only [hy, true_and]
          simpa only [mul_ite, mul_zero] using
            FlexibleLifting.weighted_support_le F A T (a.val : ℤ) y V w
        · simp [hy]
      · simp [ha]
    _ = _ := by rw [LiftingTotient.sum_coprime_const]; ring

/-- The exact weighted flexible-lifting estimate with the residue
restriction retained in the zero-fiber terminal sum. -/
theorem weighted_complete_sum_le (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (A T W : ℕ) [NeZero A] [NeZero T] (hWA : W ∣ A)
    (Ω : Set (Fin n → ZMod W)) (V : Finset (Fin n → ℤ))
    (w : (Fin n → ℤ) → ℝ) (hw : ∀ v ∈ V, 0 ≤ w v) :
    (∑ v ∈ V, w v * ‖localizedCompleteCubicSum F (A^2*T) W Ω v‖) ≤
      (A : ℝ)^n * (Nat.totient (A^2*T) : ℝ) *
        WeightedResidueMaximum.maximum A V w * zeroFiberTotal F A T W Ω := by
  have hf : (A : ℝ)^(n+1) * (Nat.totient (A*T) : ℝ) =
      (A : ℝ)^n * (Nat.totient (A^2*T) : ℝ) := by
    simpa only [pow_two, mul_assoc] using
      LiftingTotient.real_lifting_factor A (A*T) n (dvd_mul_right A T)
  calc
    _ ≤ ∑ v ∈ V, w v * ((A : ℝ)^(n+1) * pointwiseBound F A T W Ω v) :=
      Finset.sum_le_sum fun v hv =>
        mul_le_mul_of_nonneg_left (norm_complete_sum_le F hF A T W hWA Ω v) (hw v hv)
    _ = (A : ℝ)^(n+1) * ∑ v ∈ V, w v * pointwiseBound F A T W Ω v := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ ≤ (A : ℝ)^(n+1) * ((Nat.totient (A*T) : ℝ) *
        WeightedResidueMaximum.maximum A V w * zeroFiberTotal F A T W Ω) :=
      mul_le_mul_of_nonneg_left (weighted_pointwise_le F A T W Ω V w) (by positivity)
    _ = _ := by
      calc
        _ = ((A : ℝ)^(n+1)*(Nat.totient (A*T) : ℝ)) *
            WeightedResidueMaximum.maximum A V w * zeroFiberTotal F A T W Ω := by ring
        _ = _ := by rw [hf]

end CubicTenVariables.LocalizedFlexibleLifting
