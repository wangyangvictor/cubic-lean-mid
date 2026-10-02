import CubicTenVariables.LocalizedPoissonArc
import CubicTenVariables.OscillatoryTrivialBound

/-! An elementary bound for the actual nonzero Poisson contribution on a
short phase interval. It is obtained from the finite physical generating
sum minus the zero mode, so no uniform infinite-frequency tail is assumed.
The only literature premise is generic Schwartz Poisson summation. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.LocalizedTinyPhase
open MvPolynomial MeasureTheory DeltaMethod LocalizedPoissonArc
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

theorem norm_generatingSum_le (G : MvPolynomial (Fin n) ℤ)
    (w : (Fin n → ℝ) → ℝ) (M : ℝ) (hM : ∀ y, |w y| ≤ M)
    (A P W : ℕ) (hP : 0 < P) (Ω : Set (Fin n → ZMod W)) (α : ℝ) :
    ‖localizedGeneratingSum G w A P W Ω α‖ ≤
      M*((2*A+1:ℕ):ℝ)^n*(P:ℝ)^n := by
  unfold localizedGeneratingSum finiteExponentialSum
  apply (norm_sum_le _ _).trans
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,norm_realExponential,mul_one]
    using countingWeight_l1_le w M hM A P W hP Ω

theorem norm_numerator_sum_le (G : MvPolynomial (Fin n) ℤ)
    (w : (Fin n → ℝ) → ℝ) (M : ℝ) (hM : ∀ y, |w y| ≤ M)
    (A P q W : ℕ) (hP : 0 < P) (Ω : Set (Fin n → ZMod W)) (θ : ℝ) :
    ‖∑ a : Fin q, if Nat.Coprime a.val q then
      localizedGeneratingSum G w A P W Ω ((a.val:ℝ)/(q:ℝ)+θ) else 0‖ ≤
      (q:ℝ)*(M*((2*A+1:ℕ):ℝ)^n*(P:ℝ)^n) := by
  have hM0 : 0 ≤ M := (abs_nonneg (w 0)).trans (hM 0)
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _a : Fin q, M*((2*A+1:ℕ):ℝ)^n*(P:ℝ)^n := by
      apply Finset.sum_le_sum
      intro a _
      split_ifs
      · exact norm_generatingSum_le G w M hM A P W hP Ω _
      · simp only [norm_zero]
        positivity
    _ = _ := by simp

/-- A bound valid for every real phase, including arbitrarily near zero.
The infinite nonzero series is the literal one in `nonzeroContribution`. -/
theorem norm_nonzeroContribution_le (lit : Literature.SteinShakarchi2011Poisson)
    (G : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ) (A P : ℕ)
    (hw : WeightSupportedInBox w A) (hw0 : w 0=0)
    (hs : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (M : ℝ) (hM : ∀ y, |w y| ≤ M) (hP : 0 < P)
    (q W : ℕ) (hq : 0 < q) (hW : 0 < W)
    (Ω : Set (Fin n → ZMod W)) (θ : ℝ) :
    ‖nonzeroContribution G w P q W Ω θ‖ ≤
      (q:ℝ)*(P:ℝ)^n*(M*((2*A+1:ℕ):ℝ)^n+∫ x : Fin n → ℝ, |w x|) := by
  have he : nonzeroContribution G w P q W Ω θ =
      (∑ a : Fin q, if Nat.Coprime a.val q then
        localizedGeneratingSum G w A P W Ω ((a.val:ℝ)/(q:ℝ)+θ) else 0) -
        zeroContribution G w P q W Ω θ := by
    rw [identity_split lit G w A P hw hw0 hs hc hP q W hq hW Ω θ]
    abel
  have hz : ‖zeroContribution G w P q W Ω θ‖ ≤
      (q:ℝ)*(P:ℝ)^n*(∫ x : Fin n → ℝ, |w x|) :=
    OscillatoryTrivialBound.norm_normalized_localized_term_le G w hs.continuous hc
      (P:ℝ) (by exact_mod_cast hP) q W hq hW Ω θ 0
  rw [he]
  calc
    _ ≤ ‖∑ a : Fin q, if Nat.Coprime a.val q then
        localizedGeneratingSum G w A P W Ω ((a.val:ℝ)/(q:ℝ)+θ) else 0‖ +
        ‖zeroContribution G w P q W Ω θ‖ := norm_sub_le _ _
    _ ≤ (q:ℝ)*(M*((2*A+1:ℕ):ℝ)^n*(P:ℝ)^n) +
        (q:ℝ)*(P:ℝ)^n*(∫ x : Fin n → ℝ, |w x|) :=
      add_le_add (norm_numerator_sum_le G w M hM A P q W hP Ω θ) hz
    _ = _ := by ring

/-- Every clipped subset of a short interval has a convergent kernel
integral with the interval-length factor. No global modulus sum is taken. -/
theorem integrableOn_and_norm_integral_le (lit : Literature.SteinShakarchi2011Poisson)
    (G : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ) (A P : ℕ)
    (hw : WeightSupportedInBox w A) (hw0 : w 0=0)
    (hs : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (M : ℝ) (hM : ∀ y, |w y| ≤ M) (hP : 0 < P)
    (q W : ℕ) (hq : 0 < q) (hW : 0 < W) (Ω : Set (Fin n → ZMod W))
    (p : ℝ → ℂ) (hp : Continuous p) (K τ : ℝ) (hK : 0 ≤ K) (hτ : 0 ≤ τ)
    (S : Set ℝ) (hS : S ⊆ Set.Icc (-τ) τ) (hbound : ∀ θ ∈ S, ‖p θ‖ ≤ K) :
    IntegrableOn (fun θ => p θ*nonzeroContribution G w P q W Ω θ) S ∧
    ‖∫ θ in S, p θ*nonzeroContribution G w P q W Ω θ‖ ≤
      2*τ*K*(q:ℝ)*(P:ℝ)^n*(M*((2*A+1:ℕ):ℝ)^n+∫ x : Fin n → ℝ, |w x|) := by
  have hi : IntegrableOn (fun θ => p θ*nonzeroContribution G w P q W Ω θ)
      (Set.Icc (-τ) τ) :=
    (hp.mul (continuous_nonzero lit G w A P hw hw0 hs hc hP q W hq hW Ω)).integrableOn_Icc
  refine ⟨hi.mono_set hS,?_⟩
  let C : ℝ := (q:ℝ)*(P:ℝ)^n*(M*((2*A+1:ℕ):ℝ)^n+∫ x : Fin n → ℝ, |w x|)
  have hM0 : 0 ≤ M := (abs_nonneg (w 0)).trans (hM 0)
  have hm : 0 ≤ ∫ x : Fin n → ℝ, |w x| := integral_nonneg fun _ => abs_nonneg _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hμ : volume S ≤ ENNReal.ofReal (2*τ) := by
    calc
      _ ≤ volume (Set.Icc (-τ) τ) := measure_mono hS
      _ = _ := by rw [Real.volume_Icc]; congr 1; ring
  have hfinite : volume S < ⊤ := lt_of_le_of_lt hμ ENNReal.ofReal_lt_top
  have hreal : volume.real S ≤ 2*τ := by
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hμ
    simpa only [Measure.real,ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*τ)] using ht
  calc
    _ ≤ (K*C)*volume.real S := norm_setIntegral_le_of_norm_le_const hfinite (by
      intro θ hθ
      rw [norm_mul]
      exact mul_le_mul (hbound θ hθ)
        (norm_nonzeroContribution_le lit G w A P hw hw0 hs hc M hM hP q W hq hW Ω θ)
        (norm_nonneg _) hK)
    _ ≤ (K*C)*(2*τ) := mul_le_mul_of_nonneg_left hreal (mul_nonneg hK hC)
    _ = _ := by dsimp [C]; ring

/-- The actual total nonzero contribution on arbitrarily clipped short
arcs. The modulus sum includes q=1 and costs at most Q². -/
theorem sum_integrableOn_and_norm_le (lit : Literature.SteinShakarchi2011Poisson)
    (G : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ) (A P : ℕ)
    (hw : WeightSupportedInBox w A) (hw0 : w 0=0)
    (hs : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (M : ℝ) (hM : ∀ y, |w y| ≤ M) (hP : 0 < P)
    (Q W : ℕ) (hW : 0 < W) (Ω : Set (Fin n → ZMod W))
    (p : ℕ → ℝ → ℂ) (K τ : ℝ) (hK : 0 ≤ K) (hτ : 0 ≤ τ)
    (S : ℕ → Set ℝ)
    (hp : ∀ q ∈ Finset.Icc 1 Q, Continuous (p q))
    (hS : ∀ q ∈ Finset.Icc 1 Q, S q ⊆ Set.Icc (-τ) τ)
    (hbound : ∀ q ∈ Finset.Icc 1 Q, ∀ θ ∈ S q, ‖p q θ‖ ≤ K) :
    (∀ q ∈ Finset.Icc 1 Q,
      IntegrableOn (fun θ => p q θ*nonzeroContribution G w P q W Ω θ) (S q)) ∧
    ‖∑ q ∈ Finset.Icc 1 Q,
      ∫ θ in S q, p q θ*nonzeroContribution G w P q W Ω θ‖ ≤
      2*τ*K*(Q:ℝ)^2*(P:ℝ)^n*(M*((2*A+1:ℕ):ℝ)^n+∫ x : Fin n → ℝ, |w x|) := by
  have hb (q : ℕ) (hq : q ∈ Finset.Icc 1 Q) :=
    integrableOn_and_norm_integral_le lit G w A P hw hw0 hs hc M hM hP q W
      (Finset.mem_Icc.mp hq).1 hW Ω (p q) (hp q hq) K τ hK hτ (S q) (hS q hq)
      (hbound q hq)
  refine ⟨fun q hq => (hb q hq).1,?_⟩
  have hM0 : 0 ≤ M := (abs_nonneg (w 0)).trans (hM 0)
  have hm : 0 ≤ ∫ x : Fin n → ℝ, |w x| := integral_nonneg fun _ => abs_nonneg _
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _q ∈ Finset.Icc 1 Q,
        2*τ*K*(Q:ℝ)*(P:ℝ)^n*(M*((2*A+1:ℕ):ℝ)^n+∫ x : Fin n → ℝ, |w x|) := by
      apply Finset.sum_le_sum
      intro q hq
      apply (hb q hq).2.trans
      have hqQ : (q:ℝ) ≤ Q := by exact_mod_cast (Finset.mem_Icc.mp hq).2
      gcongr
    _ = _ := by simp; ring

end CubicTenVariables.LocalizedTinyPhase
