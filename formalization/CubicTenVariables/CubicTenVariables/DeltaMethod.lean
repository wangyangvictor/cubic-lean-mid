import CubicTenVariables.Literature.MarmonVishe
import CubicTenVariables.WeightedCounting
import CubicTenVariables.IntegerProjectionCount
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Checked adapters for the explicit Marmon--Vishe input.
The source endpoint includes Q=1 by an elementary extension. All sums and
integrals are literal; finite weighted counting is derived from the scalar
integer delta identity, not included in the literature premise. -/

noncomputable section
namespace CubicTenVariables.DeltaMethod
open MvPolynomial MeasureTheory
open scoped BigOperators ContDiff

@[simp] theorem realExponential_zero : realExponential 0 = 1 := by
  simp [realExponential]

@[simp] theorem norm_realExponential (t : ℝ) : ‖realExponential t‖ = 1 := by
  simp [realExponential, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- The real-line character agrees exactly with the project's complete-sum
character; this fixes the sign and the factor 2*pi. -/
theorem realExponential_div (q : ℕ) (m : ℤ) :
    realExponential ((m : ℝ)/(q : ℝ)) = residueExponential q m := by
  simp only [realExponential,residueExponential,Complex.ofReal_div,
    Complex.ofReal_intCast,Complex.ofReal_natCast]
  congr 1
  ring

/-- The local rational phase splits with the same convention as completeCubicSum. -/
theorem realExponential_arc_phase (q a : ℕ) (θ : ℝ) (m : ℤ) :
    realExponential (((a : ℝ)/(q : ℝ)+θ)*(m : ℝ)) =
      residueExponential q ((a : ℤ)*m) * realExponential (θ*(m : ℝ)) := by
  unfold realExponential residueExponential
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact open-interval description, used to prove integrability rather than
silently interpreting a possibly divergent Bochner integral as zero. -/
theorem arc_eq_Ioo (Q q : ℕ) (η : ℝ) :
    arc Q q η = Set.Ioo (-(((q : ℝ)*(Q : ℝ))^(-1+η)))
      (((q : ℝ)*(Q : ℝ))^(-1+η)) := by
  ext θ
  change |θ| < _ ↔ _
  exact abs_lt

theorem deltaArc_integrable (p : ℕ → ℕ → ℝ → ℂ) (Q q a : ℕ)
    (η : ℝ) (m : ℤ) (hp : Continuous (p Q q)) :
    IntegrableOn (fun θ => p Q q θ *
      realExponential (((a : ℝ)/(q : ℝ)+θ)*(m : ℝ))) (arc Q q η) := by
  have hc : Continuous (fun θ => p Q q θ *
      realExponential (((a : ℝ)/(q : ℝ)+θ)*(m : ℝ))) := by
    unfold realExponential
    fun_prop
  rw [arc_eq_Ioo]
  exact hc.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self

/-- The Q=1 kernel may be zero because every requested error bound there
has scale one. This changes no estimate at Q>=2. -/
def extendKernel (p : ℕ → ℕ → ℝ → ℂ) (Q q : ℕ) (θ : ℝ) : ℂ :=
  if 2 ≤ Q then p Q q θ else 0

@[simp] theorem extendKernel_of_two_le (p) {Q : ℕ} (hQ : 2 ≤ Q) :
    extendKernel p Q = p Q := by
  funext q θ
  simp [extendKernel,hQ]

@[simp] theorem extendKernel_one (p) : extendKernel p 1 = 0 := by
  funext q θ
  simp [extendKernel]

theorem deltaApproximation_congr {p p' : ℕ → ℕ → ℝ → ℂ} (Q : ℕ)
    (h : p Q = p' Q) (η : ℝ) (m : ℤ) :
    deltaApproximation p Q η m = deltaApproximation p' Q η m := by
  simp only [deltaApproximation,deltaArc,h]

@[simp] theorem deltaApproximation_extend_one (p) (η : ℝ) (m : ℤ) :
    deltaApproximation (extendKernel p) 1 η m = 0 := by
  simp [deltaApproximation,deltaArc,extendKernel]

/-- Full required positive-integer-Q range, derived without adding a
literature assumption at the endpoint Q=1. -/
theorem KernelEstimates.extend {p : ℕ → ℕ → ℝ → ℂ}
    (hp : KernelEstimates 2 p) : KernelEstimates 1 (extendKernel p) := by
  constructor
  · intro Q hQ q hq hqQ
    by_cases h : 2 ≤ Q
    · simpa only [extendKernel_of_two_le p h] using hp.smooth Q h q hq hqQ
    · have h1 : Q=1 := by omega
      subst Q
      simpa only [extendKernel_one] using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0:ℂ)))
  · obtain ⟨C,hC,hb⟩ := hp.bounded
    refine ⟨C,hC,?_⟩
    intro Q hQ q hq hqQ θ
    by_cases h : 2 ≤ Q
    · simpa only [extendKernel_of_two_le p h] using hb Q h q hq hqQ θ
    · simp only [extendKernel,if_neg h,norm_zero]
      linarith
  · intro N hN
    obtain ⟨C,hC,hb⟩ := hp.near_one N hN
    refine ⟨C,hC,?_⟩
    intro Q hQ q hq hqQ θ hθ
    by_cases h : 2 ≤ Q
    · simpa only [extendKernel_of_two_le p h] using hb Q h q hq hqQ θ hθ
    · have h1 : Q=1 := by omega
      have hq1 : q=1 := by omega
      subst Q q
      simpa [extendKernel] using hC
  · intro η hη N hN
    obtain ⟨C,hC,hb⟩ := hp.delta η hη N hN
    refine ⟨C,hC,?_⟩
    intro Q hQ m
    by_cases h : 2 ≤ Q
    · rw [deltaApproximation_congr Q (extendKernel_of_two_le p h)]
      exact hb Q h m
    · have h1 : Q=1 := by omega
      subst Q
      simp only [deltaApproximation_extend_one,sub_zero,Nat.cast_one,Real.one_rpow,mul_one]
      by_cases hm : m=0
      · simpa [integerDelta,hm] using hC
      · simp [integerDelta,hm]
        linarith

/-- The manuscript's scalar delta-method proposition, with all kernel
properties and constants in the correct order, conditional only on the
explicit general literature proposition. -/
theorem exists_source_kernels (mv : Literature.MarmonVishe2019Proposition12) :
    ∃ p : ℕ → ℕ → ℝ → ℂ, KernelEstimates 1 p := by
  obtain ⟨p,hp⟩ := mv
  exact ⟨extendKernel p,hp.extend⟩

/-- A finite exponential generating function for arbitrary integer phases
and real weights. The cubic application uses f(x)=F(x) literally. -/
def finiteExponentialSum {ι : Type*} (V : Finset ι) (f : ι → ℤ)
    (w : ι → ℝ) (α : ℝ) : ℂ :=
  ∑ x ∈ V, (w x : ℂ)*realExponential (α*(f x : ℝ))

/-- The actual finite weighted count of phase-zero points. -/
def finiteZeroCount {ι : Type*} (V : Finset ι) (f : ι → ℤ) (w : ι → ℝ) : ℂ :=
  ∑ x ∈ V, if f x=0 then (w x : ℂ) else 0

/-- The literal finite arc expansion of the generating function. -/
def finiteArcApproximation {ι : Type*} (V : Finset ι) (f : ι → ℤ)
    (w : ι → ℝ) (p : ℕ → ℕ → ℝ → ℂ) (Q : ℕ) (η : ℝ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ Finset.Icc 1 q, if Nat.Coprime a q then
    ∫ θ in arc Q q η, p Q q θ * finiteExponentialSum V f w ((a : ℝ)/(q : ℝ)+θ)
  else 0

/-- All integral/sum exchanges are proved from continuous kernels on the
finite arcs; no summability premise replaces the desired identity. -/
theorem finiteArcApproximation_eq_sum {ι : Type*} (V : Finset ι) (f : ι → ℤ)
    (w : ι → ℝ) (p : ℕ → ℕ → ℝ → ℂ) (Q : ℕ) (η : ℝ)
    (hp : ∀ q ∈ Finset.Icc 1 Q, Continuous (p Q q)) :
    finiteArcApproximation V f w p Q η =
      ∑ x ∈ V, (w x : ℂ)*deltaApproximation p Q η (f x) := by
  classical
  have hi (q : ℕ) (hq : q ∈ Finset.Icc 1 Q) (a : ℕ) :
      (∫ θ in arc Q q η, p Q q θ * finiteExponentialSum V f w ((a : ℝ)/(q : ℝ)+θ)) =
        ∑ x ∈ V, (w x : ℂ)*deltaArc p Q q a η (f x) := by
    simp only [finiteExponentialSum,Finset.mul_sum]
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro x hx
      simp only [deltaArc, ← integral_const_mul]
      congr 1
      funext θ
      ring
    · intro x hx
      have hh := (deltaArc_integrable p Q q a η (f x) (hp q hq)).const_mul (w x : ℂ)
      convert hh using 1
      ext θ
      ring
  unfold finiteArcApproximation deltaApproximation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases h : Nat.Coprime a q
  · simp only [if_pos h]
    exact hi q hq a
  · simp [h]

/-- Finite weighted delta assembly. The only loss is the actual l1 mass of
weights, so signed weights and arbitrary finite supports are allowed. -/
theorem finite_count_error_of_bound {ι : Type*} (V : Finset ι) (f : ι → ℤ) (w : ι → ℝ)
    (p : ℕ → ℕ → ℝ → ℂ) (hp : KernelEstimates 1 p)
    (η : ℝ) (Q : ℕ) (hQ : 1 ≤ Q) (E : ℝ)
    (hb : ∀ m : ℤ, ‖integerDelta m - deltaApproximation p Q η m‖ ≤ E) :
    ‖finiteZeroCount V f w - finiteArcApproximation V f w p Q η‖ ≤
      (∑ x ∈ V, |w x|) * E := by
  classical
  rw [finiteArcApproximation_eq_sum V f w p Q η (fun q hq =>
    (hp.smooth Q hQ q (Finset.mem_Icc.mp hq).1 (Finset.mem_Icc.mp hq).2).continuous)]
  have hc : finiteZeroCount V f w = ∑ x ∈ V, (w x : ℂ)*integerDelta (f x) := by
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : f x=0 <;> simp [integerDelta,h]
  rw [hc,← Finset.sum_sub_distrib]
  calc
    ‖∑ x ∈ V, ((w x : ℂ)*integerDelta (f x)-(w x : ℂ)*deltaApproximation p Q η (f x))‖
      ≤ ∑ x ∈ V, ‖(w x : ℂ)*integerDelta (f x)-(w x : ℂ)*deltaApproximation p Q η (f x)‖ :=
        norm_sum_le _ _
    _ = ∑ x ∈ V, |w x| *‖integerDelta (f x)-deltaApproximation p Q η (f x)‖ := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    _ ≤ ∑ x ∈ V, |w x| *E :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hb (f x)) (abs_nonneg _))
    _ = _ := (Finset.sum_mul ..).symm

/-- The error constant is selected before the scale and all finite weighted
integer-phase sums. It depends only on the chosen kernels, eta and N. -/
theorem exists_uniform_finite_count_error {n : ℕ}
    (p : ℕ → ℕ → ℝ → ℂ) (hp : KernelEstimates 1 p)
    (η : ℝ) (hη : 0 < η) (N : ℕ) (hN : 1 ≤ N) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ Q : ℕ, 1 ≤ Q →
      ∀ (V : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → ℤ) (w : (Fin n → ℤ) → ℝ),
        ‖finiteZeroCount V f w - finiteArcApproximation V f w p Q η‖ ≤
          (∑ x ∈ V, |w x|) * (C*(Q : ℝ)^(-(N : ℝ)*η)) := by
  obtain ⟨C,hC,hb⟩ := hp.delta η hη N hN
  exact ⟨C,hC,fun Q hQ V f w => finite_count_error_of_bound V f w p hp η Q hQ _ (hb Q hQ)⟩

/-- The real counting weight, including the existing nonzero-vector and
fixed congruence restrictions, but without imposing F(x)=0. -/
def countingWeight {n : ℕ} (w : (Fin n → ℝ) → ℝ) (P W : ℕ)
    (Ω : Set (Fin n → ZMod W)) (x : Fin n → ℤ) : ℝ := by
  classical
  exact if x ≠ 0 ∧ integerResidue W x ∈ Ω then w (scaledIntegerPoint P x) else 0

/-- The finite zero-weight sum is the already-defined actual project count. -/
theorem finiteZeroCount_eq_localizedWeightedCount {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ)
    (A P W : ℕ) (Ω : Set (Fin n → ZMod W)) :
    finiteZeroCount (integerBox n (A*P)) (fun x => eval x F) (countingWeight w P W Ω) =
      (localizedWeightedCount F w A P W Ω : ℂ) := by
  classical
  simp only [finiteZeroCount,localizedWeightedCount,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h0 : x=0 <;> by_cases hF : eval x F=0 <;>
    by_cases hΩ : integerResidue W x ∈ Ω <;>
    simp [countingWeight,localizedWeightedSummand,h0,hF,hΩ]

/-- The source exponential generating function, with the same localization
and origin convention as localizedWeightedCount. -/
def localizedGeneratingSum {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (w : (Fin n → ℝ) → ℝ) (A P W : ℕ) (Ω : Set (Fin n → ZMod W)) (α : ℝ) : ℂ :=
  finiteExponentialSum (integerBox n (A*P)) (fun x => eval x F) (countingWeight w P W Ω) α

/-- The finite generating function includes every nonzero term of the
full lattice sum. No totalized divergent sum is used in the adapter. -/
theorem localizedGeneratingSum_hasSum {n A P : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ)
    (hw : WeightSupportedInBox w A) (hP : 0 < P)
    (W : ℕ) (Ω : Set (Fin n → ZMod W)) (α : ℝ) :
    HasSum (fun x : Fin n → ℤ => (countingWeight w P W Ω x : ℂ)*
      realExponential (α*(eval x F : ℝ))) (localizedGeneratingSum F w A P W Ω α) := by
  classical
  apply hasSum_sum_of_ne_finset_zero
  intro x hx
  have hwx : w (scaledIntegerPoint P x)=0 := by
    by_contra h
    exact hx (scaled_weight_support w hw hP x h)
  simp [countingWeight,hwx]

/-- Concrete localized counting expansion; one constant precedes both P
and Q. This estimate retains the exact l1 mass of the sampled weight. -/
theorem exists_localized_count_error {n : ℕ}
    (mv : Literature.MarmonVishe2019Proposition12)
    (F : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ)
    (A W : ℕ) (Ω : Set (Fin n → ZMod W)) :
    ∃ p : ℕ → ℕ → ℝ → ℂ, KernelEstimates 1 p ∧
      ∀ η : ℝ, 0 < η → ∀ N : ℕ, 1 ≤ N → ∃ C : ℝ, 1 ≤ C ∧
        ∀ P Q : ℕ, 1 ≤ Q →
          ‖(localizedWeightedCount F w A P W Ω : ℂ) -
            ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ Finset.Icc 1 q, if Nat.Coprime a q then
              ∫ θ in arc Q q η, p Q q θ *
                localizedGeneratingSum F w A P W Ω ((a : ℝ)/(q : ℝ)+θ) else 0‖ ≤
          (∑ x ∈ integerBox n (A*P), |countingWeight w P W Ω x|) *
            (C*(Q : ℝ)^(-(N : ℝ)*η)) := by
  obtain ⟨p,hp⟩ := exists_source_kernels mv
  refine ⟨p,hp,?_⟩
  intro η hη N hN
  obtain ⟨C,hC,hb⟩ := hp.delta η hη N hN
  refine ⟨C,hC,?_⟩
  intro P Q hQ
  have h := finite_count_error_of_bound (integerBox n (A*P)) (fun x => eval x F)
    (countingWeight w P W Ω) p hp η Q hQ _ (hb Q hQ)
  rw [finiteZeroCount_eq_localizedWeightedCount] at h
  exact h

/-- A bounded weight on the actual integer box has the P^n mass required
in the counting formula. Congruence restrictions only decrease this mass. -/
theorem countingWeight_l1_le {n : ℕ} (w : (Fin n → ℝ) → ℝ)
    (M : ℝ) (hM : ∀ y, |w y| ≤ M) (A P W : ℕ) (hP : 1 ≤ P)
    (Ω : Set (Fin n → ZMod W)) :
    (∑ x ∈ integerBox n (A*P), |countingWeight w P W Ω x|) ≤
      M * ((2*A+1 : ℕ) : ℝ)^n * (P : ℝ)^n := by
  classical
  have hM0 : 0 ≤ M := (abs_nonneg (w 0)).trans (hM 0)
  have hx (x : Fin n → ℤ) : |countingWeight w P W Ω x| ≤ M := by
    unfold countingWeight
    split_ifs
    · exact hM _
    · simpa using hM0
  have hb : ((2*(A*P)+1 : ℕ) : ℝ) ≤ ((2*A+1 : ℕ) : ℝ)*(P : ℝ) := by
    have hp : (1:ℝ) ≤ P := by exact_mod_cast hP
    push_cast
    nlinarith
  calc
    (∑ x ∈ integerBox n (A*P), |countingWeight w P W Ω x|)
      ≤ ∑ _x ∈ integerBox n (A*P), M := Finset.sum_le_sum (fun x _ => hx x)
    _ = M * (((2*(A*P)+1 : ℕ) : ℝ)^n) := by
      simp only [Finset.sum_const, nsmul_eq_mul, card_integerBox, Nat.cast_pow]
      ring
    _ ≤ M * ((((2*A+1 : ℕ) : ℝ)*(P : ℝ))^n) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb _) hM0
    _ = _ := by rw [mul_pow]; ring

/-- The actual localized cubic counting formula with the manuscript's
P^n Q^(-N eta) error. The integer polynomial may have any degree: no cubic
counting conclusion is assumed as a literature input. Bounded support is
used separately by localizedGeneratingSum_hasSum to identify the finite
generating sum with the full lattice sum. -/
theorem exists_localized_count_power_error {n : ℕ}
    (mv : Literature.MarmonVishe2019Proposition12)
    (F : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ)
    (M : ℝ) (hM : ∀ y, |w y| ≤ M)
    (A W : ℕ) (Ω : Set (Fin n → ZMod W)) :
    ∃ p : ℕ → ℕ → ℝ → ℂ, KernelEstimates 1 p ∧
      ∀ η : ℝ, 0 < η → ∀ N : ℕ, 1 ≤ N → ∃ C : ℝ, 1 ≤ C ∧
        ∀ P Q : ℕ, 1 ≤ P → 1 ≤ Q →
          ‖(localizedWeightedCount F w A P W Ω : ℂ) -
            ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ Finset.Icc 1 q, if Nat.Coprime a q then
              ∫ θ in arc Q q η, p Q q θ *
                localizedGeneratingSum F w A P W Ω ((a : ℝ)/(q : ℝ)+θ) else 0‖ ≤
          C*(P : ℝ)^n*(Q : ℝ)^(-(N : ℝ)*η) := by
  obtain ⟨p,hp,h⟩ := exists_localized_count_error mv F w A W Ω
  refine ⟨p,hp,?_⟩
  intro η hη N hN
  obtain ⟨C,hC,hb⟩ := h η hη N hN
  refine ⟨max 1 (M*((2*A+1 : ℕ) : ℝ)^n*C), le_max_left _ _, ?_⟩
  intro P Q hP hQ
  calc
    _ ≤ (∑ x ∈ integerBox n (A*P), |countingWeight w P W Ω x|) *
      (C*(Q : ℝ)^(-(N : ℝ)*η)) := hb P Q hQ
    _ ≤ (M*((2*A+1 : ℕ) : ℝ)^n*(P : ℝ)^n) *
      (C*(Q : ℝ)^(-(N : ℝ)*η)) :=
        mul_le_mul_of_nonneg_right (countingWeight_l1_le w M hM A P W hP Ω)
          (mul_nonneg (by linarith) (Real.rpow_nonneg (by positivity) _))
    _ = (M*((2*A+1 : ℕ) : ℝ)^n*C)*(P : ℝ)^n*(Q : ℝ)^(-(N : ℝ)*η) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
      (Real.rpow_nonneg (by positivity) _)

/-- For the manuscript's weight, which vanishes at the origin, taking all
residue classes recovers the unrestricted sampled weight exactly. -/
theorem countingWeight_univ {n : ℕ} (w : (Fin n → ℝ) → ℝ) (hw0 : w 0=0)
    (P W : ℕ) (x : Fin n → ℤ) : countingWeight w P W Set.univ x = w (scaledIntegerPoint P x) := by
  classical
  by_cases hx : x=0
  · subst x
    simp [countingWeight,hw0]
  · simp [countingWeight,hx]

/-- Literal unrestricted lattice generating series, with its actual
summability supplied by bounded support. -/
theorem localizedGeneratingSum_eq_source_tsum {n A P : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ)
    (hw : WeightSupportedInBox w A) (hw0 : w 0=0) (hP : 0 < P) (α : ℝ) :
    localizedGeneratingSum F w A P 1 Set.univ α =
      ∑' x : Fin n → ℤ, (w (scaledIntegerPoint P x) : ℂ)*realExponential (α*(eval x F : ℝ)) := by
  have h := localizedGeneratingSum_hasSum F w hw hP 1 Set.univ α
  simp only [countingWeight_univ w hw0] at h
  exact h.tsum_eq.symm

/-- The source counting expansion for literal full lattice sums, at the
positive integral P scales used by the project's Diophantine endpoint.
There is only the explicit Marmon--Vishe premise; every summation adapter
and P^n loss has been proved above. -/
theorem exists_source_count_expansion {n : ℕ}
    (mv : Literature.MarmonVishe2019Proposition12)
    (F : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ) (A : ℕ)
    (hw : WeightSupportedInBox w A) (hw0 : w 0=0)
    (M : ℝ) (hM : ∀ y, |w y| ≤ M) :
    ∃ p : ℕ → ℕ → ℝ → ℂ, KernelEstimates 1 p ∧
      ∀ η : ℝ, 0 < η → ∀ N : ℕ, 1 ≤ N → ∃ C : ℝ, 1 ≤ C ∧
        ∀ P Q : ℕ, 1 ≤ P → 1 ≤ Q →
          ‖(((∑' x : Fin n → ℤ, if eval x F=0 then w (scaledIntegerPoint P x) else 0) : ℝ) : ℂ) -
            ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ Finset.Icc 1 q, if Nat.Coprime a q then
              ∫ θ in arc Q q η, p Q q θ *
                (∑' x : Fin n → ℤ, (w (scaledIntegerPoint P x) : ℂ)*
                  realExponential (((a : ℝ)/(q : ℝ)+θ)*(eval x F : ℝ))) else 0‖ ≤
          C*(P : ℝ)^n*(Q : ℝ)^(-(N : ℝ)*η) := by
  obtain ⟨p,hp,h⟩ := exists_localized_count_power_error mv F w M hM A 1 Set.univ
  refine ⟨p,hp,?_⟩
  intro η hη N hN
  obtain ⟨C,hC,hb⟩ := h η hη N hN
  refine ⟨C,hC,?_⟩
  intro P Q hP hQ
  have hP0 : 0 < P := by omega
  have hb' := hb P Q hP hQ
  rw [localizedWeightedCount_eq_source_tsum F w hw hw0 hP0] at hb'
  simpa only [Set.mem_univ, and_true,
    localizedGeneratingSum_eq_source_tsum F w hw hw0 hP0] using hb'

end CubicTenVariables.DeltaMethod
