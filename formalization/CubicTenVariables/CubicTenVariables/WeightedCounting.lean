import CubicTenVariables.CountingEndpoint
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Ring.Real

/-! The actual localized weighted counting functional and its final endpoint.

The source uses `w(x/P)` and an allowed set of residues modulo a fixed `W`.
We sample `P` at natural numbers, which suffices for the existence conclusion.
If the real weight is supported in the box of radius `A`, all contributing
vectors lie in `integerBox n (A*P)`. The finite sum is proved equal to the
full sum at positive scales. Smoothness is not needed for these endpoint
lemmas, and signed weights are allowed. No asymptotic estimate is asserted.
-/

noncomputable section
namespace CubicTenVariables
open MvPolynomial Filter
open scoped BigOperators Topology Classical

/-- The real vector `x/P` appearing in the manuscript's weight. -/
def scaledIntegerPoint {n : ℕ} (P : ℕ) (x : Fin n → ℤ) : Fin n → ℝ :=
  fun i => (x i : ℝ) / (P : ℝ)

@[simp] theorem scaledIntegerPoint_zero {n : ℕ} (P : ℕ) :
    scaledIntegerPoint P (0 : Fin n → ℤ) = 0 := by
  ext i
  simp [scaledIntegerPoint]

/-- The actual residue vector modulo the fixed integer `W`. In analytic
applications `W≥1`; the endpoint does not need this additional premise. -/
def integerResidue {n : ℕ} (W : ℕ) (x : Fin n → ℤ) : Fin n → ZMod W :=
  fun i => (x i : ZMod W)

/-- A coordinatewise bounded-support condition for the real weight. -/
def WeightSupportedInBox {n : ℕ} (w : (Fin n → ℝ) → ℝ) (A : ℕ) : Prop :=
  ∀ y, w y ≠ 0 → ∀ i, |y i| ≤ (A : ℝ)

/-- The actual summand: the vector is nonzero, is an integral zero of F,
and lies in the allowed residue set. -/
def localizedWeightedSummand {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (w : (Fin n → ℝ) → ℝ) (P W : ℕ) (Ω : Set (Fin n → ZMod W))
    (x : Fin n → ℤ) : ℝ := by
  classical
  exact if x ≠ 0 ∧ eval x F = 0 ∧ integerResidue W x ∈ Ω then
    w (scaledIntegerPoint P x) else 0

/-- A finite, concrete localized weighted count at natural scale P.
The origin is excluded even for weights that do not vanish there. -/
def localizedWeightedCount {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (w : (Fin n → ℝ) → ℝ) (A P W : ℕ)
    (Ω : Set (Fin n → ZMod W)) : ℝ :=
  ∑ x ∈ integerBox n (A * P), localizedWeightedSummand F w P W Ω x

/-- The weight's support places every nonzero summand in the actual finite box. -/
theorem scaled_weight_support {n A P : ℕ} (w : (Fin n → ℝ) → ℝ)
    (hw : WeightSupportedInBox w A) (hP : 0 < P) (x : Fin n → ℤ)
    (hx : w (scaledIntegerPoint P x) ≠ 0) : x ∈ integerBox n (A * P) := by
  rw [mem_integerBox]
  intro i
  have hi := hw _ hx i
  have hp : (0 : ℝ) < P := by exact_mod_cast hP
  change |(x i : ℝ) / (P : ℝ)| ≤ (A : ℝ) at hi
  rw [abs_div, abs_of_pos hp] at hi
  have hb : |(x i : ℝ)| ≤ (A : ℝ) * (P : ℝ) := (div_le_iff₀ hp).mp hi
  exact_mod_cast hb

theorem localizedWeightedSummand_eq_zero_outside_box {n A P : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ)
    (hw : WeightSupportedInBox w A) (hP : 0 < P)
    (W : ℕ) (Ω : Set (Fin n → ZMod W)) (x : Fin n → ℤ)
    (hx : x ∉ integerBox n (A * P)) : localizedWeightedSummand F w P W Ω x = 0 := by
  classical
  have hz : w (scaledIntegerPoint P x) = 0 := by
    by_contra h
    exact hx (scaled_weight_support w hw hP x h)
  simp [localizedWeightedSummand, hz]

/-- The full localized series actually converges to the displayed finite count.
This prevents the default value of `tsum` for a divergent series from entering
the identification with the source functional. -/
theorem localizedWeightedSummand_hasSum {n A P : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ)
    (hw : WeightSupportedInBox w A) (hP : 0 < P)
    (W : ℕ) (Ω : Set (Fin n → ZMod W)) :
    HasSum (localizedWeightedSummand F w P W Ω)
      (localizedWeightedCount F w A P W Ω) :=
  hasSum_sum_of_ne_finset_zero (fun x hx =>
    localizedWeightedSummand_eq_zero_outside_box F w hw hP W Ω x hx)

/-- With bounded support, this finite count is the complete sum over all
integer vectors; no contributing terms have been truncated. -/
theorem localizedWeightedCount_eq_tsum {n A P : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ)
    (hw : WeightSupportedInBox w A) (hP : 0 < P)
    (W : ℕ) (Ω : Set (Fin n → ZMod W)) :
    localizedWeightedCount F w A P W Ω =
      ∑' x : Fin n → ℤ, localizedWeightedSummand F w P W Ω x := by
  symm
  exact tsum_eq_sum (fun x hx =>
    localizedWeightedSummand_eq_zero_outside_box F w hw hP W Ω x hx)

/-- If the weight vanishes at zero, excluding the zero vector does not
change the manuscript's summand. -/
theorem localizedWeightedSummand_eq_source {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ) (hw0 : w 0 = 0)
    (P W : ℕ) (Ω : Set (Fin n → ZMod W)) (x : Fin n → ℤ) :
    localizedWeightedSummand F w P W Ω x =
      if eval x F = 0 ∧ integerResidue W x ∈ Ω then
        w (scaledIntegerPoint P x) else 0 := by
  classical
  by_cases hx : x = 0
  · subst x
    simp [localizedWeightedSummand, hw0]
  · simp [localizedWeightedSummand, hx]

/-- Equality with the precise manuscript count, including its residue
restriction and scaling. Bounded support and w(0)=0 make the infinite
expression a finite sum of nonzero-vector contributions. -/
theorem localizedWeightedCount_eq_source_tsum {n A P : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ)
    (hw : WeightSupportedInBox w A) (hw0 : w 0 = 0) (hP : 0 < P)
    (W : ℕ) (Ω : Set (Fin n → ZMod W)) :
    localizedWeightedCount F w A P W Ω =
      ∑' x : Fin n → ℤ, if eval x F = 0 ∧ integerResidue W x ∈ Ω then
        w (scaledIntegerPoint P x) else 0 := by
  rw [localizedWeightedCount_eq_tsum F w hw hP W Ω]
  exact tsum_congr (localizedWeightedSummand_eq_source F w hw0 P W Ω)

/-- Without a nonzero integral zero the actual weighted count is identically
zero, irrespective of signs, support, or the allowed residue set. -/
theorem localizedWeightedCount_eq_zero_of_not_hasIntegerZero {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : ¬ HasIntegerZero F)
    (w : (Fin n → ℝ) → ℝ) (A P W : ℕ) (Ω : Set (Fin n → ZMod W)) :
    localizedWeightedCount F w A P W Ω = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro x hx
  unfold localizedWeightedSummand
  split_ifs with h
  · exact (hF ⟨x, h.1, h.2.1⟩).elim
  · rfl

theorem hasIntegerZero_of_localizedWeightedCount_pos {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ)
    (A P W : ℕ) (Ω : Set (Fin n → ZMod W))
    (h : 0 < localizedWeightedCount F w A P W Ω) : HasIntegerZero F := by
  by_contra hF
  rw [localizedWeightedCount_eq_zero_of_not_hasIntegerZero F hF w A P W Ω] at h
  exact (lt_irrefl 0) h

/-- Positive normalized limit implies eventual positivity of the actual
finite weighted count. The exponent may be any natural number. -/
theorem eventually_localizedWeightedCount_pos_of_tendsto {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ)
    (A W : ℕ) (Ω : Set (Fin n → ZMod W)) (k : ℕ)
    {c : ℝ} (hc : 0 < c)
    (hlim : Tendsto (fun P : ℕ => localizedWeightedCount F w A P W Ω / (P : ℝ) ^ k)
      atTop (𝓝 c)) :
    ∀ᶠ P : ℕ in atTop, 0 < localizedWeightedCount F w A P W Ω := by
  filter_upwards [hlim.eventually_const_lt hc, eventually_gt_atTop 0] with P hP hpos
  have hp : (0 : ℝ) < P := by exact_mod_cast hpos
  exact (div_pos_iff_of_pos_right (pow_pos hp k)).mp hP

theorem hasIntegerZero_of_localizedWeightedCount_tendsto {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ)
    (A W : ℕ) (Ω : Set (Fin n → ZMod W)) (k : ℕ)
    {c : ℝ} (hc : 0 < c)
    (hlim : Tendsto (fun P : ℕ => localizedWeightedCount F w A P W Ω / (P : ℝ) ^ k)
      atTop (𝓝 c)) : HasIntegerZero F := by
  obtain ⟨P, hP⟩ := (eventually_localizedWeightedCount_pos_of_tendsto
    F w A W Ω k hc hlim).exists
  exact hasIntegerZero_of_localizedWeightedCount_pos F w A P W Ω hP

/-- Ten-variable endpoint after a proved main/error decomposition of the
actual functional. Both normalized limits are explicit hypotheses; this
lemma does not assert either analytic estimate. -/
theorem ten_variable_weighted_endpoint
    (F : MvPolynomial (Fin 10) ℤ) (w : (Fin 10 → ℝ) → ℝ)
    (A W : ℕ) (Ω : Set (Fin 10 → ZMod W))
    (main error : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (hdecomp : ∀ᶠ P : ℕ in atTop,
      localizedWeightedCount F w A P W Ω = main P + error P)
    (hmain : Tendsto (fun P : ℕ => main P / (P : ℝ) ^ 7) atTop (𝓝 c))
    (herror : Tendsto (fun P : ℕ => error P / (P : ℝ) ^ 7) atTop (𝓝 0)) :
    (∀ᶠ P : ℕ in atTop, 0 < localizedWeightedCount F w A P W Ω) ∧ HasIntegerZero F := by
  have hlim : Tendsto (fun P : ℕ => localizedWeightedCount F w A P W Ω / (P : ℝ) ^ 7)
      atTop (𝓝 c) := by
    have h := hmain.add herror
    rw [add_zero] at h
    apply h.congr'
    filter_upwards [hdecomp] with P hP
    rw [hP, add_div]
  exact ⟨eventually_localizedWeightedCount_pos_of_tendsto F w A W Ω 7 hc hlim,
    hasIntegerZero_of_localizedWeightedCount_tendsto F w A W Ω 7 hc hlim⟩

end CubicTenVariables
