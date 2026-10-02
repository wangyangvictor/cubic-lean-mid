import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Elementary moment contradiction in the trace argument. A moment of
order p^(a*m), divided by p^(a*(m+1)), tends to zero. Literal finite sums
of squared complex norms are monotone under inclusion, so a bound on an
ambient plane applies to every finite subset. The sheaf-theoretic
pointwise-bound-or-large-moment alternative is never asserted here: every
use retains that alternative as an explicit hypothesis. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.MomentTraceNumerics

open Filter
open scoped BigOperators Topology

/-- Exact cancellation of the common exponential scale. -/
theorem normalized_power (p C : ℝ) (hp : p ≠ 0) (a m : ℕ) :
    C*p^(a*m)/p^(a*(m+1)) = C*(p⁻¹)^a := by
  rw [Nat.mul_add, Nat.mul_one, pow_add, div_mul_eq_div_div,
    mul_div_cancel_right₀ _ (pow_ne_zero _ hp), div_eq_mul_inv, inv_pow]

/-- A nonnegative moment bounded eventually by C*p^(a*m) has vanishing
normalization at the next integral weight. There is no regularity premise
on the sequence A and no sign premise on C is needed. -/
theorem normalized_moment_tendsto (p C : ℝ) (hp : 2 ≤ p) (m : ℕ)
    (A : ℕ → ℝ) (hA : ∀ᶠ a in atTop, 0 ≤ A a)
    (hbound : ∀ᶠ a in atTop, A a ≤ C*p^(a*m)) :
    Tendsto (fun a => A a / p^(a*(m+1))) atTop (𝓝 0) := by
  have hp0 : 0 < p := by linarith
  have hi : p⁻¹ < 1 := (inv_lt_one₀ hp0).mpr (by linarith)
  have ht : Tendsto (fun a : ℕ => C*(p⁻¹)^a) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hp0.le) hi).const_mul C
  apply squeeze_zero' _ _ ht
  · filter_upwards [hA] with a ha
    exact div_nonneg ha (pow_nonneg hp0.le _)
  · filter_upwards [hbound] with a ha
    calc
      _ ≤ C*p^(a*m)/p^(a*(m+1)) :=
        div_le_div_of_nonneg_right ha (pow_nonneg hp0.le _)
      _ = C*(p⁻¹)^a := normalized_power p C hp0.ne' a m

theorem normalized_moment_limsup (p C : ℝ) (hp : 2 ≤ p) (m : ℕ)
    (A : ℕ → ℝ) (hA : ∀ᶠ a in atTop, 0 ≤ A a)
    (hbound : ∀ᶠ a in atTop, A a ≤ C*p^(a*m)) :
    limsup (fun a => A a / p^(a*(m+1))) atTop = 0 :=
  (normalized_moment_tendsto p C hp m A hA hbound).limsup_eq

/-- The large-moment alternative is impossible under the smaller moment
bound; this implication is purely numerical. -/
theorem not_large_normalized_moment (p C : ℝ) (hp : 2 ≤ p) (m : ℕ)
    (A : ℕ → ℝ) (hA : ∀ᶠ a in atTop, 0 ≤ A a)
    (hbound : ∀ᶠ a in atTop, A a ≤ C*p^(a*m)) :
    ¬ 1 ≤ limsup (fun a => A a / p^(a*(m+1))) atTop := by
  rw [normalized_moment_limsup p C hp m A hA hbound]
  norm_num

theorem resolve_moment_alternative (p C : ℝ) (hp : 2 ≤ p) (m : ℕ)
    (A : ℕ → ℝ) (hA : ∀ᶠ a in atTop, 0 ≤ A a)
    (hbound : ∀ᶠ a in atTop, A a ≤ C*p^(a*m)) (B : Prop)
    (halt : B ∨ 1 ≤ limsup (fun a => A a / p^(a*(m+1))) atTop) : B :=
  halt.resolve_right (not_large_normalized_moment p C hp m A hA hbound)

/-- Inclusion of finite frequency sets preserves their literal second
moments. In particular no assumption excluding the zero frequency is needed. -/
theorem norm_sq_sum_mono {α : Type*} (U L : Finset α) (hUL : U ⊆ L)
    (T : α → ℂ) :
    ∑ v ∈ U, ‖T v‖^2 ≤ ∑ v ∈ L, ‖T v‖^2 := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hUL (fun _ _ _ => sq_nonneg _)

/-- Finite ambient spaces may vary with the extension degree. A bound on
the larger frequency set for every a≥1 suffices for the subset's limit. -/
theorem finite_moment_tendsto {α : ℕ → Type*}
    (U L : (a : ℕ) → Finset (α a)) (T : (a : ℕ) → α a → ℂ)
    (p C : ℝ) (hp : 2 ≤ p) (m : ℕ)
    (hUL : ∀ a, 1 ≤ a → U a ⊆ L a)
    (hbound : ∀ a, 1 ≤ a → ∑ v ∈ L a, ‖T a v‖^2 ≤ C*(p^a)^m) :
    Tendsto (fun a => (∑ v ∈ U a, ‖T a v‖^2) / p^(a*(m+1))) atTop (𝓝 0) := by
  apply normalized_moment_tendsto p C hp m (fun a => ∑ v ∈ U a, ‖T a v‖^2)
  · exact Eventually.of_forall fun a => Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with a ha
    exact (norm_sq_sum_mono (U a) (L a) (hUL a ha) (T a)).trans
      (by simpa only [pow_mul] using hbound a ha)

theorem finite_moment_limsup {α : ℕ → Type*}
    (U L : (a : ℕ) → Finset (α a)) (T : (a : ℕ) → α a → ℂ)
    (p C : ℝ) (hp : 2 ≤ p) (m : ℕ)
    (hUL : ∀ a, 1 ≤ a → U a ⊆ L a)
    (hbound : ∀ a, 1 ≤ a → ∑ v ∈ L a, ‖T a v‖^2 ≤ C*(p^a)^m) :
    limsup (fun a => (∑ v ∈ U a, ‖T a v‖^2) / p^(a*(m+1))) atTop = 0 :=
  (finite_moment_tendsto U L T p C hp m hUL hbound).limsup_eq

/-- A supplied pointwise-bound-or-large-moment alternative yields its
pointwise branch when the ambient finite sets satisfy the smaller moment
bound. The alternative is an explicit antecedent, not a proved sheaf input. -/
theorem pointwise_bound_of_alternative {α : ℕ → Type*}
    (U L : (a : ℕ) → Finset (α a)) (T : (a : ℕ) → α a → ℂ)
    (p C : ℝ) (hp : 2 ≤ p) (m : ℕ) (B : ℕ → ℝ)
    (hUL : ∀ a, 1 ≤ a → U a ⊆ L a)
    (hbound : ∀ a, 1 ≤ a → ∑ v ∈ L a, ‖T a v‖^2 ≤ C*(p^a)^m)
    (halt : (∀ a, 1 ≤ a → ∀ v ∈ U a, ‖T a v‖ ≤ B a) ∨
      1 ≤ limsup (fun a => (∑ v ∈ U a, ‖T a v‖^2) / p^(a*(m+1))) atTop) :
    ∀ a, 1 ≤ a → ∀ v ∈ U a, ‖T a v‖ ≤ B a := by
  apply halt.resolve_right
  rw [finite_moment_limsup U L T p C hp m hUL hbound]
  norm_num

end CubicTenVariables.MomentTraceNumerics
