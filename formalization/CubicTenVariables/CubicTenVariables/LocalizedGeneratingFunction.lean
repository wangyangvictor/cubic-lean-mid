import CubicTenVariables.LocalizedPeriodicPhase

/-! The literal finite generating function as a convergent lattice series
with its true periodic coefficient. The vanishing weight at the origin
removes precisely the source's explicit origin exclusion. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.LocalizedGeneratingFunction
open MvPolynomial DeltaMethod LocalizedPeriodicPhase
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def sampledPhase (G : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ)
    (P : ℕ) (θ : ℝ) (x : Fin n → ℤ) : ℂ :=
  (w (scaledIntegerPoint P x):ℂ)*realExponential (θ*(eval x G:ℝ))

theorem coefficient_phase_eq (G : MvPolynomial (Fin n) ℤ)
    (w : (Fin n → ℝ) → ℝ) (hw0 : w 0=0) (P q W : ℕ)
    (Ω : Set (Fin n → ZMod W)) (θ : ℝ) (x : Fin n → ℤ) :
    coefficient G q W Ω x*sampledPhase G w P θ x =
      ∑ a : Fin q, if Nat.Coprime a.val q then
        (countingWeight w P W Ω x:ℂ)*
          realExponential (((a.val:ℝ)/(q:ℝ)+θ)*(eval x G:ℝ)) else 0 := by
  unfold coefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : Nat.Coprime a.val q
  · rw [if_pos ha,if_pos ha]
    by_cases hx : x=0
    · subst x
      simp [sampledPhase,countingWeight,hw0]
    · by_cases hΩ : integerResidue W x ∈ Ω
      · simp only [if_pos hΩ,countingWeight,ne_eq,hx,not_false_eq_true,
          true_and,hΩ,if_true,sampledPhase,realExponential_arc_phase]
        ring
      · simp [hΩ,countingWeight,hx]
  · simp [ha]

/-- The complete lattice series has finite support; no totalized
divergent sum is used to identify the actual generating function. -/
theorem hasSum (G : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ)
    (A P : ℕ) (hw : WeightSupportedInBox w A) (hw0 : w 0=0) (hP : 0 < P)
    (q W : ℕ) (Ω : Set (Fin n → ZMod W)) (θ : ℝ) :
    HasSum (fun x : Fin n → ℤ => coefficient G q W Ω x*sampledPhase G w P θ x)
      (∑ a : Fin q, if Nat.Coprime a.val q then
        localizedGeneratingSum G w A P W Ω ((a.val:ℝ)/(q:ℝ)+θ) else 0) := by
  have hz (x : Fin n → ℤ) (hx : x ∉ integerBox n (A*P)) :
      coefficient G q W Ω x*sampledPhase G w P θ x=0 := by
    have hwx : w (scaledIntegerPoint P x)=0 := by
      by_contra h
      exact hx (scaled_weight_support w hw hP x h)
    simp [sampledPhase,hwx]
  have he : (∑ x ∈ integerBox n (A*P), coefficient G q W Ω x*sampledPhase G w P θ x) =
      ∑ a : Fin q, if Nat.Coprime a.val q then
        localizedGeneratingSum G w A P W Ω ((a.val:ℝ)/(q:ℝ)+θ) else 0 := by
    simp_rw [coefficient_phase_eq G w hw0 P q W Ω θ]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : Nat.Coprime a.val q
    · simp only [if_pos ha]
      rfl
    · simp [ha]
  rw [← he]
  exact hasSum_sum_of_ne_finset_zero hz

end CubicTenVariables.LocalizedGeneratingFunction
