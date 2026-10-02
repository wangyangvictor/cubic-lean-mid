import CubicTenVariables.DeltaMethod
import CubicTenVariables.IntegerLatticeResidues

/-! Exact canonical-numerator adapters for the actual localized generating
function and its delta-method arc integrals. The exchanged endpoints are
proved equal from the integer polynomial phase. The modulus-one term is
retained. These identities require no literature input or convergence
assumption, since only finite sums are reindexed. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.LocalizedGeneratingNumerators
open MvPolynomial MeasureTheory DeltaMethod
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

/-- The q-th integer numerator has trivial character, including q=1. -/
theorem realExponential_numerator_endpoint (q : ℕ) (hq : 0 < q)
    (θ : ℝ) (m : ℤ) :
    realExponential (((q : ℝ)/(q : ℝ)+θ)*(m : ℝ)) =
      realExponential (((0 : ℝ)/(q : ℝ)+θ)*(m : ℝ)) := by
  letI : NeZero q := ⟨hq.ne'⟩
  rw [realExponential_arc_phase q q θ m,
    PrimeSumAdapter.residueExponential_eq_stdAddChar]
  simp

/-- Endpoint equality for the literal finite localized generating function.
The counting weight retains both the congruence and origin restrictions. -/
theorem numerator_endpoint (G : MvPolynomial (Fin n) ℤ)
    (w : (Fin n → ℝ) → ℝ) (A P q W : ℕ) (hq : 0 < q)
    (Ω : Set (Fin n → ZMod W)) (θ : ℝ) :
    localizedGeneratingSum G w A P W Ω ((q : ℝ)/(q : ℝ)+θ) =
      localizedGeneratingSum G w A P W Ω ((0 : ℝ)/(q : ℝ)+θ) := by
  unfold localizedGeneratingSum finiteExponentialSum
  apply Finset.sum_congr rfl
  intro x _
  rw [realExponential_numerator_endpoint q hq]

/-- Replace the source interval 1,...,q by the canonical representatives
0,...,q-1 without losing the modulus-one numerator. -/
theorem sum_Icc_eq_sum_fin (G : MvPolynomial (Fin n) ℤ)
    (w : (Fin n → ℝ) → ℝ) (A P q W : ℕ) (hq : 0 < q)
    (Ω : Set (Fin n → ZMod W)) (θ : ℝ) :
    (∑ a ∈ Finset.Icc 1 q, if Nat.Coprime a q then
      localizedGeneratingSum G w A P W Ω ((a : ℝ)/(q : ℝ)+θ) else 0) =
    ∑ a : Fin q, if Nat.Coprime a.val q then
      localizedGeneratingSum G w A P W Ω ((a.val : ℝ)/(q : ℝ)+θ) else 0 :=
  IntegerLatticeResidues.sum_Icc_coprime_eq_sum_fin q hq
    (fun a => localizedGeneratingSum G w A P W Ω ((a : ℝ)/(q : ℝ)+θ))
    (by simpa only [Nat.cast_zero] using numerator_endpoint G w A P q W hq Ω θ)

/-- The same replacement for each weighted phase integral. The domain and
kernel are arbitrary and independent of the numerator. -/
theorem sum_Icc_integrals_eq_sum_fin (G : MvPolynomial (Fin n) ℤ)
    (w : (Fin n → ℝ) → ℝ) (A P q W : ℕ) (hq : 0 < q)
    (Ω : Set (Fin n → ZMod W)) (S : Set ℝ) (k : ℝ → ℂ) :
    (∑ a ∈ Finset.Icc 1 q, if Nat.Coprime a q then
      ∫ θ in S, k θ * localizedGeneratingSum G w A P W Ω
        ((a : ℝ)/(q : ℝ)+θ) else 0) =
    ∑ a : Fin q, if Nat.Coprime a.val q then
      ∫ θ in S, k θ * localizedGeneratingSum G w A P W Ω
        ((a.val : ℝ)/(q : ℝ)+θ) else 0 := by
  apply IntegerLatticeResidues.sum_Icc_coprime_eq_sum_fin q hq
  apply integral_congr_ae
  filter_upwards [] with θ
  simp only [Nat.cast_zero]
  rw [numerator_endpoint G w A P q W hq Ω θ]

/-- Exact rewrite of the complete numerator/modulus expression appearing in
the existing localized delta-method count approximation. -/
theorem arcSum_Icc_eq_sum_fin (G : MvPolynomial (Fin n) ℤ)
    (w : (Fin n → ℝ) → ℝ) (A P Q W : ℕ)
    (Ω : Set (Fin n → ZMod W)) (η : ℝ) (p : ℕ → ℕ → ℝ → ℂ) :
    (∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ Finset.Icc 1 q, if Nat.Coprime a q then
      ∫ θ in arc Q q η, p Q q θ * localizedGeneratingSum G w A P W Ω
        ((a : ℝ)/(q : ℝ)+θ) else 0) =
    ∑ q ∈ Finset.Icc 1 Q, ∑ a : Fin q, if Nat.Coprime a.val q then
      ∫ θ in arc Q q η, p Q q θ * localizedGeneratingSum G w A P W Ω
        ((a.val : ℝ)/(q : ℝ)+θ) else 0 := by
  apply Finset.sum_congr rfl
  intro q hq
  exact sum_Icc_integrals_eq_sum_fin G w A P q W (Finset.mem_Icc.mp hq).1 Ω
    (arc Q q η) (p Q q)

/-- At q=1 the surviving canonical numerator is zero and the contribution
is the original generating function at θ, rather than an empty sum. -/
theorem sum_Icc_one (G : MvPolynomial (Fin n) ℤ)
    (w : (Fin n → ℝ) → ℝ) (A P W : ℕ)
    (Ω : Set (Fin n → ZMod W)) (θ : ℝ) :
    (∑ a ∈ Finset.Icc 1 1, if Nat.Coprime a 1 then
      localizedGeneratingSum G w A P W Ω ((a : ℝ)/(1 : ℝ)+θ) else 0) =
      localizedGeneratingSum G w A P W Ω θ := by
  simpa using sum_Icc_eq_sum_fin G w A P 1 W (by decide) Ω θ

end CubicTenVariables.LocalizedGeneratingNumerators
