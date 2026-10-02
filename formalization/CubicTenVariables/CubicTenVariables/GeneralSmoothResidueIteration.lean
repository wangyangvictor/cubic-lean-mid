import CubicTenVariables.GeneralSmoothResidueLifting
import CubicTenVariables.SmoothResidueIteration

/-! Iterated exact root counts above a fixed smooth prime-field zero for
arbitrary integral polynomials. We use the existing actual reduction maps
and zeroLifts filter; only the one-step input is generalized. -/
noncomputable section
namespace CubicTenVariables.GeneralSmoothResidueIteration
open MvPolynomial SmoothResidueLifting SmoothResidueIteration PrimePowerFibers
open scoped BigOperators
variable {n : ℕ}

/-- Every actual preceding root has exactly the one-step number of preimages
inside the global zero filter above the fixed smooth base. -/
theorem card_step_fiber (p : ℕ) [Fact p.Prime] (a : ℕ) (ha : 1 ≤ a)
    (F : MvPolynomial (Fin n) ℤ) (y : Fin n → ZMod p)
    (hg : ∃ i, eval₂ (Int.castRingHom (ZMod p)) y (pderiv i F) ≠ 0)
    (z : Fin n → ZMod (p ^ a)) (hz : z ∈ zeroLifts p a ha F y) :
    ((zeroLifts p (a + 1) (by omega) F y).filter fun x =>
      (fun i => reduction p (Nat.le_succ a) (x i)) = z).card = p ^ (n - 1) := by
  classical
  have hz' := (mem_zeroLifts p a ha F y z).mp hz
  have heq : (zeroLifts p (a + 1) (by omega) F y).filter (fun x =>
        (fun i => reduction p (Nat.le_succ a) (x i)) = z) =
      Finset.univ.filter (fun x : Fin n → ZMod (p ^ (a + 1)) =>
        (∀ i, reduction p (Nat.le_succ a) (x i) = z i) ∧
          eval₂ (Int.castRingHom (ZMod (p ^ (a + 1)))) x F = 0) := by
    ext x
    simp only [Finset.mem_filter, mem_zeroLifts, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨_, hx0⟩, hred⟩
      exact ⟨fun i => congrFun hred i, hx0⟩
    · rintro ⟨hred, hx0⟩
      refine ⟨⟨fun i => ?_, hx0⟩, funext hred⟩
      rw [← toPrime_step p a ha, hred i]
      exact hz'.1 i
  rw [heq]
  have h := GeneralSmoothResidueLifting.card_smooth_zero_lifts_one_step p a ha F
    (fun i => ((z i).val : ℤ)) (canonical_zero_divisibility p a F z hz'.2)
    (canonical_gradient_nonzero p a ha F y hg z hz'.1)
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using h

/-- The exact count recurrence is obtained by partitioning full residue tuples. -/
theorem card_zeroLifts_succ (p : ℕ) [Fact p.Prime] (a : ℕ) (ha : 1 ≤ a)
    (F : MvPolynomial (Fin n) ℤ) (y : Fin n → ZMod p)
    (hg : ∃ i, eval₂ (Int.castRingHom (ZMod p)) y (pderiv i F) ≠ 0) :
    (zeroLifts p (a + 1) (by omega) F y).card =
      (zeroLifts p a ha F y).card * p ^ (n - 1) := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (fun x hx => reduction_mem_zeroLifts p a ha F y x hx)]
  rw [Finset.sum_congr rfl (fun z hz => card_step_fiber p a ha F y hg z hz)]
  simp

/-- A fixed smooth prime-field zero has exactly p^((a-1)(n-1)) actual zero
lifts at every level a≥1, with the literal reduction condition retained. -/
theorem card_smooth_zero_lifts (p : ℕ) [Fact p.Prime]
    (F : MvPolynomial (Fin n) ℤ) (y : Fin n → ZMod p)
    (hy : eval₂ (Int.castRingHom (ZMod p)) y F = 0)
    (hg : ∃ i, eval₂ (Int.castRingHom (ZMod p)) y (pderiv i F) ≠ 0)
    (a : ℕ) (ha : 1 ≤ a) :
    (zeroLifts p a ha F y).card = p ^ ((a - 1) * (n - 1)) := by
  have hcount (k : ℕ) : (zeroLifts p (k + 1) (by omega) F y).card =
      p ^ (k * (n - 1)) := by
    induction k with
    | zero => simp only [zeroLifts_one p F y hy, Finset.card_singleton,
        zero_mul, pow_zero]
    | succ k ih =>
      rw [card_zeroLifts_succ p (k + 1) (by omega) F y hg, ih, ← pow_add]
      congr 1
      simp only [Nat.succ_mul]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  simpa only [Nat.succ_sub_one] using hcount k

/-- The all-level count displayed directly as the actual global finite filter. -/
theorem card_smooth_zero_filter (p : ℕ) [Fact p.Prime]
    (F : MvPolynomial (Fin n) ℤ) (y : Fin n → ZMod p)
    (hy : eval₂ (Int.castRingHom (ZMod p)) y F = 0)
    (hg : ∃ i, eval₂ (Int.castRingHom (ZMod p)) y (pderiv i F) ≠ 0)
    (a : ℕ) (ha : 1 ≤ a) :
    (Finset.univ.filter fun z : Fin n → ZMod (p ^ a) =>
      (∀ i, toPrime p a ha (z i) = y i) ∧
        eval₂ (Int.castRingHom (ZMod (p ^ a))) z F = 0).card =
      p ^ ((a - 1) * (n - 1)) :=
  card_smooth_zero_lifts p F y hy hg a ha

/-- The same literal global count from any integer representative of the smooth
base zero, including negative and noncanonical representatives. -/
theorem card_smooth_integer_zero_lifts (p : ℕ) [Fact p.Prime]
    (F : MvPolynomial (Fin n) ℤ) (y : Fin n → ℤ)
    (hy : (p : ℤ) ∣ eval y F)
    (hg : ∃ i, ((eval y (pderiv i F) : ℤ) : ZMod p) ≠ 0)
    (a : ℕ) (ha : 1 ≤ a) :
    (Finset.univ.filter fun z : Fin n → ZMod (p ^ a) =>
      (∀ i, toPrime p a ha (z i) = (y i : ZMod p)) ∧
        eval₂ (Int.castRingHom (ZMod (p ^ a))) z F = 0).card =
      p ^ ((a - 1) * (n - 1)) := by
  apply card_smooth_zero_filter p F (fun i => (y i : ZMod p))
  · rw [← cast_eval_int, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hy
  · simpa only [cast_eval_int] using hg


end CubicTenVariables.GeneralSmoothResidueIteration
