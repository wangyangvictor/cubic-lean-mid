import CubicTenVariables.SmoothResidueLifting

/-!
# Exact iteration above a fixed smooth prime-field zero

At each step, partition the actual global residue-class zero filter by its
literal reduction to the preceding modulus. Smoothness modulo p is inherited
from the fixed base point. The one-step finite count therefore iterates with
no Hensel lemma, p-adic existence theorem, or quotient-descent assumption.
-/

noncomputable section
namespace CubicTenVariables.SmoothResidueIteration

open MvPolynomial SmoothResidueLifting PrimePowerFibers
open scoped BigOperators

variable {n : ℕ}

/-- Literal reduction from p^a to p, defined when a≥1. -/
def toPrime (p a : ℕ) (ha : 1 ≤ a) : ZMod (p ^ a) →+* ZMod p :=
  ZMod.castHom (by simpa only [pow_one] using pow_dvd_pow p ha) (ZMod p)

def primeLift (p : ℕ) : ZMod p →+* ZMod (p ^ 1) :=
  ZMod.castHom (by simp only [pow_one, dvd_refl]) (ZMod (p ^ 1))

@[simp] theorem primeLift_toPrime (p : ℕ) (z : ZMod (p ^ 1)) :
    primeLift p (toPrime p 1 le_rfl z) = z := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
  simp only [map_intCast]

@[simp] theorem toPrime_primeLift (p : ℕ) (z : ZMod p) :
    toPrime p 1 le_rfl (primeLift p z) = z := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
  simp only [map_intCast]

theorem toPrime_step (p a : ℕ) (ha : 1 ≤ a) (z : ZMod (p ^ (a + 1))) :
    toPrime p a ha (reduction p (Nat.le_succ a) z) =
      toPrime p (a + 1) (by omega) z := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
  simp only [map_intCast]

theorem toPrime_val (p a : ℕ) [NeZero p] (ha : 1 ≤ a) (z : ZMod (p ^ a)) :
    toPrime p a ha z = (z.val : ZMod p) := by
  have h := map_natCast (toPrime p a ha) z.val
  rwa [ZMod.natCast_zmod_val] at h

theorem map_eval₂_int {q r : ℕ} (f : ZMod q →+* ZMod r)
    (F : MvPolynomial (Fin n) ℤ) (z : Fin n → ZMod q) :
    f (eval₂ (Int.castRingHom (ZMod q)) z F) =
      eval₂ (Int.castRingHom (ZMod r)) (fun i => f (z i)) F := by
  have hc : f.comp (Int.castRingHom (ZMod q)) = Int.castRingHom (ZMod r) := by
    ext k
    simp
  simpa only [hc, Function.comp_def] using
    eval₂_comp_left f (Int.castRingHom (ZMod q)) z F

/-- All actual zero classes at level p^a whose prime reduction is the fixed base. -/
def zeroLifts (p : ℕ) [Fact p.Prime] (a : ℕ) (ha : 1 ≤ a)
    (F : MvPolynomial (Fin n) ℤ) (y : Fin n → ZMod p) :
    Finset (Fin n → ZMod (p ^ a)) :=
  Finset.univ.filter fun z => (∀ i, toPrime p a ha (z i) = y i) ∧
    eval₂ (Int.castRingHom (ZMod (p ^ a))) z F = 0

@[simp] theorem mem_zeroLifts (p : ℕ) [Fact p.Prime] (a : ℕ) (ha : 1 ≤ a)
    (F : MvPolynomial (Fin n) ℤ) (y : Fin n → ZMod p) (z : Fin n → ZMod (p ^ a)) :
    z ∈ zeroLifts p a ha F y ↔
      (∀ i, toPrime p a ha (z i) = y i) ∧
      eval₂ (Int.castRingHom (ZMod (p ^ a))) z F = 0 := by
  classical
  simp [zeroLifts]

/-- Actual one-step reduction preserves both the fixed base class and the zero equation. -/
theorem reduction_mem_zeroLifts (p : ℕ) [Fact p.Prime] (a : ℕ) (ha : 1 ≤ a)
    (F : MvPolynomial (Fin n) ℤ) (y : Fin n → ZMod p)
    (z : Fin n → ZMod (p ^ (a + 1))) (hz : z ∈ zeroLifts p (a + 1) (by omega) F y) :
    (fun i => reduction p (Nat.le_succ a) (z i)) ∈ zeroLifts p a ha F y := by
  rw [mem_zeroLifts] at hz ⊢
  refine ⟨fun i => (toPrime_step p a ha (z i)).trans (hz.1 i), ?_⟩
  rw [← map_eval₂_int, hz.2, map_zero]

/-- Canonical integer representatives of an actual zero satisfy the integral congruence. -/
theorem canonical_zero_divisibility (p a : ℕ) [NeZero p]
    (F : MvPolynomial (Fin n) ℤ) (z : Fin n → ZMod (p ^ a))
    (hz : eval₂ (Int.castRingHom (ZMod (p ^ a))) z F = 0) :
    ((p ^ a : ℕ) : ℤ) ∣ eval (fun i => ((z i).val : ℤ)) F := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ a)).mp
  rw [cast_eval_int]
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hz

/-- Prime-field smoothness is retained by every point above the fixed base. -/
theorem canonical_gradient_nonzero (p : ℕ) [Fact p.Prime] (a : ℕ) (ha : 1 ≤ a)
    (F : MvPolynomial (Fin n) ℤ) (y : Fin n → ZMod p)
    (hg : ∃ i, eval₂ (Int.castRingHom (ZMod p)) y (pderiv i F) ≠ 0)
    (z : Fin n → ZMod (p ^ a)) (hz : ∀ i, toPrime p a ha (z i) = y i) :
    ∃ i, ((eval (fun j => ((z j).val : ℤ)) (pderiv i F) : ℤ) : ZMod p) ≠ 0 := by
  obtain ⟨i, hi⟩ := hg
  refine ⟨i, ?_⟩
  have hcoords : (fun j => (((z j).val : ℤ) : ZMod p)) = y := by
    funext j
    simpa only [Int.cast_natCast] using (toPrime_val p a ha (z j)).symm.trans (hz j)
  rwa [cast_eval_int, hcoords]

/-- Every actual preceding root has exactly the one-step number of preimages
inside the global zero filter above the fixed smooth base. -/
theorem card_step_fiber (p : ℕ) [Fact p.Prime] (a : ℕ) (ha : 1 ≤ a)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3) (y : Fin n → ZMod p)
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
  have h := card_smooth_zero_lifts_one_step p a ha F hF
    (fun i => ((z i).val : ℤ)) (canonical_zero_divisibility p a F z hz'.2)
    (canonical_gradient_nonzero p a ha F y hg z hz'.1)
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using h

/-- The exact count recurrence is obtained by partitioning full residue tuples. -/
theorem card_zeroLifts_succ (p : ℕ) [Fact p.Prime] (a : ℕ) (ha : 1 ≤ a)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3) (y : Fin n → ZMod p)
    (hg : ∃ i, eval₂ (Int.castRingHom (ZMod p)) y (pderiv i F) ≠ 0) :
    (zeroLifts p (a + 1) (by omega) F y).card =
      (zeroLifts p a ha F y).card * p ^ (n - 1) := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (fun x hx => reduction_mem_zeroLifts p a ha F y x hx)]
  rw [Finset.sum_congr rfl (fun z hz => card_step_fiber p a ha F hF y hg z hz)]
  simp

/-- The level-one filter consists exactly of the supplied base zero. -/
theorem zeroLifts_one (p : ℕ) [Fact p.Prime]
    (F : MvPolynomial (Fin n) ℤ) (y : Fin n → ZMod p)
    (hy : eval₂ (Int.castRingHom (ZMod p)) y F = 0) :
    zeroLifts p 1 le_rfl F y = {fun i => primeLift p (y i)} := by
  classical
  ext z
  simp only [mem_zeroLifts, Finset.mem_singleton]
  constructor
  · intro h
    funext i
    rw [← h.1 i, primeLift_toPrime]
  · intro h
    subst z
    refine ⟨fun i => toPrime_primeLift p (y i), ?_⟩
    rw [← map_eval₂_int, hy, map_zero]

/-- A fixed smooth prime-field zero has exactly p^((a-1)(n-1)) actual zero
lifts at every level a≥1, with the literal reduction condition retained. -/
theorem card_smooth_zero_lifts (p : ℕ) [Fact p.Prime]
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3) (y : Fin n → ZMod p)
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
      rw [card_zeroLifts_succ p (k + 1) (by omega) F hF y hg, ih, ← pow_add]
      congr 1
      simp only [Nat.succ_mul]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  simpa only [Nat.succ_sub_one] using hcount k

/-- The all-level count displayed directly as the actual global finite filter. -/
theorem card_smooth_zero_filter (p : ℕ) [Fact p.Prime]
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3) (y : Fin n → ZMod p)
    (hy : eval₂ (Int.castRingHom (ZMod p)) y F = 0)
    (hg : ∃ i, eval₂ (Int.castRingHom (ZMod p)) y (pderiv i F) ≠ 0)
    (a : ℕ) (ha : 1 ≤ a) :
    (Finset.univ.filter fun z : Fin n → ZMod (p ^ a) =>
      (∀ i, toPrime p a ha (z i) = y i) ∧
        eval₂ (Int.castRingHom (ZMod (p ^ a))) z F = 0).card =
      p ^ ((a - 1) * (n - 1)) :=
  card_smooth_zero_lifts p F hF y hy hg a ha

/-- The same literal global count from any integer representative of the smooth
base zero, including negative and noncanonical representatives. -/
theorem card_smooth_integer_zero_lifts (p : ℕ) [Fact p.Prime]
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3) (y : Fin n → ℤ)
    (hy : (p : ℤ) ∣ eval y F)
    (hg : ∃ i, ((eval y (pderiv i F) : ℤ) : ZMod p) ≠ 0)
    (a : ℕ) (ha : 1 ≤ a) :
    (Finset.univ.filter fun z : Fin n → ZMod (p ^ a) =>
      (∀ i, toPrime p a ha (z i) = (y i : ZMod p)) ∧
        eval₂ (Int.castRingHom (ZMod (p ^ a))) z F = 0).card =
      p ^ ((a - 1) * (n - 1)) := by
  apply card_smooth_zero_filter p F hF (fun i => (y i : ZMod p))
  · rw [← cast_eval_int, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hy
  · simpa only [cast_eval_int] using hg

end CubicTenVariables.SmoothResidueIteration
