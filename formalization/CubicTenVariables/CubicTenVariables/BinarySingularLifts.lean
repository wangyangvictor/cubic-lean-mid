import CubicTenVariables.BinaryCubicPerturbation

/-!
# Exact singular-class lifting for a binary cubic perturbation

The literal prime-reduction fiber is parametrized by its remaining digits.
At a critical integer center, division by p² identifies its zero equation
with the actual rescaled polynomial. The last two free digits account for
p², including when the remaining modulus is one.
-/

noncomputable section
namespace CubicTenVariables.BinarySingularLifts

open BinaryCubicPerturbation PrimePowerFibers SmoothResidueIteration
open scoped BigOperators

/-- Cancellation of an integral power of p in an actual residue equation. -/
theorem power_mul_cast_eq_zero_iff (p k t : ℕ) [NeZero p] (z : ℤ) :
    ((((p ^ t : ℕ) : ℤ) * z : ℤ) : ZMod (p ^ (k + t))) = 0 ↔
      (z : ZMod (p ^ k)) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd,
    pow_add, Nat.cast_mul, mul_comm ((p ^ k : ℕ) : ℤ), mul_dvd_mul_iff_left]
  exact_mod_cast pow_ne_zero t (NeZero.ne p)

/-- The fixed low digit is represented by an arbitrary integer center. -/
def lowDigitLift (p k : ℕ) {n : ℕ} (y : Fin n → ℤ)
    (x : Fin n → ZMod (p ^ k)) : Fin n → ZMod (p ^ (k + 1)) :=
  fun i => ((y i + (p : ℤ) * (x i).val : ℤ) : ZMod (p ^ (k + 1)))

@[simp] theorem toPrime_lowDigitLift (p k : ℕ) {n : ℕ} (y : Fin n → ℤ)
    (x : Fin n → ZMod (p ^ k)) (i : Fin n) :
    toPrime p (k + 1) (by omega) (lowDigitLift p k y x i) = (y i : ZMod p) := by
  simp [lowDigitLift]

theorem lowDigitLift_injective (p k : ℕ) [NeZero p] {n : ℕ}
    (y : Fin n → ℤ) : Function.Injective (lowDigitLift p k y) := by
  intro x x' h
  funext i
  have hi := congrFun h i
  have hz : ((((p ^ 1 : ℕ) : ℤ) * ((x i).val - (x' i).val) : ℤ) :
      ZMod (p ^ (k + 1))) = 0 := by
    simp only [lowDigitLift, Int.cast_add, Int.cast_mul, Int.cast_sub,
      Int.cast_natCast, pow_one] at hi ⊢
    linear_combination hi
  have hsmall := (power_mul_cast_eq_zero_iff p k 1 _).mp hz
  simpa only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val,
    sub_eq_zero] using hsmall

theorem card_toPrime_fiber (p k : ℕ) [Fact p.Prime] (b : ZMod p) :
    Nat.card {z : ZMod (p ^ (k + 1)) // toPrime p (k + 1) (by omega) z = b} = p ^ k := by
  have hf : Function.Surjective (toPrime p (k + 1) (by omega)) := by
    intro z
    obtain ⟨a, rfl⟩ := ZMod.intCast_surjective z
    exact ⟨(a : ZMod (p ^ (k + 1))), map_intCast _ a⟩
  have hc := card_fiber_mul_card_of_surjective
    (toPrime p (k + 1) (by omega)).toAddMonoidHom hf b
  apply Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos
  simpa only [Nat.card_zmod, pow_succ] using hc

/-- All and only the actual residue classes with this fixed low digit. -/
def lowDigitLiftEquiv (p k : ℕ) [Fact p.Prime] {n : ℕ} (y : Fin n → ℤ) :
    (Fin n → ZMod (p ^ k)) ≃ {z : Fin n → ZMod (p ^ (k + 1)) //
      ∀ i, toPrime p (k + 1) (by omega) (z i) = (y i : ZMod p)} := by
  classical
  let f : (Fin n → ZMod (p ^ k)) → {z : Fin n → ZMod (p ^ (k + 1)) //
      ∀ i, toPrime p (k + 1) (by omega) (z i) = (y i : ZMod p)} :=
    fun x => ⟨lowDigitLift p k y x, toPrime_lowDigitLift p k y x⟩
  apply Equiv.ofBijective f
  apply (Fintype.bijective_iff_injective_and_card f).mpr
  refine ⟨fun x x' h => lowDigitLift_injective p k y (congrArg Subtype.val h), ?_⟩
  simp only [← Nat.card_eq_fintype_card]
  rw [Nat.card_congr (Equiv.subtypePiEquivPi
    (p := fun (i : Fin n) (z : ZMod (p ^ (k + 1))) =>
      toPrime p (k + 1) (by omega) z = (y i : ZMod p)))]
  simp only [Nat.card_pi, card_toPrime_fiber p k, Nat.card_zmod,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]


@[simp] theorem lowDigitLiftEquiv_apply (p k : ℕ) [Fact p.Prime] {n : ℕ}
    (y : Fin n → ℤ) (x : Fin n → ZMod (p ^ k)) :
    (lowDigitLiftEquiv p k y x).val = lowDigitLift p k y x := rfl

@[simp] theorem cast_value (G : Coefficients) (p x y : ℤ) (m : ℕ) :
    ((value G p x y : ℤ) : ZMod m) = value G (p : ZMod m) (x : ZMod m) (y : ZMod m) := by
  simp [value]

/-- The last digit of a pair contributes precisely p² to every lifted subset. -/
theorem card_reduction_preimage (p k : ℕ) [Fact p.Prime]
    (P : (Fin 2 → ZMod (p ^ k)) → Prop) [DecidablePred P] :
    (Finset.univ.filter fun x : Fin 2 → ZMod (p ^ (k + 1)) =>
      P (fun i => reduction p (Nat.le_succ k) (x i))).card =
      p ^ 2 * (Finset.univ.filter P).card := by
  classical
  let S := Finset.univ.filter fun x : Fin 2 → ZMod (p ^ (k + 1)) =>
    P (fun i => reduction p (Nat.le_succ k) (x i))
  let T := Finset.univ.filter P
  have hf : ∀ x ∈ S, (fun i => reduction p (Nat.le_succ k) (x i)) ∈ T := by
    simp only [S, T, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun _ h => h
  have hc (z : Fin 2 → ZMod (p ^ k)) (hz : z ∈ T) :
      (S.filter fun x => (fun i => reduction p (Nat.le_succ k) (x i)) = z).card =
        p ^ 2 := by
    have heq : S.filter (fun x => (fun i => reduction p (Nat.le_succ k) (x i)) = z) =
        Finset.univ.filter (fun x : Fin 2 → ZMod (p ^ (k + 1)) =>
          ∀ i, reduction p (Nat.le_succ k) (x i) = z i) := by
      ext x
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h i => congrFun h.2 i
      · intro h
        have hzP : P z := (Finset.mem_filter.mp hz).2
        exact ⟨by simpa only [funext h] using hzP, funext h⟩
    rw [heq, card_filter_vector_reduction_fiber]
    simp
  change S.card = p ^ 2 * T.card
  rw [Finset.card_eq_sum_card_fiberwise hf]
  rw [Finset.sum_congr rfl hc]
  simp [mul_comm]

/-- Reindex a literal prime fiber by all its remaining digits. -/
theorem card_lowDigit_filter (p k : ℕ) [Fact p.Prime] {n : ℕ} (y : Fin n → ℤ)
    (Q : (Fin n → ZMod (p ^ (k + 1))) → Prop) [DecidablePred Q] :
    (Finset.univ.filter fun z : Fin n → ZMod (p ^ (k + 1)) =>
      (∀ i, toPrime p (k + 1) (by omega) (z i) = (y i : ZMod p)) ∧ Q z).card =
      (Finset.univ.filter fun x : Fin n → ZMod (p ^ k) => Q (lowDigitLift p k y x)).card := by
  classical
  let P : (Fin n → ZMod (p ^ (k + 1))) → Prop := fun z =>
    ∀ i, toPrime p (k + 1) (by omega) (z i) = (y i : ZMod p)
  let e := (lowDigitLiftEquiv p k y).subtypeEquiv
    (p := fun x => Q (lowDigitLift p k y x)) (q := fun z => Q z.val) (fun _ => Iff.rfl)
  have hc := Nat.card_congr (e.trans (Equiv.subtypeSubtypeEquivSubtypeInter P Q))
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, P] using hc.symm

theorem value_lowDigitLift (G : Coefficients) (p k : ℕ) (a b : ℤ)
    (x : Fin 2 → ZMod (p ^ (k + 1))) :
    value G (p : ZMod (p ^ (k + 2)))
      (lowDigitLift p (k + 1) ![a,b] x 0) (lowDigitLift p (k + 1) ![a,b] x 1) =
      ((value G (p : ℤ) (a + p * (x 0).val) (b + p * (x 1).val) : ℤ) : ZMod (p ^ (k + 2))) := by
  rw [cast_value]
  simp only [Int.cast_natCast]
  rfl

/-- Literal root equivalence after division by p², before counting. -/
theorem zero_lowDigitLift_iff (G : Coefficients) (p k : ℕ) [Fact p.Prime]
    (a b : ℤ) (hx : (p : ℤ) ∣ dx G p a b) (hy : (p : ℤ) ∣ dy G p a b)
    (h0 : (p : ℤ) ^ 2 ∣ value G p a b) (x : Fin 2 → ZMod (p ^ (k + 1))) :
    value G (p : ZMod (p ^ (k + 2)))
      (lowDigitLift p (k + 1) ![a,b] x 0) (lowDigitLift p (k + 1) ![a,b] x 1) = 0 ↔
    value (rescale G p a b) (p : ZMod (p ^ k))
      (reduction p (Nat.le_succ k) (x 0)) (reduction p (Nat.le_succ k) (x 1)) = 0 := by
  rw [value_lowDigitLift, value_translate_rescale G (p : ℤ) a b h0 hx hy]
  rw [show (p : ℤ) ^ 2 = ((p ^ 2 : ℕ) : ℤ) by simp,
    power_mul_cast_eq_zero_iff, cast_value]
  have hv (i : Fin 2) : (((x i).val : ℤ) : ZMod (p ^ k)) =
      reduction p (Nat.le_succ k) (x i) := by
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using
      (map_natCast (reduction p (Nat.le_succ k)) (x i).val).symm
  rw [hv 0, hv 1, Int.cast_natCast]

/-- The integral derivative divisibilities are precisely the conditions
supplied by an actual critical point of the prime-field reduction. -/
theorem critical_divisibility (G : Coefficients) (p : ℕ) (a b : ℤ)
    (hx : dx G (0 : ZMod p) (a : ZMod p) (b : ZMod p) = 0)
    (hy : dy G (0 : ZMod p) (a : ZMod p) (b : ZMod p) = 0) :
    (p : ℤ) ∣ dx G p a b ∧ (p : ℤ) ∣ dy G p a b := by
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    simpa [dx] using hx
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    simpa [dy] using hy

/-- A critical class with nonzero p² obstruction has no literal roots. -/
theorem card_singular_binary_lifts_of_not_sq_dvd (G : Coefficients) (p s : ℕ)
    [Fact p.Prime] (hs : 2 ≤ s) (a b : ℤ)
    (hx : (p : ℤ) ∣ dx G p a b) (hy : (p : ℤ) ∣ dy G p a b)
    (h0 : ¬ (p : ℤ) ^ 2 ∣ value G p a b) :
    (Finset.univ.filter fun z : Fin 2 → ZMod (p ^ s) =>
      (∀ i, toPrime p s (by omega) (z i) = (![a,b] i : ZMod p)) ∧
      value G (p : ZMod (p ^ s)) (z 0) (z 1) = 0).card = 0 := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 2 := ⟨s - 2, by omega⟩
  rw [card_lowDigit_filter p (k + 1)]
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hroot
  have heq := (Finset.mem_filter.mp hroot).2
  rw [value_lowDigitLift, ZMod.intCast_zmod_eq_zero_iff_dvd] at heq
  have hp : (p : ℤ) ^ 2 ∣ ((p ^ (k + 2) : ℕ) : ℤ) := by
    exact_mod_cast pow_dvd_pow p (show 2 ≤ k + 2 by omega)
  exact h0 ((sq_dvd_value_translate_iff G (p : ℤ) a b hx hy _ _).mp (hp.trans heq))

/-- Exact singular-class recurrence for the actual polynomial and actual
prime reduction. It includes s=2, where the rescaled modulus is one. -/
theorem card_singular_binary_lifts_of_sq_dvd (G : Coefficients) (p s : ℕ)
    [Fact p.Prime] (hs : 2 ≤ s) (a b : ℤ)
    (hx : (p : ℤ) ∣ dx G p a b) (hy : (p : ℤ) ∣ dy G p a b)
    (h0 : (p : ℤ) ^ 2 ∣ value G p a b) :
    (Finset.univ.filter fun z : Fin 2 → ZMod (p ^ s) =>
      (∀ i, toPrime p s (by omega) (z i) = (![a,b] i : ZMod p)) ∧
      value G (p : ZMod (p ^ s)) (z 0) (z 1) = 0).card =
      p ^ 2 * (Finset.univ.filter fun z : Fin 2 → ZMod (p ^ (s - 2)) =>
        value (rescale G p a b) (p : ZMod (p ^ (s - 2))) (z 0) (z 1) = 0).card := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 2 := ⟨s - 2, by omega⟩
  rw [card_lowDigit_filter p (k + 1)]
  simp only [zero_lowDigitLift_iff G p k a b hx hy h0]
  exact card_reduction_preimage p k (fun z => value (rescale G p a b) (p : ZMod (p ^ k)) (z 0) (z 1) = 0)

end CubicTenVariables.BinarySingularLifts
