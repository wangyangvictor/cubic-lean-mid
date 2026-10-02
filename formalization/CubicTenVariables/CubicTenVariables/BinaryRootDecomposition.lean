import CubicTenVariables.BinaryPrimeZeroCount

/-!
# Partitioning the actual binary root count by prime residue classes

The functions here count literal roots in the indicated residue rings. The
final lemma separates the proved smooth contribution from an explicitly
supplied bound on the singular contribution; it is an assembly lemma, not
the completed root-count theorem.
-/

noncomputable section
namespace CubicTenVariables.BinaryCubicPerturbation
open scoped BigOperators
open SmoothResidueIteration

def rootCount (G : Coefficients) (p : ℕ) [Fact p.Prime] (s : ℕ) : ℕ :=
  (Finset.univ.filter fun z : Fin 2 → ZMod (p^s) =>
    value G (p : ZMod (p^s)) (z 0) (z 1) = 0).card

def liftCount (G : Coefficients) (p : ℕ) [Fact p.Prime]
    (s : ℕ) (hs : 1 ≤ s) (v : Fin 2 → ZMod p) : ℕ :=
  (Finset.univ.filter fun z : Fin 2 → ZMod (p^s) =>
    (∀ i, toPrime p s hs (z i) = v i) ∧
      value G (p : ZMod (p^s)) (z 0) (z 1) = 0).card

/-- Canonical integer representatives of a critical prime-field point have
both actual integral derivatives divisible by the prime. -/
theorem canonical_center_critical (G : Coefficients) (p : ℕ) [Fact p.Prime]
    (v : Fin 2 → ZMod p) (hx : dx G 0 (v 0) (v 1) = 0)
    (hy : dy G 0 (v 0) (v 1) = 0) :
    (p : ℤ) ∣ dx G (p : ℤ) ((v 0).val : ℤ) ((v 1).val : ℤ) ∧
      (p : ℤ) ∣ dy G (p : ℤ) ((v 0).val : ℤ) ((v 1).val : ℤ) := by
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    simpa [dx] using hx
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    simpa [dy] using hy

@[simp] theorem rootCount_zero (G : Coefficients) (p : ℕ) [Fact p.Prime] :
    rootCount G p 0 = 1 := by
  classical
  letI : Subsingleton (ZMod (p^0)) := by rw [pow_zero]; infer_instance
  have hz (z : Fin 2 → ZMod (p^0)) :
      value G (p : ZMod (p^0)) (z 0) (z 1) = 0 := Subsingleton.elim _ _
  simp [rootCount, hz]

theorem toPrime_value (G : Coefficients) (p s : ℕ) (hs : 1 ≤ s)
    (z : Fin 2 → ZMod (p^s)) :
    toPrime p s hs (value G (p : ZMod (p^s)) (z 0) (z 1)) =
      value G 0 (toPrime p s hs (z 0)) (toPrime p s hs (z 1)) := by
  simp only [value, map_add, map_mul, map_intCast, map_pow, map_natCast,
    ZMod.natCast_self]

theorem rootCount_one_le (G : Coefficients) (p : ℕ) [Fact p.Prime]
    (hD : (discriminant G : ZMod p) ≠ 0) :
    rootCount G p 1 ≤ 2*p := by
  classical
  apply le_trans _ (card_prime_zeros_le_two_mul G p hD)
  unfold rootCount
  apply Finset.card_le_card_of_injOn (fun z i => toPrime p 1 le_rfl (z i))
  · intro z hz
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    rw [← toPrime_value, hz, map_zero]
  · intro x hx y hy hxy
    funext i
    have h := congrArg (primeLift p) (congrFun hxy i)
    simpa only [primeLift_toPrime] using h

/-- Partition the full root filter using literal prime reduction. -/
theorem rootCount_eq_sum_liftCount (G : Coefficients) (p : ℕ) [Fact p.Prime]
    (s : ℕ) (hs : 1 ≤ s) :
    rootCount G p s =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 2 → ZMod p =>
        value G 0 (v 0) (v 1) = 0), liftCount G p s hs v := by
  classical
  let S := Finset.univ.filter (fun z : Fin 2 → ZMod (p^s) =>
    value G (p : ZMod (p^s)) (z 0) (z 1) = 0)
  let T := Finset.univ.filter (fun v : Fin 2 → ZMod p =>
    value G 0 (v 0) (v 1) = 0)
  have hmap : ∀ z ∈ S, (fun i => toPrime p s hs (z i)) ∈ T := by
    intro z hz
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← toPrime_value, hz, map_zero]
  change S.card = ∑ v ∈ T, liftCount G p s hs v
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro v hv
  unfold liftCount
  congr 1
  ext z
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, funext_iff]
  exact and_comm

/-- With a bound `B` for each singular class, the actual smooth contribution
and uniqueness of the critical point give `2*p^s+B`. -/
theorem rootCount_le_smooth_add_singular (G : Coefficients) (p : ℕ) [Fact p.Prime]
    (hD : (discriminant G : ZMod p) ≠ 0) (s : ℕ) (hs : 1 ≤ s) (B : ℕ)
    (hB : ∀ v : Fin 2 → ZMod p, value G 0 (v 0) (v 1) = 0 →
      dx G 0 (v 0) (v 1) = 0 → dy G 0 (v 0) (v 1) = 0 →
      liftCount G p s hs v ≤ B) :
    rootCount G p s ≤ 2*p^s+B := by
  classical
  let T := Finset.univ.filter (fun v : Fin 2 → ZMod p =>
    value G 0 (v 0) (v 1) = 0)
  let critical := fun v : Fin 2 → ZMod p =>
    dx G 0 (v 0) (v 1) = 0 ∧ dy G 0 (v 0) (v 1) = 0
  have hpoint (v) (hv : v ∈ T) :
      liftCount G p s hs v ≤ p^(s-1) + if critical v then B else 0 := by
    have hv0 : value G 0 (v 0) (v 1) = 0 := (Finset.mem_filter.mp hv).2
    by_cases hc : critical v
    · simpa only [if_pos hc] using
        (hB v hv0 hc.1 hc.2).trans (Nat.le_add_left _ _)
    · have hg : dx G 0 (v 0) (v 1) ≠ 0 ∨ dy G 0 (v 0) (v 1) ≠ 0 := by
        simpa only [critical, not_and_or] using hc
      have h := card_smooth_binary_lifts G p s hs v hv0 hg
      simpa only [liftCount, h, if_neg hc, add_zero] using (le_refl (p^(s-1)))
  have hcrit : (T.filter critical).card ≤ 1 := by
    have heq : T.filter critical = Finset.univ.filter (fun v : Fin 2 → ZMod p =>
        value G 0 (v 0) (v 1) = 0 ∧ dx G 0 (v 0) (v 1) = 0 ∧
          dy G 0 (v 0) (v 1) = 0) := by
      ext v
      simp only [T, critical, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [heq]
    exact card_singular_prime_zeros_le_one G p hD
  have hsum : (∑ v ∈ T, if critical v then B else 0) = (T.filter critical).card*B := by
    rw [← Finset.sum_filter]
    simp
  calc
    rootCount G p s = ∑ v ∈ T, liftCount G p s hs v :=
      rootCount_eq_sum_liftCount G p s hs
    _ ≤ ∑ v ∈ T, (p^(s-1) + if critical v then B else 0) :=
      Finset.sum_le_sum hpoint
    _ = T.card*p^(s-1) + (T.filter critical).card*B := by
      rw [Finset.sum_add_distrib, hsum]
      simp
    _ ≤ (2*p)*p^(s-1) + 1*B := Nat.add_le_add
      (Nat.mul_le_mul_right _ (card_prime_zeros_le_two_mul G p hD))
      (Nat.mul_le_mul_right _ hcrit)
    _ = 2*p^s+B := by
      rw [one_mul, mul_assoc, ← pow_succ', Nat.sub_add_cancel hs]

end CubicTenVariables.BinaryCubicPerturbation
