import CubicTenVariables.BinarySingularLifts
import CubicTenVariables.GeneralSmoothResidueLifting

/-!
# Exact singular-class lifting for actual multivariate polynomials

A supplied integral rescaling identity identifies the literal roots above
an integer center with roots of the actual rescaled polynomial. Counting
the free last digit in every coordinate gives p^n. Separately, the general
Taylor congruence proves that a critical center with nonzero obstruction
modulo p² has no lifts. Neither statement requires a degree bound.
-/

noncomputable section
namespace CubicTenVariables.PolynomialSingularLifts

open MvPolynomial PrimePowerFibers SmoothResidueIteration BinarySingularLifts
open scoped BigOperators
variable {n : ℕ}

/-- Every actual subset at a lower prime-power level has the exact number
of preimages dictated by the reduction fibers, in any dimension. -/
theorem card_reduction_preimage (p : ℕ) [Fact p.Prime] {s t : ℕ} (hts : t ≤ s)
    (P : (Fin n → ZMod (p ^ t)) → Prop) [DecidablePred P] :
    (Finset.univ.filter fun x : Fin n → ZMod (p ^ s) =>
      P (fun i => reduction p hts (x i))).card =
      p ^ ((s-t)*n) * (Finset.univ.filter P).card := by
  classical
  let S := Finset.univ.filter fun x : Fin n → ZMod (p ^ s) =>
    P (fun i => reduction p hts (x i))
  let T := Finset.univ.filter P
  have hf : ∀ x ∈ S, (fun i => reduction p hts (x i)) ∈ T := by
    simp only [S, T, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun _ h => h
  have hc (z : Fin n → ZMod (p ^ t)) (hz : z ∈ T) :
      (S.filter fun x => (fun i => reduction p hts (x i)) = z).card =
        p ^ ((s-t)*n) := by
    have heq : S.filter (fun x => (fun i => reduction p hts (x i)) = z) =
        Finset.univ.filter (fun x : Fin n → ZMod (p ^ s) =>
          ∀ i, reduction p hts (x i) = z i) := by
      ext x
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h i => congrFun h.2 i
      · intro h
        have hzP : P z := (Finset.mem_filter.mp hz).2
        exact ⟨by simpa only [funext h] using hzP, funext h⟩
    rw [heq]
    exact card_filter_vector_reduction_fiber p hts n z
  change S.card = p ^ ((s-t)*n) * T.card
  rw [Finset.card_eq_sum_card_fiberwise hf, Finset.sum_congr rfl hc]
  simp [mul_comm]

/-- Evaluating at actual remaining digits is the cast of the integral
polynomial evaluated at their shifted integer representatives. -/
theorem eval₂_lowDigitLift (F : MvPolynomial (Fin n) ℤ) (p a : ℕ)
    (k : Fin n → ℤ) (x : Fin n → ZMod (p ^ (a + 1))) :
    eval₂ (Int.castRingHom (ZMod (p ^ (a + 2)))) (lowDigitLift p (a+1) k x) F =
      ((eval (k + (p : ℤ) • (fun i => ((x i).val : ℤ))) F : ℤ) : ZMod (p ^ (a+2))) := by
  rw [SmoothResidueLifting.cast_eval_int]
  rfl

/-- The integral rescaling identity becomes a literal equivalence of
root conditions in the two residue rings. -/
theorem zero_lowDigitLift_iff (F G : MvPolynomial (Fin n) ℤ) (p a : ℕ)
    [Fact p.Prime] (k : Fin n → ℤ)
    (hidentity : ∀ y : Fin n → ℤ,
      eval (k + (p : ℤ) • y) F = (p : ℤ)^2 * eval y G)
    (x : Fin n → ZMod (p ^ (a+1))) :
    eval₂ (Int.castRingHom (ZMod (p ^ (a+2)))) (lowDigitLift p (a+1) k x) F = 0 ↔
      eval₂ (Int.castRingHom (ZMod (p ^ a)))
        (fun i => reduction p (Nat.le_succ a) (x i)) G = 0 := by
  rw [eval₂_lowDigitLift, hidentity,
    show (p : ℤ)^2 = ((p^2 : ℕ) : ℤ) by simp,
    power_mul_cast_eq_zero_iff, SmoothResidueLifting.cast_eval_int]
  have hv (i : Fin n) : (((x i).val : ℤ) : ZMod (p ^ a)) =
      reduction p (Nat.le_succ a) (x i) := by
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using
      (map_natCast (reduction p (Nat.le_succ a)) (x i).val).symm
  simp only [hv]

/-- Exact singular-class count for actual polynomials and literal prime
reduction. The supplied identity is the only rescaling premise. This
includes r=2, where G is evaluated in the one-element ring. -/
theorem card_singular_lifts_of_rescale (F G : MvPolynomial (Fin n) ℤ)
    (p r : ℕ) [Fact p.Prime] (hr : 2 ≤ r) (k : Fin n → ℤ)
    (hidentity : ∀ y : Fin n → ℤ,
      eval (k + (p : ℤ) • y) F = (p : ℤ)^2 * eval y G) :
    (Finset.univ.filter fun z : Fin n → ZMod (p^r) =>
      (∀ i, toPrime p r (by omega) (z i) = (k i : ZMod p)) ∧
      eval₂ (Int.castRingHom (ZMod (p^r))) z F = 0).card =
      p^n * (Finset.univ.filter fun z : Fin n → ZMod (p^(r-2)) =>
        eval₂ (Int.castRingHom (ZMod (p^(r-2)))) z G = 0).card := by
  classical
  obtain ⟨a, rfl⟩ : ∃ a, r = a+2 := ⟨r-2, by omega⟩
  rw [card_lowDigit_filter p (a+1)]
  simp only [zero_lowDigitLift_iff F G p a k hidentity]
  have ha : a.succ - a = 1 := by omega
  simpa only [ha, one_mul] using
    card_reduction_preimage p (Nat.le_succ a)
      (fun z => eval₂ (Int.castRingHom (ZMod (p^a))) z G = 0)

/-- At an actual critical center, the polynomial value is constant modulo
p² throughout its entire prime residue class, in every degree. -/
theorem sq_dvd_eval_translate_sub (F : MvPolynomial (Fin n) ℤ) (p : ℤ)
    (k y : Fin n → ℤ) (hgradient : ∀ i, p ∣ eval k (pderiv i F)) :
    p^2 ∣ eval (k + p • y) F - eval k F := by
  have hdir : p ∣ CubicTaylorExpansion.directional F k y := by
    change p ∣ ∑ i, y i * eval k (pderiv i F)
    exact Finset.dvd_sum (fun i _ => dvd_mul_of_dvd_right (hgradient i) (y i))
  have hmul : p^2 ∣ p * CubicTaylorExpansion.directional F k y := by
    rw [pow_two]
    exact mul_dvd_mul_left p hdir
  have hsum := dvd_add (GeneralSmoothResidueLifting.sq_dvd_eval_difference F k y p) hmul
  convert hsum using 1; ring

/-- Consequently divisibility by p² can be checked at the fixed center. -/
theorem sq_dvd_eval_translate_iff (F : MvPolynomial (Fin n) ℤ) (p : ℤ)
    (k y : Fin n → ℤ) (hgradient : ∀ i, p ∣ eval k (pderiv i F)) :
    p^2 ∣ eval (k + p • y) F ↔ p^2 ∣ eval k F := by
  have h := sq_dvd_eval_translate_sub F p k y hgradient
  constructor
  · intro hz
    simpa only [sub_sub_cancel] using dvd_sub hz h
  · intro hk
    simpa only [sub_add_cancel] using dvd_add h hk

/-- The actual root filter above a critical center is empty whenever its
value is not divisible by p². No degree or homogeneity input is needed. -/
theorem card_singular_lifts_of_not_sq_dvd (F : MvPolynomial (Fin n) ℤ)
    (p r : ℕ) [Fact p.Prime] (hr : 2 ≤ r) (k : Fin n → ℤ)
    (hgradient : ∀ i, (p : ℤ) ∣ eval k (pderiv i F))
    (h0 : ¬ (p : ℤ)^2 ∣ eval k F) :
    (Finset.univ.filter fun z : Fin n → ZMod (p^r) =>
      (∀ i, toPrime p r (by omega) (z i) = (k i : ZMod p)) ∧
      eval₂ (Int.castRingHom (ZMod (p^r))) z F = 0).card = 0 := by
  classical
  obtain ⟨a, rfl⟩ : ∃ a, r = a+2 := ⟨r-2, by omega⟩
  rw [card_lowDigit_filter p (a+1)]
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hroot
  have heq := (Finset.mem_filter.mp hroot).2
  rw [eval₂_lowDigitLift, ZMod.intCast_zmod_eq_zero_iff_dvd] at heq
  have hp : (p : ℤ)^2 ∣ ((p^(a+2) : ℕ) : ℤ) := by
    exact_mod_cast pow_dvd_pow p (show 2 ≤ a+2 by omega)
  exact h0 ((sq_dvd_eval_translate_iff F (p : ℤ) k _ hgradient).mp (hp.trans heq))

end CubicTenVariables.PolynomialSingularLifts
