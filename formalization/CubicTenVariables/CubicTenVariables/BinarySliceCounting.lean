import CubicTenVariables.QuadraticRankTwoCoordinates
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fintype.BigOperators

/-! Finite counting by an actual selected pair of coordinates. Reconstruction
of the full vector and its inverse are constructed, and the fiber count is
then summed over the complementary coordinates. The bounds on individual
slices are explicit hypotheses, not asserted polynomial root theorems. -/

noncomputable section
namespace CubicTenVariables.BinarySliceCounting
open Matrix

abbrev Complement {n : ℕ} (e : Fin 2 ↪ Fin n) :=
  {i : Fin n // i ∉ Set.range e}

instance complementFintype {n : ℕ} (e : Fin 2 ↪ Fin n) : Fintype (Complement e) :=
  Fintype.ofFinite _

/-- The selected indices and their actual set-theoretic complement exhaust
the original coordinate set, without overlap. -/
def indexEquiv {n : ℕ} (e : Fin 2 ↪ Fin n) : Fin 2 ⊕ Complement e ≃ Fin n := by
  classical
  exact (Equiv.sumCongr e.toEquivRange (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range e))

@[simp] theorem indexEquiv_inl {n : ℕ} (e : Fin 2 ↪ Fin n) (j : Fin 2) :
    indexEquiv e (Sum.inl j) = e j := rfl

@[simp] theorem indexEquiv_inr {n : ℕ} (e : Fin 2 ↪ Fin n) (i : Complement e) :
    indexEquiv e (Sum.inr i) = i := rfl

/-- Reconstruct the actual vector from its two selected coordinates and
the fixed values on every complementary coordinate. -/
def combine {n : ℕ} {R : Type*} (e : Fin 2 ↪ Fin n)
    (z : Fin 2 → R) (w : Complement e → R) : Fin n → R :=
  fun i => Sum.elim z w ((indexEquiv e).symm i)

/-- Reconstruction commutes with every pointwise map, in particular with
the cast from integral coordinates to residue coordinates. -/
theorem map_combine {n : ℕ} {R S : Type*} (f : R → S) (e : Fin 2 ↪ Fin n)
    (z : Fin 2 → R) (w : Complement e → R) :
    (fun i => f (combine e z w i)) =
      combine e (fun j => f (z j)) (fun i => f (w i)) := by
  funext i
  cases h : (indexEquiv e).symm i <;> simp only [combine, h, Sum.elim_inl, Sum.elim_inr]

@[simp] theorem combine_selected {n : ℕ} {R : Type*} (e : Fin 2 ↪ Fin n)
    (z : Fin 2 → R) (w : Complement e → R) (j : Fin 2) :
    combine e z w (e j) = z j := by
  change Sum.elim z w ((indexEquiv e).symm (indexEquiv e (Sum.inl j))) = z j
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem combine_complement {n : ℕ} {R : Type*} (e : Fin 2 ↪ Fin n)
    (z : Fin 2 → R) (w : Complement e → R) (i : Fin n) (hi : i ∉ Set.range e) :
    combine e z w i = w ⟨i, hi⟩ := by
  change Sum.elim z w ((indexEquiv e).symm (indexEquiv e (Sum.inr ⟨i, hi⟩))) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem combine_complement_index {n : ℕ} {R : Type*} (e : Fin 2 ↪ Fin n)
    (z : Fin 2 → R) (w : Complement e → R) (i : Complement e) :
    combine e z w i = w i := combine_complement e z w i i.property

/-- Splitting and reconstructing coordinate vectors are inverse operations. -/
def splitEquiv {n : ℕ} (e : Fin 2 ↪ Fin n) (R : Type*) :
    (Fin n → R) ≃ (Fin 2 → R) × (Complement e → R) :=
  ((indexEquiv e).symm.arrowCongr (Equiv.refl R)).trans
    (Equiv.sumArrowEquivProdArrow (Fin 2) (Complement e) R)

@[simp] theorem splitEquiv_symm {n : ℕ} {R : Type*} (e : Fin 2 ↪ Fin n)
    (z : Fin 2 → R) (w : Complement e → R) :
    (splitEquiv e R).symm (z, w) = combine e z w := rfl

theorem card_complement {n : ℕ} (e : Fin 2 ↪ Fin n) :
    Fintype.card (Complement e) = n - 2 := by
  have h := Fintype.card_congr (indexEquiv e)
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  omega

/-- Summation over all coordinates is the sum over the selected pair and
the complementary coordinates. -/
theorem sum_split {n : ℕ} {R : Type*} [AddCommMonoid R]
    (e : Fin 2 ↪ Fin n) (f : Fin n → R) :
    ∑ i, f i = (∑ j : Fin 2, f (e j)) + ∑ i : Complement e, f i := by
  simpa only [Fintype.sum_sum_type, indexEquiv_inl, indexEquiv_inr] using
    (Equiv.sum_comp (indexEquiv e) f).symm

/-- After any actual matrix coordinate change, a fixed complementary
slice is exactly a translated two-column linear family. -/
theorem mulVec_combine {n m : ℕ} {R : Type*} [Semiring R]
    (A : Matrix (Fin m) (Fin n) R) (e : Fin 2 ↪ Fin n)
    (z : Fin 2 → R) (w : Complement e → R) :
    A.mulVec (combine e z w) = A.mulVec (combine e 0 w) +
      Matrix.mulVec (fun i j => A i (e j)) z := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply]
  rw [sum_split e (fun j => A i j * combine e z w j),
    sum_split e (fun j => A i j * combine e 0 w j)]
  simp only [combine_selected, combine_complement_index, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero, zero_add]
  exact add_comm _ _

/-- The actual number of satisfying vectors is the sum of the actual
two-coordinate slice counts. -/
theorem card_filter_eq_sum_slices {n : ℕ} {R : Type*} [Fintype R]
    (e : Fin 2 ↪ Fin n) (P : (Fin n → R) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      ∑ w : Complement e → R,
        (Finset.univ.filter fun z : Fin 2 → R => P (combine e z w)).card := by
  classical
  let E := (splitEquiv e R).trans (Equiv.prodComm _ _)
  let q := fun w : Complement e → R => fun z : Fin 2 → R => P (combine e z w)
  have hq : ∀ x, P x ↔ q (E x).1 (E x).2 := by
    intro x
    change P x ↔ P ((splitEquiv e R).symm (splitEquiv e R x))
    rw [Equiv.symm_apply_apply]
  have he := Fintype.card_congr
    ((E.subtypeEquiv hq).trans (Equiv.subtypeProdEquivSigmaSubtype q))
  simpa only [Fintype.card_sigma, Fintype.card_subtype, q] using he

/-- Uniform slice bounds give the total bound, with the exact number of
complementary choices. -/
theorem card_filter_le_of_slices {n : ℕ} {R : Type*} [Fintype R]
    (e : Fin 2 ↪ Fin n) (P : (Fin n → R) → Prop) [DecidablePred P]
    (B : ℕ)
    (hB : ∀ w : Complement e → R,
      (Finset.univ.filter fun z : Fin 2 → R => P (combine e z w)).card ≤ B) :
    (Finset.univ.filter P).card ≤ Fintype.card R ^ (n - 2) * B := by
  rw [card_filter_eq_sum_slices e P]
  calc
    _ ≤ ∑ _w : Complement e → R, B := Finset.sum_le_sum (fun w _ => hB w)
    _ = Fintype.card R ^ (n - 2) * B := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_fun, card_complement, Nat.cast_id]

/-- Assembly at the literal residue level p^s. No assertion about an
individual polynomial slice is hidden in this theorem. -/
theorem residue_count_le {n : ℕ} (hn : 2 ≤ n) (p s : ℕ) [NeZero p]
    (e : Fin 2 ↪ Fin n) (P : (Fin n → ZMod (p^s)) → Prop) [DecidablePred P]
    (hB : ∀ w : Complement e → ZMod (p^s),
      (Finset.univ.filter fun z : Fin 2 → ZMod (p^s) => P (combine e z w)).card
        ≤ (s+1)*p^s) :
    (Finset.univ.filter P).card ≤ (s+1)*p^(s*(n-1)) := by
  have h := card_filter_le_of_slices e P ((s+1)*p^s) hB
  rw [ZMod.card] at h
  convert h using 1
  rw [pow_mul]
  have hn' : n - 1 = (n - 2) + 1 := by omega
  rw [hn', pow_succ]
  ring

/-- Counting is unchanged by any supplied bijection of the actual finite
vector space. -/
theorem card_filter_comp_bijective {V : Type*} [Fintype V]
    (f : V → V) (hf : Function.Bijective f) (P : V → Prop) [DecidablePred P] :
    (Finset.univ.filter fun v => P (f v)).card = (Finset.univ.filter P).card := by
  classical
  let E : {v // P (f v)} ≃ {v // P v} :=
    (Equiv.ofBijective f hf).subtypeEquiv (fun _ => Iff.rfl)
  simpa only [Fintype.card_subtype] using
    Fintype.card_congr E

/-- The same assembly applies after the actual integral matrix coordinate
change; nonvanishing determinant modulo p supplies all residue bijections. -/
theorem residue_count_le_after_matrix {n : ℕ} (hn : 2 ≤ n)
    (p : ℕ) [Fact p.Prime] (s : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : (A.det : ZMod p) ≠ 0)
    (e : Fin 2 ↪ Fin n) (P : (Fin n → ZMod (p^s)) → Prop) [DecidablePred P]
    (hB : ∀ w : Complement e → ZMod (p^s),
      (Finset.univ.filter fun z : Fin 2 → ZMod (p^s) =>
        P ((A.map (Int.castRingHom (ZMod (p^s)))).mulVec (combine e z w))).card
          ≤ (s+1)*p^s) :
    (Finset.univ.filter P).card ≤ (s+1)*p^(s*(n-1)) := by
  have h := residue_count_le hn p s e
    (fun v => P ((A.map (Int.castRingHom (ZMod (p^s)))).mulVec v)) hB
  rwa [card_filter_comp_bijective _
    (QuadraticRankTwoCoordinates.integral_matrix_bijective_prime_power p A hA s) P] at h

end CubicTenVariables.BinarySliceCounting
