import CubicTenVariables.SmithKernelFormula
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.NatAbs

/-!
# Modular kernel bounds from an actual nonzero integral minor

A full-rank square matrix has at most the absolute value of its determinant
many kernel vectors modulo every positive integer. For a selected minor,
fixing the complementary coordinates reduces each fiber to an affine fiber
of that square matrix. All matrices and residue equations are literal.
-/

noncomputable section
namespace CubicTenVariables.ModularMinorKernelBound
open Matrix
open scoped BigOperators

/-- The actual modular kernel of a nonsingular integer square matrix has
at most |det| elements, including modulus one and the empty matrix. -/
theorem card_kernel_le_natAbs_det {j : ℕ} (B : Matrix (Fin j) (Fin j) ℤ)
    (hB : B.det ≠ 0) (m : ℕ) [NeZero m] :
    Nat.card {x : Fin j → ZMod m //
      (B.map (Int.castRingHom (ZMod m))).mulVec x = 0} ≤ B.det.natAbs := by
  obtain ⟨U,V,d,hD,hcard⟩ := SmithKernelFormula.exists_diagonalization_and_kernel_formula B
  have hU : (U : Matrix (Fin j) (Fin j) ℤ).det.natAbs = 1 :=
    Int.isUnit_iff_natAbs_eq.mp (Matrix.isUnits_det_units U)
  have hV : (V : Matrix (Fin j) (Fin j) ℤ).det.natAbs = 1 :=
    Int.isUnit_iff_natAbs_eq.mp (Matrix.isUnits_det_units V)
  have habs : (∏ i, (d i).natAbs) = B.det.natAbs := by
    have h := congrArg (fun A : Matrix (Fin j) (Fin j) ℤ => A.det.natAbs) hD
    have hprod : (∏ i, d i).natAbs = ∏ i, (d i).natAbs :=
      map_prod Int.natAbsHom d Finset.univ
    simpa only [Matrix.det_mul, Matrix.det_diagonal, Int.natAbs_mul, hU, hV,
      one_mul, mul_one, hprod] using h.symm
  have hd : ∀ i, (d i).natAbs ≠ 0 := by
    intro i hi
    have hz : (∏ i, (d i).natAbs) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [habs] at hz
    exact hB (Int.natAbs_eq_zero.mp hz)
  rw [hcard m (Nat.pos_of_ne_zero (NeZero.ne m)), ← habs]
  exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    (fun i _ => Nat.gcd_le_left m (Nat.pos_of_ne_zero (hd i)))

/-- An affine fiber of a matrix is empty or a translate of its actual kernel. -/
theorem card_fiber_le_natAbs_det {j : ℕ} (B : Matrix (Fin j) (Fin j) ℤ)
    (hB : B.det ≠ 0) (m : ℕ) [NeZero m] (b : Fin j → ZMod m) :
    (Finset.univ.filter fun x : Fin j → ZMod m =>
      (B.map (Int.castRingHom (ZMod m))).mulVec x = b).card ≤ B.det.natAbs := by
  classical
  let f := (B.map (Int.castRingHom (ZMod m))).mulVecLin.toAddMonoidHom
  by_cases h : ∃ x, f x = b
  · obtain ⟨x,hx⟩ := h
    have he : Nat.card {z : Fin j → ZMod m // f z = b} = Nat.card f.ker := by
      change Nat.card (f ⁻¹' {b}) = _
      rw [← hx]
      exact Nat.card_congr (f.fiberEquivKer x)
    have hk := card_kernel_le_natAbs_det B hB m
    change Nat.card f.ker ≤ _ at hk
    rw [← he] at hk
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hk
  · have hz : ∀ x : Fin j → ZMod m,
        ¬ (B.map (Int.castRingHom (ZMod m))).mulVec x = b := by
      intro x hx
      exact h ⟨x,hx⟩
    simp only [hz, Finset.filter_false, Finset.card_empty, zero_le]

private abbrev Complement {n j : ℕ} (e : Fin j ↪ Fin n) :=
  {i : Fin n // i ∉ Set.range e}

private instance complementFintype {n j : ℕ} (e : Fin j ↪ Fin n) :
    Fintype (Complement e) := Fintype.ofFinite _

private def indexEquiv {n j : ℕ} (e : Fin j ↪ Fin n) :
    Fin j ⊕ Complement e ≃ Fin n := by
  classical
  exact (Equiv.sumCongr e.toEquivRange (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range e))

private def combine {n j : ℕ} {R : Type*} (e : Fin j ↪ Fin n)
    (z : Fin j → R) (w : Complement e → R) : Fin n → R :=
  fun i => Sum.elim z w ((indexEquiv e).symm i)

private theorem combine_selected {n j : ℕ} {R : Type*} (e : Fin j ↪ Fin n)
    (z : Fin j → R) (w : Complement e → R) (a : Fin j) :
    combine e z w (e a) = z a := by
  change Sum.elim z w ((indexEquiv e).symm (indexEquiv e (Sum.inl a))) = z a
  rw [Equiv.symm_apply_apply]
  rfl

private theorem combine_complement {n j : ℕ} {R : Type*} (e : Fin j ↪ Fin n)
    (z : Fin j → R) (w : Complement e → R) (i : Complement e) :
    combine e z w i = w i := by
  change Sum.elim z w ((indexEquiv e).symm (indexEquiv e (Sum.inr i))) = w i
  rw [Equiv.symm_apply_apply]
  rfl

private def splitEquiv {n j : ℕ} (e : Fin j ↪ Fin n) (R : Type*) :
    (Fin n → R) ≃ (Fin j → R) × (Complement e → R) :=
  ((indexEquiv e).symm.arrowCongr (Equiv.refl R)).trans
    (Equiv.sumArrowEquivProdArrow (Fin j) (Complement e) R)

private theorem card_complement {n j : ℕ} (e : Fin j ↪ Fin n) :
    Fintype.card (Complement e) = n-j := by
  have h := Fintype.card_congr (indexEquiv e)
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  omega

private theorem sum_split {n j : ℕ} {R : Type*} [AddCommMonoid R]
    (e : Fin j ↪ Fin n) (f : Fin n → R) :
    ∑ i, f i = (∑ a : Fin j, f (e a)) + ∑ i : Complement e, f i := by
  simpa only [Fintype.sum_sum_type] using (Equiv.sum_comp (indexEquiv e) f).symm

private theorem mulVec_combine {n j : ℕ} {R : Type*} [Semiring R]
    (A : Matrix (Fin n) (Fin n) R) (e : Fin j ↪ Fin n)
    (z : Fin j → R) (w : Complement e → R) :
    A.mulVec (combine e z w) = A.mulVec (combine e 0 w) +
      Matrix.mulVec (fun i a => A i (e a)) z := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply]
  rw [sum_split e (fun a => A i a * combine e z w a),
    sum_split e (fun a => A i a * combine e 0 w a)]
  simp only [combine_selected, combine_complement, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero, zero_add]
  exact add_comm _ _

private theorem card_filter_le_of_slices {n j : ℕ} {R : Type*} [Fintype R]
    (e : Fin j ↪ Fin n) (P : (Fin n → R) → Prop) [DecidablePred P] (C : ℕ)
    (hC : ∀ w : Complement e → R,
      (Finset.univ.filter fun z : Fin j → R => P (combine e z w)).card ≤ C) :
    (Finset.univ.filter P).card ≤ Fintype.card R ^ (n-j) * C := by
  classical
  let E := (splitEquiv e R).trans (Equiv.prodComm _ _)
  let q := fun w : Complement e → R => fun z : Fin j → R => P (combine e z w)
  have hq : ∀ x, P x ↔ q (E x).1 (E x).2 := by
    intro x
    change P x ↔ P ((splitEquiv e R).symm (splitEquiv e R x))
    rw [Equiv.symm_apply_apply]
  have he := Fintype.card_congr
    ((E.subtypeEquiv hq).trans (Equiv.subtypeProdEquivSigmaSubtype q))
  have hs : (Finset.univ.filter P).card =
      ∑ w : Complement e → R,
        (Finset.univ.filter fun z : Fin j → R => P (combine e z w)).card := by
    simpa only [Fintype.card_sigma, Fintype.card_subtype, q] using he
  rw [hs]
  calc
    _ ≤ ∑ _w : Complement e → R, C := Finset.sum_le_sum (fun w _ => hC w)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_fun, card_complement, Nat.cast_id]

/-- Any actual nonzero integral j-by-j minor controls the complete modular
kernel. The embeddings allow unrelated row and column sets. -/
theorem card_kernel_le_minor {n j : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (rows cols : Fin j ↪ Fin n) (hdet : (B.submatrix rows cols).det ≠ 0)
    (m : ℕ) [NeZero m] :
    (Finset.univ.filter fun x : Fin n → ZMod m =>
      (B.map (Int.castRingHom (ZMod m))).mulVec x = 0).card ≤
        m^(n-j)*(B.submatrix rows cols).det.natAbs := by
  classical
  apply (card_filter_le_of_slices cols _ (B.submatrix rows cols).det.natAbs ?_).trans_eq
    (by rw [ZMod.card])
  intro w
  let A := B.map (Int.castRingHom (ZMod m))
  let b : Fin j → ZMod m := fun i => -(A.mulVec (combine cols 0 w) (rows i))
  apply (Finset.card_le_card (show
      (Finset.univ.filter fun z : Fin j → ZMod m =>
        A.mulVec (combine cols z w) = 0) ⊆
      (Finset.univ.filter fun z : Fin j → ZMod m =>
        ((B.submatrix rows cols).map (Int.castRingHom (ZMod m))).mulVec z = b) from ?_)).trans
    (card_fiber_le_natAbs_det (B.submatrix rows cols) hdet m b)
  intro z hz
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ z, ?_⟩
  have hz' := (Finset.mem_filter.mp hz).2
  rw [mulVec_combine] at hz'
  funext i
  have hi := congrFun hz' (rows i)
  change A.mulVec (combine cols 0 w) (rows i) +
    ((B.submatrix rows cols).map (Int.castRingHom (ZMod m))).mulVec z i = 0 at hi
  exact eq_neg_of_add_eq_zero_right hi

/-- Natural-cardinality form of the same literal kernel estimate. -/
theorem natCard_kernel_le_minor {n j : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (rows cols : Fin j ↪ Fin n) (hdet : (B.submatrix rows cols).det ≠ 0)
    (m : ℕ) [NeZero m] :
    Nat.card {x : Fin n → ZMod m //
      (B.map (Int.castRingHom (ZMod m))).mulVec x = 0} ≤
        m^(n-j)*(B.submatrix rows cols).det.natAbs := by
  classical
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using
    card_kernel_le_minor B rows cols hdet m

end CubicTenVariables.ModularMinorKernelBound
