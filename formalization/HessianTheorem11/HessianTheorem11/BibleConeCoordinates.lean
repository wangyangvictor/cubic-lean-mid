import HessianTheorem11.BibleVertex
import HessianTheorem11.AdaptedFlag
import Mathlib.Algebra.MvPolynomial.Funext

/-! A coordinate criterion for the ordinary cone structure. The maximal
translation vertex is exactly the collection of directions in which the
homogeneous equation is independent of its variables. In particular a
nonzero vertex is equivalent to an invertible coordinate system in which
the cubic is the pullback of a cubic in one fewer variable. -/
noncomputable section
namespace HessianTheorem11.BibleVertex
open MvPolynomial Module PolynomialRestriction

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

def eraseCoordinates (J : Finset (Fin n)) (z : Fin n → K) : Fin n → K :=
  fun i => if i ∈ J then 0 else z i

def remainingVariable (J : Finset (Fin n)) (i : Fin n) :
    MvPolynomial {j : Fin n // j ∉ J} K :=
  if h : i ∈ J then 0 else X ⟨i,h⟩

def removeCoordinates (J : Finset (Fin n)) (P : MvPolynomial (Fin n) K) :
    MvPolynomial {j : Fin n // j ∉ J} K := aeval (remainingVariable J) P

theorem remaining_variables_card (J : Finset (Fin n)) :
    Fintype.card {j : Fin n // j ∉ J} = n - J.card := by
  rw [Fintype.card_subtype_compl]
  simp

theorem removeCoordinates_homogeneous (J : Finset (Fin n))
    (P : MvPolynomial (Fin n) K) {d : ℕ} (hP : P.IsHomogeneous d) :
    (removeCoordinates J P).IsHomogeneous d := by
  have hlinear (i : Fin n) : (remainingVariable (K := K) J i).IsHomogeneous 1 := by
    unfold remainingVariable
    split_ifs
    · exact isHomogeneous_zero _ _ _
    · exact isHomogeneous_X _ _
  simpa only [one_mul] using hP.aeval (remainingVariable J) hlinear

theorem eval_rename_removeCoordinates (J : Finset (Fin n))
    (P : MvPolynomial (Fin n) K) (z : Fin n → K) :
    eval z (rename Subtype.val (removeCoordinates J P)) = eval (eraseCoordinates J z) P := by
  rw [eval_rename]
  change aeval (z ∘ Subtype.val) (aeval (remainingVariable J) P) = aeval (eraseCoordinates J z) P
  rw [MvPolynomial.comp_aeval_apply]
  have hvars : (fun i => aeval (fun j : {j : Fin n // j ∉ J} => z j.val)
      (remainingVariable (K := K) J i)) = eraseCoordinates J z := by
    funext i
    by_cases hi : i ∈ J <;> simp [remainingVariable, eraseCoordinates, hi]
  exact congrArg (fun f : Fin n → K => aeval f P) hvars

/-- For any selected basis directions, membership in the actual maximal
vertex is equivalent to an actual polynomial in only the remaining variables. -/
theorem coordinates_factor_iff_vertex
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (b : Basis (Fin n) K (Fin n → K)) (J : Finset (Fin n)) :
    (∀ i ∈ J, b i ∈ affineVertex F hF) ↔
      ∃ Q : MvPolynomial {j : Fin n // j ∉ J} K,
        Q.IsHomogeneous 3 ∧ restrict (basisMatrix b) F = rename Subtype.val Q := by
  classical
  constructor
  · intro hvertex
    let P := restrict (basisMatrix b) F
    refine ⟨removeCoordinates J P,
      removeCoordinates_homogeneous J P (homogeneous_restrict _ F hF), ?_⟩
    apply MvPolynomial.funext
    intro z
    rw [eval_rename_removeCoordinates, eval_restrict, eval_restrict,
      basisMatrix_mulVec_eq, basisMatrix_mulVec_eq]
    let v := b.equivFun.symm (z - eraseCoordinates J z)
    have hv : v ∈ affineVertex F hF := by
      dsimp only [v]
      rw [Basis.equivFun_symm_apply]
      apply Submodule.sum_mem
      intro i _
      by_cases hi : i ∈ J
      · exact (affineVertex F hF).smul_mem _ (hvertex i hi)
      · simp [eraseCoordinates, hi]
    have he := translation_of_hessian_zero F hF v hv
      (b.equivFun.symm (eraseCoordinates J z)) 1
    have hvsum : b.equivFun.symm (eraseCoordinates J z) + (1 : K) • v = b.equivFun.symm z := by
      simp only [v, map_sub, one_smul]
      abel
    rwa [hvsum] at he
  · rintro ⟨Q,hQ,he⟩ i hi
    apply (mem_affineVertex_iff_translation F hF (b i)).mpr
    intro x t
    let z := b.equivFun x
    have hshift : (basisMatrix b).mulVec (z + t • (Pi.single i (1 : K) : Fin n → K)) =
        x + t • b i := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, basisMatrix_mulVec_single,
        basisMatrix_mulVec_eq]
      simp [z]
    calc
      eval (x + t • b i) F = eval (z + t • (Pi.single i (1 : K) : Fin n → K))
          (restrict (basisMatrix b) F) := by
        rw [eval_restrict, hshift]
      _ = eval z (restrict (basisMatrix b) F) := by
        rw [he, eval_rename, eval_rename]
        have hcoords : (fun j : {j : Fin n // j ∉ J} =>
            (z + t • (Pi.single i (1 : K) : Fin n → K)) j.val) = fun j => z j.val := by
          funext j
          have hji : (j : Fin n) ≠ i := by intro h; exact j.property (h ▸ hi)
          simp [Pi.single_apply, hji]
        exact congrArg (fun a : {j : Fin n // j ∉ J} → K => eval a Q) hcoords
      _ = eval x F := by
        rw [eval_restrict, basisMatrix_mulVec_eq]
        simp [z]

/-- Explicit coordinate meaning of the cone predicate: after an invertible
basis change the defining cubic is independent of one of the coordinates.
The remaining variable type has exactly n−1 elements. -/
theorem isProjectiveCone_iff_coordinates
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3) :
    IsProjectiveCone F ↔
      ∃ (b : Basis (Fin n) K (Fin n → K)) (r : Fin n)
        (Q : MvPolynomial {j : Fin n // j ∉ ({r} : Finset (Fin n))} K),
        Q.IsHomogeneous 3 ∧ restrict (basisMatrix b) F = rename Subtype.val Q := by
  classical
  constructor
  · rintro ⟨v,hv,htrans⟩
    let T : Submodule K (Fin n → K) := Submodule.span K {v}
    have hvmem : v ∈ T := Submodule.subset_span (Set.mem_singleton v)
    let A := adaptedFlagBasis T T le_rfl v hv hvmem
    have h : ∀ i ∈ ({A.radial} : Finset (Fin n)), A.basis i ∈ affineVertex F hF := by
      intro i hi
      have hi' : i = A.radial := Finset.mem_singleton.mp hi
      rw [hi', A.radial_eq]
      exact (mem_affineVertex_iff_translation F hF v).mpr htrans
    obtain ⟨Q,hQ,he⟩ := (coordinates_factor_iff_vertex F hF A.basis {A.radial}).mp h
    exact ⟨A.basis,A.radial,Q,hQ,he⟩
  · rintro ⟨b,r,Q,hQ,he⟩
    have h := (coordinates_factor_iff_vertex F hF b {r}).mpr ⟨Q,hQ,he⟩
    exact ⟨b r, b.ne_zero r,
      (mem_affineVertex_iff_translation F hF (b r)).mp (h r (Finset.mem_singleton_self r))⟩

end HessianTheorem11.BibleVertex
