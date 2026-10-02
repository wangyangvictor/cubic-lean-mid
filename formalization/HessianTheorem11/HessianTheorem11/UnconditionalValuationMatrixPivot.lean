import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.PEquiv
import Mathlib.Data.Finset.Max

/-! Integral Gaussian pivot operations for an actual valuation subring of a
field. Maximal multiplicative valuation makes every required coefficient
integral, so the elementary matrices are invertible over the subring itself. -/
noncomputable section
namespace HessianTheorem11.UnconditionalValuationMatrix
open Matrix

variable {K : Type*} [Field K] (V : ValuationSubring K)

/-- A finite nonzero matrix has a nonzero entry dividing every other entry
inside the valuation subring. -/
theorem exists_dominating_entry {ι : Type*} [Fintype ι]
    (M : Matrix ι ι K) (hM : M ≠ 0) :
    ∃ i j, M i j ≠ 0 ∧ ∀ a b, M a b / M i j ∈ V := by
  classical
  obtain ⟨a,b,hab⟩ : ∃ a b, M a b ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hM (Matrix.ext hn)
  letI : Nonempty (ι × ι) := ⟨(a,b)⟩
  obtain ⟨ij,_,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (ι × ι))
    (fun ij => V.valuation (M ij.1 ij.2)) Finset.univ_nonempty
  have hp : M ij.1 ij.2 ≠ 0 := by
    intro hz
    have h := hmax (a,b) (Finset.mem_univ _)
    rw [hz,map_zero] at h
    exact (not_lt_of_ge h) (V.valuation.pos_iff.mpr hab)
  refine ⟨ij.1,ij.2,hp,?_⟩
  intro a b
  obtain ⟨c,hc⟩ := (V.valuation_le_iff (M a b) (M ij.1 ij.2)).mp
    (hmax (a,b) (Finset.mem_univ _))
  have he : M a b / M ij.1 ij.2 = (c : K) := (div_eq_iff hp).mpr hc.symm
  rw [he]
  exact c.property

def matrixMap {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Matrix ι ι V →+* Matrix ι ι K := V.subtype.mapMatrix

@[simp] theorem matrixMap_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι V) (i j : ι) : matrixMap V A i j = (A i j : K) := rfl

@[simp] theorem matrixMap_transvection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (c : V) : matrixMap V (transvection i j c) = transvection i j (c : K) := by
  rw [transvection,map_add,map_one,transvection]
  congr 1
  exact Matrix.map_single i j c V.subtype

theorem transvection_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) (c : V) : IsUnit (transvection i j c) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [Matrix.det_transvection_of_ne i j hij c]
  exact isUnit_one

/-- The exact field Gaussian row/column elimination can be performed by
matrices that are units already over V. -/
theorem integral_pivot_block {r : ℕ}
    (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) K)
    (hp : M (Sum.inr ()) (Sum.inr ()) ≠ 0)
    (hdiv : ∀ i j, M i j / M (Sum.inr ()) (Sum.inr ()) ∈ V) :
    ∃ A B : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) V,
      IsUnit A ∧ IsUnit B ∧ IsTwoBlockDiagonal (matrixMap V A * M * matrixMap V B) := by
  classical
  let c (i : Fin r) : V := ⟨-M (Sum.inl i) (Sum.inr ()) / M (Sum.inr ()) (Sum.inr ()), by
    rw [neg_div]
    exact V.neg_mem _ (hdiv _ _)⟩
  let d (i : Fin r) : V := ⟨-M (Sum.inr ()) (Sum.inl i) / M (Sum.inr ()) (Sum.inr ()), by
    rw [neg_div]
    exact V.neg_mem _ (hdiv _ _)⟩
  let L : List (Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) V) :=
    List.ofFn (fun i : Fin r => transvection (Sum.inl i) (Sum.inr ()) (c i))
  let R : List (Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) V) :=
    List.ofFn (fun i : Fin r => transvection (Sum.inr ()) (Sum.inl i) (d i))
  have hL : IsUnit L.prod := by
    apply List.prod_isUnit
    intro A hA
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hA
    exact transvection_isUnit V _ _ (by simp) _
  have hR : IsUnit R.prod := by
    apply List.prod_isUnit
    intro A hA
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hA
    exact transvection_isUnit V _ _ (by simp) _
  have hLc : matrixMap V L.prod = (Matrix.Pivot.listTransvecCol M).prod := by
    rw [map_list_prod]
    congr 1
    simp [L,Matrix.Pivot.listTransvecCol,c,Function.comp_def]
  have hRc : matrixMap V R.prod = (Matrix.Pivot.listTransvecRow M).prod := by
    rw [map_list_prod]
    congr 1
    simp [R,Matrix.Pivot.listTransvecRow,d,Function.comp_def]
  refine ⟨L.prod,R.prod,hL,hR,?_⟩
  rw [hLc,hRc]
  exact Matrix.Pivot.isTwoBlockDiagonal_listTransvecCol_mul_mul_listTransvecRow M hp

end HessianTheorem11.UnconditionalValuationMatrix
