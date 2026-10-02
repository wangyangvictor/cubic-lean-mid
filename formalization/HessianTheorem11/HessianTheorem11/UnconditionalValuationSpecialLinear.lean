import HessianTheorem11.UnconditionalValuationMatrix

/-! Determinant-one Cartan factorization over an arbitrary valuation subring.
The two integral frames and their residue frames are genuinely special linear. -/
noncomputable section
namespace HessianTheorem11.UnconditionalValuationMatrix
open Matrix

section Scaling
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

def pivotScale (i : ι) (a : R) : Matrix ι ι R :=
  diagonal (fun j => if j = i then a else 1)

@[simp] theorem det_pivotScale (i : ι) (a : R) : (pivotScale i a).det = a := by
  simp [pivotScale,Matrix.det_diagonal]

end Scaling

variable {K : Type*} [Field K] (V : ValuationSubring K)

@[simp] theorem matrixMap_pivotScale {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (a : V) : matrixMap V (pivotScale i a) = pivotScale i (a : K) := by
  change (diagonal (fun j => if j = i then a else 1)).map V.subtype =
    diagonal (fun j => if j = i then (a : K) else 1)
  rw [Matrix.diagonal_map V.subtype.map_zero]
  congr 1
  funext j
  by_cases h : j = i <;> simp [h]

@[simp] theorem det_matrixMap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι V) : (matrixMap V A).det = (A.det : K) :=
  (V.subtype.map_det A).symm

/-- In positive dimension an SL matrix has a Cartan factorization in which
both integral factors have determinant exactly one and the diagonal entries
have product exactly one. There is no assumption on the rank of the valuation. -/
theorem exists_specialLinear_factorization {n : ℕ} (hn : 0 < n)
    (M : Matrix (Fin n) (Fin n) K) (hM : M.det = 1) :
    ∃ (A B : Matrix (Fin n) (Fin n) V) (d : Fin n → K),
      A.det = 1 ∧ B.det = 1 ∧ (∀ i, d i ≠ 0) ∧ (∏ i, d i) = 1 ∧
      M = matrixMap V A * diagonal d * matrixMap V B := by
  classical
  obtain ⟨A,B,d,hA,hB,hd,he⟩ := exists_factorization V M (by rw [hM]; exact one_ne_zero)
  obtain ⟨a,ha⟩ := (Matrix.isUnit_iff_isUnit_det A).mp hA
  obtain ⟨b,hb⟩ := (Matrix.isUnit_iff_isUnit_det B).mp hB
  let i : Fin n := ⟨0,hn⟩
  let A' := A * pivotScale i (↑(a⁻¹) : V)
  let B' := pivotScale i (↑(b⁻¹) : V) * B
  let d' : Fin n → K := fun j =>
    (if j = i then ((a : V) : K) else 1) * d j *
      (if j = i then ((b : V) : K) else 1)
  have hA' : A'.det = 1 := by
    dsimp [A']
    rw [Matrix.det_mul,det_pivotScale,←ha]
    exact a.mul_inv
  have hB' : B'.det = 1 := by
    dsimp [B']
    rw [Matrix.det_mul,det_pivotScale,←hb]
    exact b.inv_mul
  have hai : (((a⁻¹ : Vˣ) : V) : K) * ((a : V) : K) = 1 := by
    change V.subtype (↑(a⁻¹)) * V.subtype (↑a) = 1
    rw [←map_mul]
    simp
  have hbi : ((b : V) : K) * (((b⁻¹ : Vˣ) : V) : K) = 1 := by
    change V.subtype (↑b) * V.subtype (↑(b⁻¹)) = 1
    rw [←map_mul]
    simp
  have hmid : matrixMap V (pivotScale i (↑(a⁻¹) : V)) * diagonal d' *
      matrixMap V (pivotScale i (↑(b⁻¹) : V)) = diagonal d := by
    rw [matrixMap_pivotScale,matrixMap_pivotScale]
    unfold pivotScale
    rw [Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    by_cases hj : j = i
    · simp only [d',hj,if_pos]
      calc
        _ = ((((a⁻¹ : Vˣ) : V) : K) * ((a : V) : K)) * d i *
          (((b : V) : K) * (((b⁻¹ : Vˣ) : V) : K)) := by ring
        _ = d i := by rw [hai,hbi]; simp
    · simp [d',hj]
  have he' : M = matrixMap V A' * diagonal d' * matrixMap V B' := by
    rw [he]
    dsimp [A',B']
    rw [map_mul,map_mul]
    calc
      _ = matrixMap V A * (matrixMap V (pivotScale i (↑(a⁻¹) : V)) * diagonal d' *
          matrixMap V (pivotScale i (↑(b⁻¹) : V))) * matrixMap V B := by rw [hmid]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hd' : ∀ j, d' j ≠ 0 := by
    intro j
    dsimp [d']
    apply mul_ne_zero
    · apply mul_ne_zero
      · split_ifs
        · exact fun h => a.ne_zero (Subtype.ext h)
        · exact one_ne_zero
      · exact hd j
    · split_ifs
      · exact fun h => b.ne_zero (Subtype.ext h)
      · exact one_ne_zero
  have hprod : (∏ j, d' j) = 1 := by
    have h := congrArg Matrix.det he'
    simpa [hM,Matrix.det_mul,det_matrixMap,hA',hB',Matrix.det_diagonal] using h.symm
  exact ⟨A',B',d',hA',hB',hd',hprod,he'⟩

end HessianTheorem11.UnconditionalValuationMatrix
