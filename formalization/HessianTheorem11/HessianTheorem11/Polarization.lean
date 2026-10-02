import HessianTheorem11.HessianLinearity
import HessianTheorem11.PolynomialRestriction

/-! The actual cubic polarization tensor and its behavior in a basis. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Module

variable {K : Type*} [CommRing K] {n : ℕ}

def polarization (F : MvPolynomial (Fin n) K) (u v w : Fin n → K) : K :=
  dotProduct u ((hessian F w).mulVec v)

theorem polarization_swap_first (F : MvPolynomial (Fin n) K) (u v w : Fin n → K) :
    polarization F u v w = polarization F v u w := by
  simp only [polarization, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i j) (hessian_symmetric F w)
  change hessian F w j i = hessian F w i j at h
  rw [h]
  ring

theorem polarization_swap_last {F : MvPolynomial (Fin n) K}
    (hF : F.IsHomogeneous 3) (u v w : Fin n → K) :
    polarization F u v w = polarization F u w v := by
  unfold polarization
  rw [hessian_polarization hF w v]

theorem polarization_rotate {F : MvPolynomial (Fin n) K}
    (hF : F.IsHomogeneous 3) (u v w : Fin n → K) :
    polarization F u v w = polarization F w u v := by
  rw [polarization_swap_last hF, polarization_swap_first]

def basisMatrix (b : Basis (Fin n) K (Fin n → K)) : Matrix (Fin n) (Fin n) K :=
  fun i j => b j i

theorem basisMatrix_mulVec_single (b : Basis (Fin n) K (Fin n → K)) (i : Fin n) :
    (basisMatrix b).mulVec (Pi.single i 1) = b i := by
  classical
  ext j
  simp [basisMatrix, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem basisMatrix_mulVec_eq (b : Basis (Fin n) K (Fin n → K)) (x : Fin n → K) :
    (basisMatrix b).mulVec x = b.equivFun.symm x := by
  rw [b.equivFun_symm_apply]
  ext i
  simp [basisMatrix, Matrix.mulVec, dotProduct, mul_comm]

theorem basisMatrix_injective (b : Basis (Fin n) K (Fin n → K)) :
    Function.Injective (basisMatrix b).mulVec := by
  intro x y h
  apply b.equivFun.symm.injective
  simpa only [basisMatrix_mulVec_eq] using h

theorem polarization_in_coordinates
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (b : Basis (Fin n) K (Fin n → K)) (i j l : Fin n) :
    coeff 0 (pderiv l (pderiv j (pderiv i
      (PolynomialRestriction.restrict (basisMatrix b) F)))) =
      polarization F (b i) (b j) (b l) := by
  classical
  let Q := PolynomialRestriction.restrict (basisMatrix b) F
  have hQ : Q.IsHomogeneous 3 := PolynomialRestriction.homogeneous_restrict _ _ hF
  have he := hessian_entry_expansion hQ (Pi.single l 1) i j
  have he' : hessian Q (Pi.single l 1) i j =
      coeff 0 (pderiv l (pderiv j (pderiv i Q))) := by
    simpa [Pi.single_apply] using he
  rw [← he']
  change hessian (PolynomialRestriction.restrict (basisMatrix b) F) _ i j = _
  rw [PolynomialRestriction.hessian_restrict, basisMatrix_mulVec_single]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, basisMatrix,
    polarization, dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  ring

end HessianTheorem11
