import HessianTheorem11.SaturatedHessianPencil
import HessianTheorem11.QuadraticGenericRank
import HessianTheorem11.QuadraticLowImage
import HessianTheorem11.PolynomialSchurVanishing

/-! Coordinates on the actual radical block of the saturated Hessian basis. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix Module PolynomialRestriction
namespace CoisotropicBasis.Data
variable {n m d q : ℕ} {F : GeometricPolynomial n} {x : GeometricPoint n}
  {T : Submodule GeometricField (GeometricPoint n)}
  (D : Data (hessianBilinear F x) T x m d q)

def radicalMatrix : Matrix (Fin n) (Fin m) GeometricField :=
  fun i j => D.radicalVector j i

theorem radicalMatrix_mulVec (a : GeometricPoint m) :
    D.radicalMatrix.mulVec a = D.basis.equivFun.symm (Sum.elim a 0) := by
  rw [← BasisHessianTransport.basisMatrix_mulVec_eq]
  ext i
  simp [radicalMatrix, radicalVector, Matrix.mulVec, dotProduct,
    BasisHessianTransport.basisMatrix, Fintype.sum_sum_type]

theorem radicalMatrix_injective : Function.Injective D.radicalMatrix.mulVec := by
  intro u v h
  rw [D.radicalMatrix_mulVec, D.radicalMatrix_mulVec] at h
  have he := D.basis.equivFun.symm.injective h
  funext i
  exact congrFun he (Sum.inl i)

theorem radicalMatrix_mem_kernel (a : GeometricPoint m) :
    D.radicalMatrix.mulVec a ∈ LinearMap.ker (hessian F x).mulVecLin := by
  have he : D.radicalMatrix.mulVec a = ∑ i, a i • D.radicalVector i := by
    ext j
    simp [radicalMatrix, Matrix.mulVec, dotProduct, mul_comm]
  rw [he]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (D.radical_hessian_kernel i)

theorem radicalMatrix_range : LinearMap.range D.radicalMatrix.mulVecLin =
    LinearMap.ker (hessian F x).mulVecLin := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro a ⟨v,rfl⟩
    exact D.radicalMatrix_mem_kernel v
  · have hi := LinearMap.finrank_range_of_inj (f := D.radicalMatrix.mulVecLin)
      D.radicalMatrix_injective
    have hd := D.radical_dimension
    rw [ker_hessianBilinear] at hd
    simpa using hi.trans (by simpa using hd)

def radicalGradient : Fin n → GeometricPolynomial m :=
  fun i => restrict D.radicalMatrix (pderiv i F)

theorem radicalGradient_homogeneous (hF : F.IsHomogeneous 3) (i : Fin n) :
    (D.radicalGradient i).IsHomogeneous 2 := homogeneous_restrict _ _ hF.pderiv

theorem radicalGradient_value (a : GeometricPoint m) :
    polynomialMap D.radicalGradient a = gradient F (D.radicalMatrix.mulVec a) := by
  ext i
  exact eval_restrict _ _ _

theorem radicalGradient_image : polynomialMap D.radicalGradient '' Set.univ =
    gradient F '' (LinearMap.ker (hessian F x).mulVecLin : Set (GeometricPoint n)) := by
  have he : polynomialMap D.radicalGradient = gradient F ∘ D.radicalMatrix.mulVec :=
    funext D.radicalGradient_value
  rw [he, Set.image_comp, Set.image_univ]
  have hr : Set.range D.radicalMatrix.mulVec =
      (LinearMap.ker (hessian F x).mulVecLin : Set (GeometricPoint n)) :=
    congrArg (fun S : Submodule GeometricField (GeometricPoint n) => (S : Set (GeometricPoint n)))
      D.radicalMatrix_range
  rw [hr]

theorem radicalGradient_jacobian (hF : F.IsHomogeneous 3) (a : GeometricPoint m) :
    quadraticJacobianLinearMap D.radicalGradient (D.radicalGradient_homogeneous hF) a =
      hessian F (D.radicalMatrix.mulVec a) * D.radicalMatrix := by
  have h := quadraticJacobian_restrict (fun i => pderiv i F)
    (fun i => hF.pderiv) D.radicalMatrix a
  exact h

theorem rank_basisTranspose_mul {r : ℕ} (M : Matrix (Fin n) (Fin r) GeometricField) :
    ((BasisHessianTransport.basisMatrix D.basis).transpose * M).rank = M.rank := by
  classical
  let B := BasisHessianTransport.basisMatrix D.basis
  let N := D.basis.toMatrix (Pi.basisFun GeometricField (Fin n))
  have hBN : B*N = 1 := by
    rw [show B = (Pi.basisFun GeometricField (Fin n)).toMatrix D.basis from
      BasisHessianTransport.basisMatrix_eq_toMatrix D.basis]
    exact (Pi.basisFun GeometricField (Fin n)).toMatrix_mul_toMatrix_flip D.basis
  apply le_antisymm (Matrix.rank_mul_le_right _ _)
  have he : N.transpose * (B.transpose * M) = M := by
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, hBN, Matrix.transpose_one, Matrix.one_mul]
  calc
    M.rank = (N.transpose * (B.transpose * M)).rank := congrArg Matrix.rank he.symm
    _ ≤ (B.transpose * M).rank := Matrix.rank_mul_le_right _ _

theorem radicalGram_eq_basisTranspose_hessian (a : GeometricPoint n) :
    (D.gramAt a).submatrix id Sum.inl =
      (BasisHessianTransport.basisMatrix D.basis).transpose *
        (hessian F a * D.radicalMatrix) := by
  rw [D.gramAt_eq_congruence, Matrix.mul_assoc]
  rfl

theorem normalCross_rank_eq_radicalGram (hF : F.IsHomogeneous 3)
    (hker : LinearMap.ker (hessian F x).mulVecLin ≤ T)
    (hann : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0)
    (a : GeometricPoint n) (ha : a ∈ LinearMap.ker (hessian F x).mulVecLin) :
    (D.normalCross a).rank = ((D.gramAt a).submatrix id Sum.inl).rank := by
  classical
  let Q := (D.gramAt a).submatrix id Sum.inl
  let f : Fin d → CoisotropicBasis.Index m d q := fun j => Sum.inr (Sum.inr (Sum.inr j))
  let R : Matrix (CoisotropicBasis.Index m d q) (Fin d) GeometricField :=
    (1 : Matrix (CoisotropicBasis.Index m d q) (CoisotropicBasis.Index m d q) GeometricField).submatrix id f
  have hsub : Q.submatrix f id = (D.normalCross a).transpose := by
    ext i j
    exact polarization_swap_first F _ _ a
  have hQ : Q = R * (D.normalCross a).transpose := by
    rw [show Q = (D.gramAt a).submatrix id Sum.inl from rfl,
      D.gramAt_radical hF hker hann a ha]
    ext i j
    rcases i with i | (i | (i | i)) <;>
      simp [R,f,Matrix.mul_apply,Matrix.submatrix,Matrix.one_apply,crossAt]
  rw [← Matrix.rank_transpose (D.normalCross a)]
  apply le_antisymm
  · rw [← hsub]
    exact PolynomialSchurVanishing.rank_submatrix_le Q f id
  · change Q.rank ≤ (D.normalCross a).transpose.rank
    rw [hQ]
    exact Matrix.rank_mul_le_right _ _

theorem normalCross_rank_eq_radicalGradient_jacobian (hF : F.IsHomogeneous 3)
    (hker : LinearMap.ker (hessian F x).mulVecLin ≤ T)
    (hann : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0)
    (a : GeometricPoint m) :
    (D.normalCross (D.radicalMatrix.mulVec a)).rank =
      (quadraticJacobianLinearMap D.radicalGradient (D.radicalGradient_homogeneous hF) a).rank := by
  rw [D.normalCross_rank_eq_radicalGram hF hker hann _ (D.radicalMatrix_mem_kernel a),
    D.radicalGram_eq_basisTranspose_hessian, D.rank_basisTranspose_mul,
    D.radicalGradient_jacobian hF]

end CoisotropicBasis.Data
end HessianTheorem11
