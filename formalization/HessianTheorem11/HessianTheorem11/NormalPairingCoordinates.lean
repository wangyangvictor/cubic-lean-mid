import HessianTheorem11.SingularFormalArc
import HessianTheorem11.BasisHessianTransport
import HessianTheorem11.QuadraticBlockRank

/-! Transport of the proved formal-arc quadratic relation into an actual
nondegenerate normal coordinate block. No transport of the singular
component or of its tangent space is assumed. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix Module

theorem basis_congruence_injective {n : ℕ}
    (b : Basis (Fin n) GeometricField (GeometricPoint n)) :
    Function.Injective (fun H : Matrix (Fin n) (Fin n) GeometricField =>
      (BasisHessianTransport.basisMatrix b).transpose * H * BasisHessianTransport.basisMatrix b) := by
  let B := BasisHessianTransport.basisMatrix b
  let C := b.toMatrix (Pi.basisFun GeometricField (Fin n))
  have hBC : B * C = 1 := by
    rw [show B = (Pi.basisFun GeometricField (Fin n)).toMatrix b from
      BasisHessianTransport.basisMatrix_eq_toMatrix b]
    exact (Pi.basisFun GeometricField (Fin n)).toMatrix_mul_toMatrix_flip b
  have hrecover (H : Matrix (Fin n) (Fin n) GeometricField) :
      C.transpose * (B.transpose * H * B) * C = H := by
    calc
      _ = (B * C).transpose * H * (B * C) := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
      _ = H := by rw [hBC, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  intro H J he
  have hh := congrArg (fun M => C.transpose * M * C) he
  change C.transpose * (B.transpose * H * B) * C = C.transpose * (B.transpose * J * B) * C at hh
  simpa only [hrecover] using hh

theorem renamingMatrix_mul_transpose
    {K σ τ : Type*} [Field K] [Fintype σ] [Fintype τ] [DecidableEq σ] [DecidableEq τ]
    (f : σ → τ) (hf : Function.Injective f) :
    QuadraticBlockRank.renamingMatrix (K := K) f *
      (QuadraticBlockRank.renamingMatrix (K := K) f).transpose = 1 := by
  ext i j
  simp [QuadraticBlockRank.renamingMatrix, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.one_apply, ite_mul, hf.eq_iff, eq_comm]

theorem normal_block_generalizedInverse
    {K σ τ : Type*} [Field K] [Fintype σ] [Fintype τ] [DecidableEq σ]
    (R : Matrix σ τ K) (hR : R * R.transpose = 1)
    (Q : Matrix σ σ K) (hQ : Q.det ≠ 0) :
    (R.transpose * Q * R) * (R.transpose * Q⁻¹ * R) * (R.transpose * Q * R) =
      R.transpose * Q * R := by
  calc
    _ = R.transpose * Q * (R * R.transpose) * Q⁻¹ * (R * R.transpose) * Q * R := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hR, Matrix.mul_one, Matrix.mul_one]
      rw [Matrix.mul_assoc R.transpose Q Q⁻¹,
        Matrix.mul_nonsing_inv Q (isUnit_iff_ne_zero.mpr hQ), Matrix.mul_one]

theorem generalizedInverse_from_normal_coordinates
    {n : ℕ} {σ : Type*} [Fintype σ] [DecidableEq σ]
    (b : Basis (Fin n) GeometricField (GeometricPoint n))
    (H : Matrix (Fin n) (Fin n) GeometricField)
    (R : Matrix σ (Fin n) GeometricField) (hR : R * R.transpose = 1)
    (Q : Matrix σ σ GeometricField) (hQ : Q.det ≠ 0)
    (hH : (BasisHessianTransport.basisMatrix b).transpose * H * BasisHessianTransport.basisMatrix b =
      R.transpose * Q * R) :
    H * (BasisHessianTransport.basisMatrix b * (R.transpose * Q⁻¹ * R) *
      (BasisHessianTransport.basisMatrix b).transpose) * H = H := by
  apply basis_congruence_injective b
  change (BasisHessianTransport.basisMatrix b).transpose *
    (H * (BasisHessianTransport.basisMatrix b * (R.transpose * Q⁻¹ * R) *
    (BasisHessianTransport.basisMatrix b).transpose) * H) *
    BasisHessianTransport.basisMatrix b =
    (BasisHessianTransport.basisMatrix b).transpose * H * BasisHessianTransport.basisMatrix b
  calc
    _ = ((BasisHessianTransport.basisMatrix b).transpose * H * BasisHessianTransport.basisMatrix b) *
        (R.transpose * Q⁻¹ * R) *
        ((BasisHessianTransport.basisMatrix b).transpose * H * BasisHessianTransport.basisMatrix b) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hH]; exact normal_block_generalizedInverse R hR Q hQ

theorem dotProduct_normal_coordinates
    {K σ τ υ : Type*} [Field K] [Fintype σ] [Fintype τ] [Fintype υ] [DecidableEq σ]
    (B : Matrix υ τ K) (R : Matrix σ τ K) (hR : R * R.transpose = 1)
    (Q : Matrix σ σ K) (g : υ → K) (p : σ → K)
    (hg : B.transpose.mulVec g = R.transpose.mulVec p) :
    dotProduct g ((B * (R.transpose * Q * R) * B.transpose).mulVec g) =
      dotProduct p (Q.mulVec p) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, hg]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hRp : R.mulVec (R.transpose.mulVec p) = p := by
    rw [Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]
  rw [hRp]
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.transpose_transpose,
    hRp]

/-- The actual typed inverse-pairing equation, obtained from the original
cubic's smooth singular component and actual normal-block coordinates. -/
theorem singular_normal_coordinate_quadratic_relation
    (SA : FormalSmoothArcInput) {n : ℕ}
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (Z : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z)
    (hirred : GeometricallyIrreducible Z) (hsing : ∀ z ∈ Z, gradient F z = 0)
    (x : GeometricPoint n) (hx : x ∈ Z)
    (hdim : affineDimension Z = (finrank GeometricField (affineTangentSpace Z x) : Dimension))
    (v : GeometricPoint n) (hv : v ∈ affineTangentSpace Z x)
    (b : Basis (Fin n) GeometricField (GeometricPoint n))
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (R : Matrix σ (Fin n) GeometricField) (hR : R * R.transpose = 1)
    (Q : Matrix σ σ GeometricField) (hQ : Q.det ≠ 0)
    (hH : (BasisHessianTransport.basisMatrix b).transpose * hessian F x *
      BasisHessianTransport.basisMatrix b = R.transpose * Q * R)
    (p : σ → GeometricField)
    (hp : (BasisHessianTransport.basisMatrix b).transpose.mulVec (gradient F v) =
      R.transpose.mulVec p) : dotProduct p (Q⁻¹.mulVec p) = 0 := by
  have hN := generalizedInverse_from_normal_coordinates b (hessian F x) R hR Q hQ hH
  have he := SingularFormalArc.gradient_quadratic_relation SA F hF Z hZ hirred hsing x hx hdim
    _ hN v hv
  rwa [dotProduct_normal_coordinates (BasisHessianTransport.basisMatrix b) R hR Q⁻¹
    (gradient F v) p hp] at he

end HessianTheorem11
