import HessianTheorem11.SaturatedFourDimensionalData

/-! The scalar moment identities of the actual four-dimensional maps,
obtained from the matrix coefficients of the saturated Hessian resolvent. -/
noncomputable section
namespace HessianTheorem11
open Matrix Module

theorem mulVecLin_pow_apply {K : Type*} [CommRing K] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (N : Matrix ι ι K) (j : ℕ) (v : ι → K) :
    (N.mulVecLin^j) v = (N^j).mulVec v := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ',Module.End.mul_apply,ih,pow_succ',← Matrix.mulVec_mulVec]
    rfl

theorem matrix_sandwich_diagonal {K : Type*} [CommRing K]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E : Matrix ι κ K) (N : Matrix κ κ K) (i : ι) :
    (E*N*E.transpose) i i = dotProduct (E i) (N.mulVec (E i)) := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.mulVec,dotProduct]

namespace CoisotropicBasis.Data
variable {F : GeometricPolynomial 13} {x : GeometricPoint 13}
  {T : Submodule GeometricField (GeometricPoint 13)}
  (D : Data (hessianBilinear F x) T x 5 2 4)

theorem four_moment_of_resolvent (hF : F.IsHomogeneous 3) (eta : Fin 2)
    (a : GeometricPoint 5) (j : ℕ)
    (h : D.resolventMoment (D.radicalMatrix.mulVec a) j = 0) :
    D.fourBeta (D.fourE hF eta a) (((D.fourM hF a)^j) (D.fourE hF eta a)) = 0 := by
  let E := D.mixedGramAt (D.radicalMatrix.mulVec a)
  let N := D.middleGram⁻¹ * D.middleGramAt (D.radicalMatrix.mulVec a)
  have hh : dotProduct (E eta)
      (((-N)^j).mulVec (D.middleGram⁻¹.mulVec (E eta))) = 0 := by
    have he := congrFun (congrFun h eta) eta
    change (E*(-N)^j*D.middleGram⁻¹*E.transpose) eta eta=0 at he
    rw [Matrix.mul_assoc E, matrix_sandwich_diagonal, ← Matrix.mulVec_mulVec] at he
    exact he
  change D.fourBeta (D.middleGram⁻¹.mulVec (E eta))
    ((N.mulVecLin^j) (D.middleGram⁻¹.mulVec (E eta))) = 0
  rw [D.fourBeta_inverse_left,mulVecLin_pow_apply]
  rcases Nat.even_or_odd j with hj|hj
  · simpa only [hj.neg_pow] using hh
  · simpa only [hj.neg_pow,Matrix.neg_mulVec,dotProduct_neg,neg_eq_zero] using hh

theorem four_moments (GR : GenericRankOpenInput) (hF : F.IsHomogeneous 3)
    (hker : LinearMap.ker (hessian F x).mulVecLin ≤ T)
    (hann : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0)
    (hdom : geometricClosure (gradient F ''
      (LinearMap.ker (hessian F x).mulVecLin : Set (GeometricPoint 13))) =
      ((coordinatePairing (K := GeometricField) (n := 13)).orthogonal T : Set (GeometricPoint 13)))
    (Z : Set (GeometricPoint 13))
    (hmax : ∀ y ∈ Z, (hessian F y).rank ≤ (hessian F x).rank)
    (hsat : ∀ t : GeometricField, ∀ a ∈ LinearMap.ker (hessian F x).mulVecLin,
      x+t • a ∈ Z) (eta : Fin 2) (a : GeometricPoint 5) (j : ℕ) :
    D.fourBeta (D.fourE hF eta a) (((D.fourM hF a)^j) (D.fourE hF eta a)) = 0 :=
  D.four_moment_of_resolvent hF eta a j
    ((D.cubic_saturated_schur_identities GR hF hker hann hdom Z hmax hsat _
      (D.radicalMatrix_mem_kernel a)).2 j)

end CoisotropicBasis.Data
end HessianTheorem11
