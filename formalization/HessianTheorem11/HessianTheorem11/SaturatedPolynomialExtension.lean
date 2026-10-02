import HessianTheorem11.NormalCrossGenericRank

/-! Actual polynomial expressions extend the saturated Schur identities
from the dense full-rank locus to every radical vector. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix Module
namespace CoisotropicBasis.Data
variable {n m d q : ℕ} {F : GeometricPolynomial n} {x : GeometricPoint n}
  {T : Submodule GeometricField (GeometricPoint n)}
  (D : Data (hessianBilinear F x) T x m d q)

def complementGramPolynomial : Matrix (CoisotropicBasis.NondegenerateIndex d q)
    (CoisotropicBasis.NondegenerateIndex d q) (GeometricPolynomial m) :=
  fun i j => ∑ k, C (polarization F (D.complementVector i) (D.complementVector j)
    (D.radicalVector k)) * X k

theorem eval_complementGramPolynomial (hF : F.IsHomogeneous 3) (a : GeometricPoint m) :
    D.complementGramPolynomial.map (eval a) = D.complementGramAt (D.radicalMatrix.mulVec a) := by
  classical
  have ha : D.radicalMatrix.mulVec a = ∑ i, a i • D.radicalVector i := by
    ext j
    simp [radicalMatrix, Matrix.mulVec, dotProduct, mul_comm]
  ext i j
  simp only [Matrix.map_apply, complementGramPolynomial, map_sum, map_mul, eval_C, eval_X,
    complementGramAt, ha, polarization_sum_third Finset.univ hF,
    polarization_smul_third hF]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

def isotropicGramAt (a : GeometricPoint n) : Matrix (Fin d) (Fin d) GeometricField :=
  (D.complementGramAt a).submatrix (fun i => Sum.inr (Sum.inl i))
    (fun i => Sum.inr (Sum.inl i))

def mixedGramAt (a : GeometricPoint n) : Matrix (Fin d) (Fin q) GeometricField :=
  (D.complementGramAt a).submatrix (fun i => Sum.inr (Sum.inl i)) Sum.inl

def middleGramAt (a : GeometricPoint n) : Matrix (Fin q) (Fin q) GeometricField :=
  (D.complementGramAt a).submatrix Sum.inl Sum.inl

def resolventMomentPolynomial (j : ℕ) : Matrix (Fin d) (Fin d) (GeometricPolynomial m) :=
  let E := D.complementGramPolynomial.submatrix (fun i => Sum.inr (Sum.inl i)) Sum.inl
  let Q := D.complementGramPolynomial.submatrix Sum.inl Sum.inl
  let B := D.middleGram⁻¹.map C
  E * (-(B*Q))^j * B * E.transpose

def resolventMoment (a : GeometricPoint n) (j : ℕ) : Matrix (Fin d) (Fin d) GeometricField :=
  D.mixedGramAt a * (-(D.middleGram⁻¹ * D.middleGramAt a))^j *
    D.middleGram⁻¹ * (D.mixedGramAt a).transpose

set_option maxHeartbeats 1000000 in
theorem eval_resolventMomentPolynomial (hF : F.IsHomogeneous 3) (a : GeometricPoint m) (j : ℕ) :
    (D.resolventMomentPolynomial j).map (eval a) =
      D.resolventMoment (D.radicalMatrix.mulVec a) j := by
  have hn (M : Matrix (Fin q) (Fin q) (GeometricPolynomial m)) :
      (-M).map (eval a) = -(M.map (eval a)) := by ext i k; simp
  have hc (M : Matrix (Fin q) (Fin q) GeometricField) :
      (M.map C).map (eval a) = M := by ext i k; simp
  simp only [resolventMomentPolynomial, resolventMoment, mixedGramAt, middleGramAt,
    Matrix.map_mul, Matrix.map_pow, hn, Matrix.transpose_map,
    ← Matrix.submatrix_map, hc,
    D.eval_complementGramPolynomial hF]

theorem isotropicGram_zero_of_generic (GR : GenericRankOpenInput)
    (hF : F.IsHomogeneous 3)
    (hker : LinearMap.ker (hessian F x).mulVecLin ≤ T)
    (hann : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0)
    (hdom : geometricClosure (gradient F ''
      (LinearMap.ker (hessian F x).mulVecLin : Set (GeometricPoint n))) =
      ((coordinatePairing (K := GeometricField) (n := n)).orthogonal T : Set (GeometricPoint n)))
    (hgeneric : ∀ a : GeometricPoint m,
      (D.normalCross (D.radicalMatrix.mulVec a)).rank = d →
      D.isotropicGramAt (D.radicalMatrix.mulVec a) = 0)
    (a : GeometricPoint n) (ha : a ∈ LinearMap.ker (hessian F x).mulVecLin) :
    D.isotropicGramAt a = 0 := by
  have hp (i j : Fin d) : D.complementGramPolynomial (Sum.inr (Sum.inl i))
      (Sum.inr (Sum.inl j)) = 0 := by
    apply D.polynomial_identity_of_full_normalCross_rank GR hF hker hann hdom
    intro b hb
    have he := congrFun (congrFun (D.eval_complementGramPolynomial hF b)
      (Sum.inr (Sum.inl i))) (Sum.inr (Sum.inl j))
    change eval b _ = _ at he
    rw [he]
    exact congrFun (congrFun (hgeneric b hb) i) j
  rw [← D.radicalMatrix_range] at ha
  obtain ⟨b,rfl⟩ := ha
  ext i j
  have he := congrFun (congrFun (D.eval_complementGramPolynomial hF b)
    (Sum.inr (Sum.inl i))) (Sum.inr (Sum.inl j))
  change eval b _ = _ at he
  rw [hp, map_zero] at he
  exact he.symm

theorem resolventMoment_zero_of_generic (GR : GenericRankOpenInput)
    (hF : F.IsHomogeneous 3)
    (hker : LinearMap.ker (hessian F x).mulVecLin ≤ T)
    (hann : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0)
    (hdom : geometricClosure (gradient F ''
      (LinearMap.ker (hessian F x).mulVecLin : Set (GeometricPoint n))) =
      ((coordinatePairing (K := GeometricField) (n := n)).orthogonal T : Set (GeometricPoint n)))
    (j : ℕ)
    (hgeneric : ∀ a : GeometricPoint m,
      (D.normalCross (D.radicalMatrix.mulVec a)).rank = d →
      D.resolventMoment (D.radicalMatrix.mulVec a) j = 0)
    (a : GeometricPoint n) (ha : a ∈ LinearMap.ker (hessian F x).mulVecLin) :
    D.resolventMoment a j = 0 := by
  have hp (i k : Fin d) : D.resolventMomentPolynomial j i k = 0 := by
    apply D.polynomial_identity_of_full_normalCross_rank GR hF hker hann hdom
    intro b hb
    have he := congrFun (congrFun (D.eval_resolventMomentPolynomial hF b j) i) k
    change eval b _ = _ at he
    rw [he]
    exact congrFun (congrFun (hgeneric b hb) i) k
  rw [← D.radicalMatrix_range] at ha
  obtain ⟨b,rfl⟩ := ha
  ext i k
  have he := congrFun (congrFun (D.eval_resolventMomentPolynomial hF b j) i) k
  change eval b _ = _ at he
  rw [hp, map_zero] at he
  exact he.symm

end CoisotropicBasis.Data
end HessianTheorem11
