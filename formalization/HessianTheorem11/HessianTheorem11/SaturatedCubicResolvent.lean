import HessianTheorem11.SaturatedPolynomialExtension
import HessianTheorem11.SaturatedPencilResolvent

/-! The source's saturated Schur identities, proved for actual cubic
Hessians from saturation and dominance, including extension to every vector. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix Module

theorem exists_left_inverse_of_full_column_rank
    {K : Type*} [Field K] {m d : ℕ} (P : Matrix (Fin m) (Fin d) K) (hP : P.rank = d) :
    ∃ L : Matrix (Fin d) (Fin m) K, L*P=1 := by
  classical
  have hs : Function.Surjective P.transpose.mulVecLin := by
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    change P.transpose.rank = finrank K (Fin d → K)
    simpa using hP
  choose u hu using fun i : Fin d => hs (Pi.single i 1)
  refine ⟨fun i j => u i j,?_⟩
  ext i j
  have he := congrFun (hu i) j
  simpa [Matrix.mul_apply, Matrix.mulVecLin_apply, Matrix.mulVec, Matrix.vecMul, dotProduct,
    Matrix.one_apply, Pi.single_apply, eq_comm, mul_comm] using he

namespace CoisotropicBasis.Data
variable {n m d q : ℕ} {F : GeometricPolynomial n} {x : GeometricPoint n}
  {T : Submodule GeometricField (GeometricPoint n)}
  (D : Data (hessianBilinear F x) T x m d q)

theorem complementGramAt_symmetric (a : GeometricPoint n) : (D.complementGramAt a).IsSymm := by
  ext i j
  exact polarization_swap_first F _ _ a

theorem middle_isotropic_eq_mixed_transpose (a : GeometricPoint n) :
    (D.complementGramAt a).submatrix Sum.inl (fun i => Sum.inr (Sum.inl i)) =
      (D.mixedGramAt a).transpose := by
  ext i j
  exact polarization_swap_first F _ _ a

theorem cubic_pencil_schur_generic
    (hF : F.IsHomogeneous 3)
    (hker : LinearMap.ker (hessian F x).mulVecLin ≤ T)
    (hann : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0)
    (Z : Set (GeometricPoint n))
    (hmax : ∀ y ∈ Z, (hessian F y).rank ≤ (hessian F x).rank)
    (hsat : ∀ t : GeometricField, ∀ a ∈ LinearMap.ker (hessian F x).mulVecLin,
      x+t • a ∈ Z)
    (a : GeometricPoint n) (ha : a ∈ LinearMap.ker (hessian F x).mulVecLin)
    (hP : (D.normalCross a).rank = d) :
    D.isotropicGramAt a = 0 ∧ ∀ j, D.resolventMoment a j = 0 := by
  obtain ⟨L,hL⟩ := exists_left_inverse_of_full_column_rank (D.normalCross a) hP
  have hrank (t : GeometricField) :
      (fromBlocks (0 : Matrix (Fin m) (Fin m) GeometricField)
        (t • SaturatedResolvent.cross (α := Fin q) (D.normalCross a))
        (t • (SaturatedResolvent.cross (α := Fin q) (D.normalCross a)).transpose)
        (SaturatedResolvent.initial D.middleGram+t • D.complementGramAt a)).rank ≤
          Fintype.card (Fin q ⊕ (Fin d ⊕ Fin d)) := by
    have h := D.exact_saturated_pencil_rank_le hF hker hann Z hmax hsat a ha t
    rw [D.complementGramAt_base] at h
    simpa only [SaturatedResolvent.initial, SaturatedResolvent.cross,
      crossAt, Matrix.fromCols, Fintype.card_sum, Fintype.card_fin, two_mul, add_assoc] using h
  refine ⟨(SaturatedResolvent.resolvent_of_pencil_rank D.middleGram D.middleGram_det_ne_zero
    (D.complementGramAt a) (D.normalCross a) L hL hrank).1,?_⟩
  intro j
  have h := SaturatedResolvent.resolvent_coefficients_of_pencil_rank D.middleGram
    D.middleGram_det_ne_zero (D.complementGramAt a) (D.normalCross a) L hL hrank j
  rw [D.middle_isotropic_eq_mixed_transpose] at h
  exact h

theorem cubic_saturated_schur_identities (GR : GenericRankOpenInput)
    (hF : F.IsHomogeneous 3)
    (hker : LinearMap.ker (hessian F x).mulVecLin ≤ T)
    (hann : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0)
    (hdom : geometricClosure (gradient F ''
      (LinearMap.ker (hessian F x).mulVecLin : Set (GeometricPoint n))) =
      ((coordinatePairing (K := GeometricField) (n := n)).orthogonal T : Set (GeometricPoint n)))
    (Z : Set (GeometricPoint n))
    (hmax : ∀ y ∈ Z, (hessian F y).rank ≤ (hessian F x).rank)
    (hsat : ∀ t : GeometricField, ∀ a ∈ LinearMap.ker (hessian F x).mulVecLin,
      x+t • a ∈ Z)
    (a : GeometricPoint n) (ha : a ∈ LinearMap.ker (hessian F x).mulVecLin) :
    D.isotropicGramAt a = 0 ∧ ∀ j, D.resolventMoment a j = 0 := by
  constructor
  · apply D.isotropicGram_zero_of_generic GR hF hker hann hdom _ a ha
    intro b hb
    exact (D.cubic_pencil_schur_generic hF hker hann Z hmax hsat _
      (D.radicalMatrix_mem_kernel b) hb).1
  · intro j
    apply D.resolventMoment_zero_of_generic GR hF hker hann hdom j _ a ha
    intro b hb
    exact (D.cubic_pencil_schur_generic hF hker hann Z hmax hsat _
      (D.radicalMatrix_mem_kernel b) hb).2 j

end CoisotropicBasis.Data
end HessianTheorem11
