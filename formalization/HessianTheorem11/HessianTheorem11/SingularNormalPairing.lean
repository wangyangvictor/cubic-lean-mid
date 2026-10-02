import HessianTheorem11.SingularPositiveNormalForm
import HessianTheorem11.NormalPairingCoordinates
import HessianTheorem11.TangentHessianRank

/-! The actual normal-map relation for a smooth singular component whose
 tangent space equals the Hessian kernel. The tuple is extracted from the
 original cubic, including its positive-weight remainder. -/

noncomputable section
namespace HessianTheorem11.SingularNormalPairing
open MvPolynomial Module Matrix PolynomialRestriction
open SingularRadialNormalForm SingularPositiveNormalForm SingularNormalEquations
open SingularRadialEquality NonzeroLimitTransport

variable {n : ℕ}

def blockExtension (T : Finset (Fin n)) (a : (↑T : Type) → GeometricField) : GeometricPoint n :=
  fun i => if h : i ∈ T then a ⟨i,h⟩ else 0

@[simp] theorem blockExtension_coe (T : Finset (Fin n))
    (a : (↑T : Type) → GeometricField) (i : (↑T : Type)) :
    blockExtension T a i = a i := by simp [blockExtension, i.property]

theorem blockExtension_zero (T : Finset (Fin n))
    (a : (↑T : Type) → GeometricField) (i : Fin n) (hi : i ∉ T) :
    blockExtension T a i = 0 := by simp [blockExtension, hi]

theorem gradient_restrict (B : Matrix (Fin n) (Fin n) GeometricField)
    (F : GeometricPolynomial n) (y : GeometricPoint n) :
    gradient (restrict B F) y = B.transpose.mulVec (gradient F (B.mulVec y)) := by
  ext i
  simp only [gradient, pderiv_restrict, map_sum, map_mul, eval_C, eval_restrict,
    Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem blockExtension_in_tangent
    (T : Submodule GeometricField (GeometricPoint n))
    (L : Submodule GeometricField (GeometricPoint n)) (x : GeometricPoint n)
    (A : AdaptedFlagBasis T L x)
    (a : (↑(A.tangentIndices.erase A.radial) : Type) → GeometricField) :
    (HessianTheorem11.basisMatrix A.basis).mulVec
      (blockExtension (A.tangentIndices.erase A.radial) a) ∈ T := by
  let y := blockExtension (A.tangentIndices.erase A.radial) a
  have he : (HessianTheorem11.basisMatrix A.basis).mulVec y = ∑ i, y i • A.basis i := by
    ext j
    simp [HessianTheorem11.basisMatrix, Matrix.mulVec, dotProduct, mul_comm]
  rw [he]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : i ∈ A.tangentIndices.erase A.radial
  · exact T.smul_mem _ ((A.mem_tangent_iff i).mpr (Finset.mem_of_mem_erase hi))
  · have hy : y i = 0 := blockExtension_zero _ a i hi
    simp [hy]

theorem transpose_renaming_mulVec_coe
    (T : Finset (Fin n)) (p : (↑T : Type) → GeometricField) (i : (↑T : Type)) :
    (QuadraticBlockRank.renamingMatrix (fun j : (↑T : Type) => (j : Fin n))).transpose.mulVec p i = p i := by
  classical
  change (∑ j : (↑T : Type), (if (i : Fin n) = (j : Fin n) then 1 else 0) * p j) = p i
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    have hij : (i : Fin n) ≠ (j : Fin n) := fun he => hj (Subtype.ext he.symm)
    simp [hij]
  · simp

theorem transpose_renaming_mulVec_zero
    (T : Finset (Fin n)) (p : (↑T : Type) → GeometricField) (i : Fin n) (hi : i ∉ T) :
    (QuadraticBlockRank.renamingMatrix (fun j : (↑T : Type) => (j : Fin n))).transpose.mulVec p i = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro j _
  have hij : i ≠ (j : Fin n) := by rintro rfl; exact hi j.property
  simp [QuadraticBlockRank.renamingMatrix, Matrix.transpose_apply, hij]

/-- The extracted normal tuple satisfies the actual inverse-Hessian
quadric equation. Only universal smooth-arc lifting is used as AG input. -/
theorem typed_normal_quadratic_relation
    (SA : FormalSmoothArcInput)
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (Z : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z)
    (hirred : GeometricallyIrreducible Z) (hsing : ∀ z ∈ Z, gradient F z = 0)
    (x : GeometricPoint n) (hx : x ∈ Z)
    (hdim : affineDimension Z = (finrank GeometricField (affineTangentSpace Z x) : Dimension))
    (A : AdaptedFlagBasis (affineTangentSpace Z x) (LinearMap.ker (hessian F x).mulVecLin) x)
    (hT : affineTangentSpace Z x = LinearMap.ker (hessian F x).mulVecLin)
    (htensor : ∀ t ∈ affineTangentSpace Z x,
      ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0)
    (q : MvPolynomial (↑A.tangentIndicesᶜ : Type) GeometricField)
    (p : (↑A.tangentIndicesᶜ : Type) →
      MvPolynomial (↑(A.tangentIndices.erase A.radial) : Type) GeometricField)
    (hqe : rename (fun i : (↑A.tangentIndicesᶜ : Type) => (i : Fin n)) q =
      normalQuadratic
        (zeroWeightPart (restrict (HessianTheorem11.basisMatrix A.basis) F)
          (singularRadialWeight A.radial A.tangentIndices A.tangentIndices)) A.radial)
    (hpe : ∀ i, rename (fun j : (↑(A.tangentIndices.erase A.radial) : Type) => (j : Fin n)) (p i) =
      normalMapComponent
        (zeroWeightPart (restrict (HessianTheorem11.basisMatrix A.basis) F)
          (singularRadialWeight A.radial A.tangentIndices A.tangentIndices))
        A.radial A.tangentIndices i) :
    TangentHessianRank.quadraticRelation (quadraticHessian q)⁻¹ p = 0 := by
  classical
  let B := HessianTheorem11.basisMatrix A.basis
  let P := restrict B F
  let R := QuadraticBlockRank.renamingMatrix
    (K := GeometricField) (fun i : (↑A.tangentIndicesᶜ : Type) => (i : Fin n))
  let Q := quadraticHessian q
  have hR : R * R.transpose = 1 := renamingMatrix_mul_transpose _ Subtype.val_injective
  have hQ : Q.det ≠ 0 := typed_normal_det_ne_zero_in_adapted_flag F hF x _ A hT htensor q hqe
  have hP : P.IsHomogeneous 3 := homogeneous_restrict _ _ hF
  have hW := nonnegative_in_adapted_flag F hF x _ A htensor
  rw [← adapted_indices_eq_of_tangent_eq_kernel F x _ A hT] at hW
  have hH : B.transpose * hessian F x * B = R.transpose * Q * R := by
    have he := QuadraticBlockRank.quadraticHessian_restrict R q
    rw [QuadraticBlockRank.restrict_renamingMatrix, hqe] at he
    change LocalCubicNormalForm.quadraticMatrix
      (normalQuadratic (zeroWeightPart P _) A.radial) = R.transpose * Q * R at he
    rw [retained_normalQuadratic_hessian P hP A.radial A.tangentIndices A.radial_mem hW,
      PolynomialRestriction.hessian_restrict,
      HessianTheorem11.basisMatrix_mulVec_single, A.radial_eq] at he
    exact he
  apply MvPolynomial.funext
  intro a
  let y := blockExtension (A.tangentIndices.erase A.radial) a
  let v := B.mulVec y
  have hv : v ∈ affineTangentSpace Z x := blockExtension_in_tangent _ _ x A a
  have hy (i : Fin n) (hi : i ∈ A.tangentIndicesᶜ) : y i = 0 := by
    apply blockExtension_zero
    intro hm
    exact Finset.mem_compl.mp hi (Finset.mem_of_mem_erase hm)
  have hyr : y A.radial = 0 := blockExtension_zero _ a _ (Finset.notMem_erase _ _)
  have hp : B.transpose.mulVec (gradient F v) =
      R.transpose.mulVec (fun i => eval a (p i)) := by
    ext i
    by_cases hi : i ∈ A.tangentIndicesᶜ
    · have hn := normal_partial_on_tangent P hP A.radial A.tangentIndices A.radial_mem hW y hy hyr i hi
      have hg := congrFun (gradient_restrict B F y) i
      change eval y (pderiv i P) = (B.transpose.mulVec (gradient F v)) i at hg
      rw [← hg, hn, ← hpe ⟨i,hi⟩]
      have hev : eval y (rename (fun j : (↑(A.tangentIndices.erase A.radial) : Type) =>
          (j : Fin n)) (p ⟨i,hi⟩)) = eval a (p ⟨i,hi⟩) := by
        rw [eval_rename]
        have hya : (y ∘ fun j : (↑(A.tangentIndices.erase A.radial) : Type) => (j : Fin n)) = a := by
          funext j
          exact blockExtension_coe _ a j
        rw [hya]
      rw [hev]
      exact (transpose_renaming_mulVec_coe A.tangentIndicesᶜ
        (fun i => eval a (p i)) ⟨i,hi⟩).symm
    · have hit : i ∈ A.tangentIndices := Finset.notMem_compl.mp hi
      have hk : (hessian F x).mulVec (A.basis i) = 0 :=
        hT.le ((A.mem_tangent_iff i).mpr hit)
      obtain ⟨z,hz⟩ := SingularFormalArc.gradient_tangent_mem_hessian_range
        SA F hF Z hZ hirred hsing x hx hdim v hv
      have hz' : (hessian F x).mulVec z = gradient F v := hz
      have he : (B.transpose.mulVec (gradient F v)) i = 0 := by
        change dotProduct (A.basis i) (gradient F v) = 0
        rw [← hz', Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hessian_symmetric, hk]
        simp
      rw [he]
      exact (transpose_renaming_mulVec_zero A.tangentIndicesᶜ (fun i => eval a (p i)) i hi).symm
  have he := singular_normal_coordinate_quadratic_relation SA F hF Z hZ hirred hsing x hx hdim
    v hv A.basis R hR Q hQ hH (fun i => eval a (p i)) hp
  simpa only [TangentHessianRank.quadraticRelation, map_sum, map_mul, eval_C, map_zero,
    dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, mul_left_comm] using he

end HessianTheorem11.SingularNormalPairing
