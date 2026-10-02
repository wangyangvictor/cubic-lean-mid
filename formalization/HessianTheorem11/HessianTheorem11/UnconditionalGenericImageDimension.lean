import HessianTheorem11.UnconditionalGenericImageAlgebra

/-! Generic differential rank equals the Krull dimension of the actual
polynomial image. The proof extends coordinate derivations through the
inclusion of function fields. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 160000
namespace HessianTheorem11.UnconditionalGeneric
open MvPolynomial Module ReducedTangentRank

variable {n m c : ℕ} (I : Ideal (GeometricPolynomial n)) [I.IsPrime]

def imageDerivationValues (P : Fin m → GeometricPolynomial n) :
    Derivation GeometricField (affineCoordinateRing I) (affineFunctionField I) →ₗ[affineFunctionField I]
      (Fin m → affineFunctionField I) where
  toFun D i := D (Ideal.Quotient.mk I (P i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The derivative values of image coordinate functions have rank equal to
the dimension of their actual coordinate-ring image. -/
theorem image_derivation_dimension (P : Fin m → GeometricPolynomial n) :
    ringKrullDim (affineCoordinateRing (polynomialImageIdeal I P)) =
      (finrank (affineFunctionField I) (LinearMap.range (imageDerivationValues I P)) : Dimension) := by
  let J := polynomialImageIdeal I P
  letI : J.IsPrime := (inferInstance : I.IsPrime).comap _
  let A := affineCoordinateRing I
  let B := affineCoordinateRing J
  let F := affineFunctionField I
  let E := FractionRing B
  let g : B →ₐ[GeometricField] A := polynomialImageCoordinateMap I P
  letI : Algebra B A := g.toAlgebra
  letI : IsScalarTower GeometricField B A := IsScalarTower.of_algHom g
  letI : IsScalarTower GeometricField B F :=
    IsScalarTower.to₁₂₄ GeometricField B A F
  have hginj : Function.Injective g := polynomialImageCoordinateMap_injective I P
  letI : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr hginj
  letI : FaithfulSMul B F := inferInstance
  letI : Algebra E F := FractionRing.liftAlgebra B F
  letI : IsScalarTower B E F := FractionRing.isScalarTower_liftAlgebra B F
  letI : IsScalarTower GeometricField E F :=
    IsScalarTower.to₁₃₄ GeometricField B E F
  letI : CharZero E := charZero_of_injective_algebraMap (algebraMap GeometricField E).injective
  let R := coordinateDerivationRestriction GeometricField B A F
  let V := coordinateDerivationValues J F
  have hR : Function.Surjective R :=
    coordinate_derivation_restriction_surjective GeometricField B A E F
  have hcomp : imageDerivationValues I P = V.comp R := by
    ext D i
    change D (Ideal.Quotient.mk I (P i)) =
      D (g (Ideal.Quotient.mk J (X i)))
    rw [polynomialImageCoordinateMap_X]
  have hdim := coordinate_derivation_dimension B F
  rw [hcomp,LinearMap.range_comp_of_range_eq_top V (LinearMap.range_eq_top.mpr hR),
    LinearMap.finrank_range_of_inj (coordinateDerivationValues_injective J F)]
  exact hdim

/-- Evaluation on representatives agrees with the actual polynomial
Jacobian derivation, despite quotient descent having been constructed by an
equivalence. -/
theorem genericJacobianDerivationEquiv_mk
    (f : Fin c → GeometricPolynomial n)
    (hf : Submodule.span (GeometricPolynomial n) (Set.range f) = I)
    (v : LinearMap.ker (genericMatrix I (jacobian f)).mulVecLin)
    (p : GeometricPolynomial n) :
    genericJacobianDerivationEquiv I f hf v (Ideal.Quotient.mk I p) =
      polynomialDerivationEquiv GeometricField (affineFunctionField I) (Fin n) v.val p := by
  let e := quotientDerivationEquiv GeometricField (GeometricPolynomial n) (affineFunctionField I) I
  have h := e.apply_symm_apply (genericJacobianAnnihilatorEquiv I f hf v)
  exact congrArg (fun d : annihilatingDerivations GeometricField (GeometricPolynomial n)
    (affineFunctionField I) I => d.val p) h

 theorem generic_stacked_rank (f : Fin c → GeometricPolynomial n)
    (P : Fin m → GeometricPolynomial n) :
    genericMatrixRank I (stackedJacobian f P) = genericMatrixRank I (jacobian f) +
      finrank (affineFunctionField I) (LinearMap.range
        ((genericMatrix I (jacobian P)).mulVecLin.domRestrict
          (LinearMap.ker (genericMatrix I (jacobian f)).mulVecLin))) := by
  have he : genericMatrix I (stackedJacobian f P) =
      (stackMatrix (genericMatrix I (jacobian f)) (genericMatrix I (jacobian P))).submatrix
        finSumFinEquiv.symm (Equiv.refl _) := by
    ext i j
    change genericPointMap I (stackMatrix (jacobian f) (jacobian P) (finSumFinEquiv.symm i) j) = _
    cases h : finSumFinEquiv.symm i <;> simp [Matrix.submatrix,h,stackMatrix,genericMatrix]
  change (genericMatrix I (stackedJacobian f P)).rank = _
  rw [he,Matrix.rank_submatrix,rank_stacked]
  rfl

/-- The second generic Jacobian dimension identity, now with no geometry
premise. Its coordinate ideal is the actual comap of the source prime ideal. -/
theorem generic_image_dimension
    (f : Fin c → GeometricPolynomial n)
    (hf : Submodule.span (GeometricPolynomial n) (Set.range f) = I)
    (P : Fin m → GeometricPolynomial n) :
    ringKrullDim (affineCoordinateRing (polynomialImageIdeal I P)) =
      ((genericMatrixRank I (stackedJacobian f P) - genericMatrixRank I (jacobian f) : ℕ) : Dimension) := by
  let e := genericJacobianDerivationEquiv I f hf
  let L := (genericMatrix I (jacobian P)).mulVecLin.domRestrict
    (LinearMap.ker (genericMatrix I (jacobian f)).mulVecLin)
  have he : (imageDerivationValues I P).comp e.toLinearMap = L := by
    ext v i
    change genericJacobianDerivationEquiv I f hf v (Ideal.Quotient.mk I (P i)) =
      ((genericMatrix I (jacobian P)).mulVec v.val) i
    rw [genericJacobianDerivationEquiv_mk,polynomialDerivation_apply]
    simp only [genericMatrix,jacobian,Matrix.mulVec,dotProduct,Matrix.map_apply,
      genericPointMap_algebraMap]
  have hrange : LinearMap.range L = LinearMap.range (imageDerivationValues I P) := by
    rw [←he,LinearMap.range_comp_of_range_eq_top _ e.range]
  have hr := generic_stacked_rank I f P
  change genericMatrixRank I (stackedJacobian f P) = genericMatrixRank I (jacobian f) +
    finrank (affineFunctionField I) (LinearMap.range L) at hr
  have hd := image_derivation_dimension I P
  rw [←hrange] at hd
  have hn : finrank (affineFunctionField I) (LinearMap.range L) =
      genericMatrixRank I (stackedJacobian f P) - genericMatrixRank I (jacobian f) := by omega
  exact hd.trans (congrArg (fun d : ℕ => (d : Dimension)) hn)

end HessianTheorem11.UnconditionalGeneric
