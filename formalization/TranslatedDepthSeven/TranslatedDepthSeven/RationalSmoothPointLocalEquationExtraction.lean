import TranslatedDepthSeven.RationalPointLocalPolynomialExtension
import TranslatedDepthSeven.LocalSmoothConormalEquationSelection
import TranslatedDepthSeven.RationalLocalEquationIntegralization
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Literal local equations at a rational smooth point

This file connects the abstract conormal selection argument to the ordinary
Jacobian matrix of a finite family of polynomials.  The source of the local
presentation is the polynomial local ring at the displayed point.  Its
cotangent coordinates are obtained from the standard basis `dX_i`, first by
localization and then by the two scalar extensions to the quotient local ring
and its residue field.
-/

namespace TranslatedDepthSeven

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 500000

open scoped TensorProduct
open MvPolynomial KaehlerDifferential IsLocalRing

universe u

/-- The `dX_i` basis after localizing the polynomial ring at a displayed
affine point. -/
noncomputable def affinePolynomialLocalKaehlerBasis
    {k : Type u} [Field k] {N : ℕ} (z : Fin N → k) :
    Module.Basis (Fin N) (Localization.AtPrime (affineEvaluationPrime z))
      Ω[Localization.AtPrime (affineEvaluationPrime z)⁄k] := by
  let R := MvPolynomial (Fin N) k
  let L := Localization.AtPrime (affineEvaluationPrime z)
  letI : Algebra.FormallyEtale R L :=
    Algebra.FormallyEtale.of_isLocalization
      (affineEvaluationPrime z).primeCompl
  exact
    ((KaehlerDifferential.mvPolynomialBasis k (Fin N)).baseChange L).map
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R L)

@[simp]
theorem affinePolynomialLocalKaehlerBasis_repr_D_algebraMap
    {k : Type u} [Field k] {N : ℕ} (z : Fin N → k)
    (f : MvPolynomial (Fin N) k) (i : Fin N) :
    (affinePolynomialLocalKaehlerBasis z).repr
        (KaehlerDifferential.D k
          (Localization.AtPrime (affineEvaluationPrime z))
          (algebraMap (MvPolynomial (Fin N) k)
            (Localization.AtPrime (affineEvaluationPrime z)) f)) i =
      algebraMap (MvPolynomial (Fin N) k)
        (Localization.AtPrime (affineEvaluationPrime z))
          (MvPolynomial.pderiv i f) := by
  classical
  let R := MvPolynomial (Fin N) k
  let L := Localization.AtPrime (affineEvaluationPrime z)
  letI : Algebra.FormallyEtale R L :=
    Algebra.FormallyEtale.of_isLocalization
      (affineEvaluationPrime z).primeCompl
  simp only [affinePolynomialLocalKaehlerBasis, Module.Basis.map_repr,
    LinearEquiv.trans_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    Module.Basis.baseChange_repr_tmul,
    KaehlerDifferential.mvPolynomialBasis_repr_apply, Algebra.smul_def,
    mul_one]

/-- The standard ambient differential coordinates for the local polynomial
presentation of an affine quotient at a rational point. -/
noncomputable def affineQuotientResidualAmbientCoordinates
    {k : Type u} [Field k] {N : ℕ}
    (J : Ideal (MvPolynomial (Fin N) k)) (z : Fin N → k)
    (hJ : J ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom) :
    let S := AffineQuotientRationalPointLocalRing J z hJ
    let P := affineQuotientLocalExtension J z hJ
    (ResidueField S ⊗[S] P.CotangentSpace) ≃ₗ[ResidueField S]
      (Fin N → ResidueField S) := by
  let S := AffineQuotientRationalPointLocalRing J z hJ
  let P := affineQuotientLocalExtension J z hJ
  let L := Localization.AtPrime (affineEvaluationPrime z)
  let localMap := affineQuotientLocalRingAlgHom J z hJ
  letI : Algebra L S := localMap.toRingHom.toAlgebra
  letI : IsScalarTower k L S :=
    IsScalarTower.of_algebraMap_eq' localMap.comp_algebraMap.symm
  let bL := affinePolynomialLocalKaehlerBasis z
  let bS : Module.Basis (Fin N) S P.CotangentSpace := bL.baseChange S
  let bR : Module.Basis (Fin N) (ResidueField S)
      (ResidueField S ⊗[S] P.CotangentSpace) :=
    bS.baseChange (ResidueField S)
  exact bR.repr ≪≫ₗ
    Finsupp.linearEquivFunOnFinite (ResidueField S) (ResidueField S) (Fin N)

/-- An equation of the affine quotient, viewed as a literal element of the
kernel of the local polynomial presentation. -/
noncomputable def affineQuotientLocalKernelElement
    {k : Type u} [Field k] {N : ℕ}
    (J : Ideal (MvPolynomial (Fin N) k)) (z : Fin N → k)
    (hJ : J ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom)
    (f : MvPolynomial (Fin N) k) (hf : f ∈ J) :
    (affineQuotientLocalExtension J z hJ).ker := by
  refine ⟨algebraMap (MvPolynomial (Fin N) k)
    (Localization.AtPrime (affineEvaluationPrime z)) f, ?_⟩
  rw [affineQuotientLocalExtension_ker]
  exact Ideal.mem_map_of_mem _ hf

/-- In the canonical residual ambient coordinates, the differential of a
literal quotient equation has entries equal to its ordinary partial
derivatives, mapped through the two local rings. -/
theorem affineQuotientResidualAmbientCoordinates_apply
    {k : Type u} [Field k] {N : ℕ}
    (J : Ideal (MvPolynomial (Fin N) k)) (z : Fin N → k)
    (hJ : J ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom)
    (f : MvPolynomial (Fin N) k) (hf : f ∈ J) (i : Fin N) :
    let S := AffineQuotientRationalPointLocalRing J z hJ
    let P := affineQuotientLocalExtension J z hJ
    affineQuotientResidualAmbientCoordinates J z hJ
        ((P.cotangentComplex.baseChange (ResidueField S))
          ((1 : ResidueField S) ⊗ₜ[S]
            Algebra.Extension.Cotangent.mk
              (affineQuotientLocalKernelElement J z hJ f hf))) i =
      algebraMap S (ResidueField S)
        (affineQuotientLocalRingAlgHom J z hJ
          (algebraMap (MvPolynomial (Fin N) k)
            (Localization.AtPrime (affineEvaluationPrime z))
              (MvPolynomial.pderiv i f))) := by
  classical
  let S := AffineQuotientRationalPointLocalRing J z hJ
  let P := affineQuotientLocalExtension J z hJ
  let L := Localization.AtPrime (affineEvaluationPrime z)
  let localMap := affineQuotientLocalRingAlgHom J z hJ
  letI : Algebra L S := localMap.toRingHom.toAlgebra
  letI : IsScalarTower k L S :=
    IsScalarTower.of_algebraMap_eq' localMap.comp_algebraMap.symm
  simp only [affineQuotientResidualAmbientCoordinates,
    LinearEquiv.trans_apply, Finsupp.linearEquivFunOnFinite_apply,
    LinearMap.baseChange_tmul,
    Algebra.Extension.cotangentComplex_mk,
    Module.Basis.baseChange_repr_tmul,
    Algebra.smul_def, mul_one,
    affineQuotientLocalKernelElement]
  apply congrArg (algebraMap S (ResidueField S))
  change
    ((affinePolynomialLocalKaehlerBasis z).baseChange S).repr
        ((1 : S) ⊗ₜ[L]
          KaehlerDifferential.D k L
            (algebraMap (MvPolynomial (Fin N) k) L f)) i =
      localMap
        (algebraMap (MvPolynomial (Fin N) k) L
          (MvPolynomial.pderiv i f))
  rw [Module.Basis.baseChange_repr_tmul]
  simp only [Algebra.smul_def, mul_one]
  rw [affinePolynomialLocalKaehlerBasis_repr_D_algebraMap]
  rfl

end

end TranslatedDepthSeven
