import TranslatedDepthSeven.AugmentedStandardSmoothGeometricDomainInternal
import TranslatedDepthSeven.SmoothRationalPointStandardChartInternal
import TranslatedDepthSeven.HomogeneousChartPolynomialEmbedding
import TranslatedDepthSeven.AlgebraicallyClosedCoefficientPrime

/-!
# Geometric integrality from an actual smooth affine rational point

The selected-Jacobian neighbourhood is used only as an injective target
for the integral affine coordinate ring.  Flat field extension preserves
that injection, and the global standard-smooth argument proves the target
is a domain.  The projective cone is then treated by its existing concrete
embedding into a polynomial ring over the affine chart.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct
open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

theorem tensorProduct_affineQuotient_isDomain_of_smooth_rationalPoint
    {K : Type*} [Field K] {N : ℕ}
    (J : Ideal (MvPolynomial (Fin N) K)) (hJ : J.IsPrime)
    (z : Fin N → K) (hsmooth : IsSmoothAffineIdealRationalPoint J z)
    (L : Type*) [Field L] [Algebra K L] :
    IsDomain (L ⊗[K] (MvPolynomial (Fin N) K ⧸ J)) := by
  letI : J.IsPrime := hJ
  obtain ⟨hz, hsm⟩ := hsmooth
  let f := affineQuotientRationalPoint J z hz
  obtain ⟨a, ha, r, hr⟩ :=
    exists_standardSmooth_principalOpen_at_smooth_affineRationalPoint J z hz ⟨hz, hsm⟩
  let A := MvPolynomial (Fin N) K ⧸ J
  let B := Localization.Away a
  have ha0 : a ≠ 0 := by intro h; exact ha (by simp [h])
  have hM : Submonoid.powers a ≤ nonZeroDivisors A :=
    powers_le_nonZeroDivisors_of_noZeroDivisors ha0
  letI : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B hM
  letI : Algebra.IsStandardSmoothOfRelativeDimension r K B := hr
  let g : A →ₐ[K] B := IsScalarTower.toAlgHom K A B
  have hg : Function.Injective g := IsLocalization.injective B hM
  let fB : B →ₐ[K] K := IsLocalization.liftAlgHom
    (M := Submonoid.powers a) (f := f) (fun y ↦ by
    obtain ⟨n, hn⟩ := y.property
    apply isUnit_iff_ne_zero.mpr
    change f (y : A) ≠ 0
    rw [← hn, map_pow]
    exact pow_ne_zero n ha)
  exact tensorProduct_isDomain_of_injective_into_standardSmooth_rationalPoint
    g hg fB r L

theorem tensorProduct_polynomial_isDomain_of_tensorProduct_isDomain
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (L : Type*) [Field L] [Algebra K L]
    [IsDomain (L ⊗[K] A)] : IsDomain (L ⊗[K] Polynomial A) := by
  letI : IsDomain (A ⊗[K] L) :=
    (Algebra.TensorProduct.comm K A L).toMulEquiv.isDomain _
  letI : IsDomain ((MvPolynomial PUnit.{1} A) ⊗[K] L) :=
    (MvPolynomial.rTensorAlgEquiv (R := K) (S := A) (N := L)
      (σ := PUnit.{1})).toMulEquiv.isDomain _
  let ep : MvPolynomial PUnit.{1} A ≃ₐ[A] Polynomial A :=
    MvPolynomial.pUnitAlgEquiv A
  let e := Algebra.TensorProduct.congr
    (ep.symm.restrictScalars K) (AlgEquiv.refl : L ≃ₐ[K] L)
  letI : IsDomain (Polynomial A ⊗[K] L) := e.toMulEquiv.isDomain _
  exact (Algebra.TensorProduct.comm K L (Polynomial A)).toMulEquiv.isDomain _

theorem tensorProduct_optionCone_isDomain_of_chart
    {K : Type*} [Field K] {N : ℕ}
    (I : Ideal (MvPolynomial (Option (Fin N)) K))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Option (Fin N)) K))
    (hprime : I.IsPrime) (hX : X (none : Option (Fin N)) ∉ I)
    (L : Type*) [Field L] [Algebra K L]
    [IsDomain (L ⊗[K] (MvPolynomial (Fin N) K ⧸
      I.map multivariateDehomogenization.toRingHom))] :
    IsDomain (L ⊗[K] (MvPolynomial (Option (Fin N)) K ⧸ I)) := by
  let R := MvPolynomial (Fin N) K ⧸ I.map multivariateDehomogenization.toRingHom
  letI : IsDomain (L ⊗[K] Polynomial R) :=
    tensorProduct_polynomial_isDomain_of_tensorProduct_isDomain L
  let g := optionConeChartPolynomialEmbedding I hI hprime hX
  have hg : Function.Injective g :=
    optionConeChartPolynomialEmbedding_injective I hI hprime hX
  let h := Algebra.TensorProduct.map (AlgHom.id K L) g
  have hh : Function.Injective h :=
    Module.Flat.lTensor_preserves_injective_linearMap g.toLinearMap hg
  exact Function.Injective.isDomain h hh

end

end TranslatedDepthSeven
