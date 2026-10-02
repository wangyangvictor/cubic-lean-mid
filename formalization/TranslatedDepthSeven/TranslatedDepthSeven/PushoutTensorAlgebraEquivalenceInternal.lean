import TranslatedDepthSeven.RealProjectiveHilbertExtension

/-!
# Algebra, rather than only module, equivalences for coefficient extension

The canonical cancellation equivalence for a scalar-extension square is
multiplicative: on a pure tensor its inverse sends `l ⊗ a` to
`algebraMap(l) ⊗ a`. This upgrades the existing module equivalence to an
algebra equivalence and applies to literal polynomial quotients.
-/

namespace TranslatedDepthSeven

noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

def pushoutTensorAlgebraEquiv
    (K L B S A : Type*)
    [CommRing K] [CommRing L] [CommRing B] [CommRing S] [CommRing A]
    [Algebra K L] [Algebra K B] [Algebra K S] [Algebra B S] [Algebra L S]
    [IsScalarTower K B S] [IsScalarTower K L S] [Algebra.IsPushout K L B S]
    [Algebra K A] [Algebra B A] [IsScalarTower K B A] :
    S ⊗[B] A ≃ₐ[L] L ⊗[K] A :=
  (AlgEquiv.ofLinearEquiv (Algebra.IsPushout.cancelBaseChange K L B S A).symm
    (by simp only [Algebra.TensorProduct.one_def,
      Algebra.IsPushout.cancelBaseChange_symm_tmul, map_one])
    (LinearMap.map_mul_of_map_mul_tmul (fun l l' a a' ↦ by
      change (Algebra.IsPushout.cancelBaseChange K L B S A).symm
        ((l * l') ⊗ₜ[K] (a * a')) =
        (Algebra.IsPushout.cancelBaseChange K L B S A).symm (l ⊗ₜ[K] a) *
        (Algebra.IsPushout.cancelBaseChange K L B S A).symm (l' ⊗ₜ[K] a')
      simp only [Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.IsPushout.cancelBaseChange_symm_tmul, map_mul]))).symm

@[simp] theorem pushoutTensorAlgebraEquiv_symm_tmul
    (K L B S A : Type*)
    [CommRing K] [CommRing L] [CommRing B] [CommRing S] [CommRing A]
    [Algebra K L] [Algebra K B] [Algebra K S] [Algebra B S] [Algebra L S]
    [IsScalarTower K B S] [IsScalarTower K L S] [Algebra.IsPushout K L B S]
    [Algebra K A] [Algebra B A] [IsScalarTower K B A]
    (l : L) (a : A) :
    (pushoutTensorAlgebraEquiv K L B S A).symm (l ⊗ₜ[K] a) =
      algebraMap L S l ⊗ₜ[B] a :=
  Algebra.IsPushout.cancelBaseChange_symm_tmul K L B S A l a

noncomputable local instance realMvPolynomialCoefficientAlgebra'' {σ : Type*} :
    Algebra (MvPolynomial σ ℚ) (MvPolynomial σ ℝ) :=
  MvPolynomial.algebraMvPolynomial

/-- Literal real polynomial quotient as the coefficient extension of the
rational quotient, with its full algebra structure retained. -/
def realCoefficientQuotientTensorAlgEquiv
    {σ : Type*} (I : Ideal (MvPolynomial σ ℚ)) :
    (MvPolynomial σ ℝ ⧸ I.map (MvPolynomial.map (algebraMap ℚ ℝ))) ≃ₐ[ℝ]
      ℝ ⊗[ℚ] (MvPolynomial σ ℚ ⧸ I) := by
  let e₁ := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot
    (MvPolynomial σ ℝ) I).restrictScalars ℝ
  let e₂ := pushoutTensorAlgebraEquiv ℚ ℝ
    (MvPolynomial σ ℚ) (MvPolynomial σ ℝ) (MvPolynomial σ ℚ ⧸ I)
  simpa only [MvPolynomial.algebraMap_apply] using e₁.trans e₂

end
end TranslatedDepthSeven
