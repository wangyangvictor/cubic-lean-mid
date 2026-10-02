import TranslatedDepthSeven.AbsoluteIrreducibility
import TranslatedDepthSeven.AlgebraicallyClosedCoefficientPrime
import TranslatedDepthSeven.GeometricPrimeness
import Mathlib.RingTheory.Flat.Basic

/-! # Absolute irreducibility of a hypersurface image

An equation generating the kernel of a map into a geometrically integral
polynomial quotient is absolutely irreducible. The image quotient embeds
in the source; flat field extension preserves this embedding. No new
projection theorem or geometric-integrality premise for the image is used.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

theorem absolutelyIrreducible_of_ker_eq_span_of_geometricallyPrime
    {σ τ : Type} (I : Ideal (MvPolynomial σ ℚ))
    (hI : GeometricallyPrimeMvPolynomialIdeal I)
    (g : MvPolynomial τ ℚ →ₐ[ℚ] (MvPolynomial σ ℚ ⧸ I))
    (G : MvPolynomial τ ℚ) (hG : G ≠ 0)
    (hker : RingHom.ker g.toRingHom = Ideal.span {G}) :
    Published.IsAbsolutelyIrreducible G := by
  let L := AlgebraicClosure ℚ
  let A := MvPolynomial σ ℚ ⧸ I
  let J := RingHom.ker g.toRingHom
  let B := MvPolynomial τ ℚ ⧸ J
  let j : B →ₐ[ℚ] A := Ideal.kerLiftAlg g
  letI : (I.map (MvPolynomial.map (algebraMap ℚ L))).IsPrime := hI L
  letI : IsDomain (L ⊗[ℚ] A) :=
    (polynomialQuotientTensorAlgEquiv (L := L) I).symm.toMulEquiv.isDomain _
  let jt : (L ⊗[ℚ] B) →ₐ[L] (L ⊗[ℚ] A) :=
    Algebra.TensorProduct.map (AlgHom.id L L) j
  have hjt : Function.Injective jt :=
    Module.Flat.lTensor_preserves_injective_linearMap j.toLinearMap
      (Ideal.kerLiftAlg_injective g)
  letI : IsDomain (L ⊗[ℚ] B) := Function.Injective.isDomain jt hjt
  have hprime : (J.map (MvPolynomial.map (algebraMap ℚ L))).IsPrime := by
    apply (Ideal.Quotient.isDomain_iff_prime _).mp
    exact (polynomialQuotientTensorAlgEquiv (L := L) J).toMulEquiv.isDomain _
  have heq : J.map (MvPolynomial.map (algebraMap ℚ L)) =
      Ideal.span {MvPolynomial.map (algebraMap ℚ L) G} := by
    rw [show J = Ideal.span {G} from hker, Ideal.map_span, Set.image_singleton]
  rw [heq] at hprime
  have hmap : MvPolynomial.map (algebraMap ℚ L) G ≠ 0 := by
    exact fun h ↦ hG ((MvPolynomial.map_injective (algebraMap ℚ L)
      (algebraMap ℚ L).injective) (by simpa using h))
  exact ((Ideal.span_singleton_prime hmap).mp hprime).irreducible

end
end TranslatedDepthSeven
