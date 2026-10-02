import TranslatedDepthSeven.TensorIdealSeparatednessInternal
import TranslatedDepthSeven.SmoothPointKrullIntersectionPrimeInternal
import Mathlib.RingTheory.Flat.Basic

/-!
# A standard-smooth domain with a rational point is geometrically integral

For a rational augmentation of a Noetherian domain, the powers of its
kernel have zero intersection.  Field extension preserves this separation
coefficient by coefficient.  Standard smoothness makes the corresponding
intersection prime after field extension, by the checked polynomial-jet
calculation.  Thus the entire scalar extension is a domain, not just its
local ring at the point.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct

def rationalAugmentationBaseChange
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (f : A →ₐ[K] K) (L : Type*) [Field L] [Algebra K L] :
    (L ⊗[K] A) →ₐ[L] L :=
  (Algebra.TensorProduct.rid K L L).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id L L) f)

theorem rationalAugmentationBaseChange_ker
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (f : A →ₐ[K] K) (L : Type*) [Field L] [Algebra K L] :
    RingHom.ker (rationalAugmentationBaseChange f L).toRingHom =
      (RingHom.ker f.toRingHom).map
        (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) := by
  have hsurj : Function.Surjective f := fun a ↦
    ⟨algebraMap K A a, f.commutes a⟩
  have hker := Algebra.TensorProduct.lTensor_ker (A := L) f hsurj
  change RingHom.ker
      ((Algebra.TensorProduct.rid K L L).toRingHom.comp
        (Algebra.TensorProduct.map (AlgHom.id L L) f).toRingHom) = _
  trans RingHom.ker (Algebra.TensorProduct.map (AlgHom.id K L) f)
  · ext x
    change (Algebra.TensorProduct.rid K L L)
        (Algebra.TensorProduct.map (AlgHom.id L L) f x) = 0 ↔
      Algebra.TensorProduct.map (AlgHom.id K L) f x = 0
    constructor
    · intro hx
      apply (Algebra.TensorProduct.rid K L L).injective
      simpa using hx
    · intro hx
      change (Algebra.TensorProduct.rid K L L)
        (Algebra.TensorProduct.map (AlgHom.id K L) f x) = 0
      rw [hx, map_zero]
  · exact hker

theorem tensorProduct_isDomain_of_standardSmooth_rationalPoint
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    [IsNoetherianRing A] [IsDomain A]
    (f : A →ₐ[K] K) (r : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A]
    (L : Type*) [Field L] [Algebra K L] : IsDomain (L ⊗[K] A) := by
  have hm : RingHom.ker f.toRingHom ≠ ⊤ := by
    intro h
    have : (1 : A) ∈ RingHom.ker f.toRingHom := by rw [h]; trivial
    exact (one_ne_zero : (1 : K) ≠ 0) (by simpa using this)
  have hsep : (⨅ n : ℕ,
      RingHom.ker (rationalAugmentationBaseChange f L).toRingHom ^ n) = ⊥ := by
    rw [rationalAugmentationBaseChange_ker]
    exact iInf_map_powers_includeRight_eq_bot (RingHom.ker f.toRingHom) hm
  letI : (⊥ : Ideal (L ⊗[K] A)).IsPrime := by
    rw [← hsep]
    exact iInf_pointIdeal_pow_isPrime_of_standardSmooth
      (rationalAugmentationBaseChange f L) r
  exact IsDomain.of_bot_isPrime _

theorem tensorProduct_isDomain_of_injective_into_standardSmooth_rationalPoint
    {K A B : Type*} [Field K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [IsNoetherianRing B] [IsDomain B]
    (g : A →ₐ[K] B) (hg : Function.Injective g)
    (f : B →ₐ[K] K) (r : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension r K B]
    (L : Type*) [Field L] [Algebra K L] : IsDomain (L ⊗[K] A) := by
  letI : IsDomain (L ⊗[K] B) :=
    tensorProduct_isDomain_of_standardSmooth_rationalPoint f r L
  let h := Algebra.TensorProduct.map (AlgHom.id K L) g
  have hh : Function.Injective h :=
    Module.Flat.lTensor_preserves_injective_linearMap g.toLinearMap hg
  exact Function.Injective.isDomain h hh

end

end TranslatedDepthSeven
