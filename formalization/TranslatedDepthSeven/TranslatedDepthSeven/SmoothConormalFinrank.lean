import TranslatedDepthSeven.ExactSequenceFinrank
import Mathlib.RingTheory.Smooth.Local

/-!
# The residual conormal dimension from a smooth local presentation

This file records the finite-dimensional linear-algebra consequence of the
local Jacobian criterion.  For a surjective extension `P → S` with formally
smooth source and target, the residual cotangent-complex map is injective.
The conormal fibre therefore has dimension equal to the difference between
the ambient and target differential-fibre dimensions.

The theorem deliberately takes those two differential-fibre dimensions as
explicit hypotheses.  It does not identify them with Krull dimensions.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct
open Function
open KaehlerDifferential

universe u v

variable {k : Type u} {S : Type v} [CommRing k] [CommRing S]
  [Algebra k S] [IsLocalRing S]

/-- In a smooth local presentation, the residual conormal dimension is the
difference between the dimensions of the ambient and target differential
fibres. -/
theorem finrank_residueTensor_extensionCotangent_eq_sub
    (P : Algebra.Extension k S)
    [Algebra.FormallySmooth k P.Ring]
    [Module.Free P.Ring Ω[P.Ring⁄k]]
    [Module.Finite P.Ring Ω[P.Ring⁄k]]
    (hker : P.ker.FG) [Algebra.FormallySmooth k S]
    {N s : ℕ}
    (hambient : Module.finrank (IsLocalRing.ResidueField S)
      (IsLocalRing.ResidueField S ⊗[S] P.CotangentSpace) = N)
    (htarget : Module.finrank (IsLocalRing.ResidueField S)
      (IsLocalRing.ResidueField S ⊗[S] Ω[S⁄k]) = s) :
    Module.finrank (IsLocalRing.ResidueField S)
      (IsLocalRing.ResidueField S ⊗[S] P.Cotangent) = N - s := by
  have hfiniteCotangentRing : Module.Finite P.Ring P.Cotangent := by
    have : Module.Finite P.Ring P.ker :=
      ⟨(Submodule.fg_top P.ker).mpr hker⟩
    exact Module.Finite.of_surjective _ Algebra.Extension.Cotangent.mk_surjective
  letI : Module.Finite S P.Cotangent :=
    Module.Finite.of_restrictScalars_finite P.Ring S P.Cotangent
  have hinj : Function.Injective
      (P.cotangentComplex.lTensor (IsLocalRing.ResidueField S)) :=
    (Algebra.FormallySmooth.iff_injective_lTensor_residueField P hker).mp
      (inferInstance : Algebra.FormallySmooth k S)
  let fK := P.cotangentComplex.baseChange (IsLocalRing.ResidueField S)
  let gK := P.toKaehler.baseChange (IsLocalRing.ResidueField S)
  have hinjK : Function.Injective fK := by
    rw [show fK = P.cotangentComplex.baseChange
      (IsLocalRing.ResidueField S) from rfl,
      LinearMap.baseChange_eq_ltensor]
    exact hinj
  have hexact : Function.Exact fK gK := by
    simpa only [fK, gK, LinearMap.baseChange_eq_ltensor] using
      (lTensor_exact (IsLocalRing.ResidueField S)
        P.exact_cotangentComplex_toKaehler P.toKaehler_surjective)
  have hsurj : Function.Surjective gK := by
    rw [show gK = P.toKaehler.baseChange (IsLocalRing.ResidueField S) from rfl,
      LinearMap.baseChange_eq_ltensor]
    exact P.toKaehler.lTensor_surjective _ P.toKaehler_surjective
  rw [finrank_eq_sub_of_injective_exact_surjective fK gK hinjK hexact hsurj,
    hambient, htarget]

end

end TranslatedDepthSeven
