import TranslatedDepthSeven.RationalResidueDifferential
import TranslatedDepthSeven.SmoothConormalGeneration

/-!
# Rational smooth conormal generation without a regular-local interface

A selected minor supplies the upper bound for the target differential-fibre
dimension that is absent from the general smooth-local API.  Krull's height
theorem supplies the opposite inequality at a rational point.  Together they
force the target dimension, after which the existing conormal Nakayama
argument applies.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct
open KaehlerDifferential IsLocalRing

universe u v

/-- At a rational smooth point of known Krull dimension, a full selected
residual Jacobian minor forces the expected differential-fibre dimension and
the displayed equations generate the exact local kernel.

This theorem avoids any appeal to a general theorem equating the embedding
dimension and Krull dimension of a regular local ring. -/
theorem extension_ker_eq_span_of_rationalSmooth_krullDim_and_selectedMinor
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Nontrivial S]
    [Algebra k S] [IsLocalRing S] [IsNoetherianRing S]
    (e : ResidueField S ≃ₐ[k] k)
    (P : Algebra.Extension k S) [IsLocalRing P.Ring]
    [Algebra.FormallySmooth k P.Ring]
    [Module.Free P.Ring Ω[P.Ring⁄k]]
    [Module.Finite P.Ring Ω[P.Ring⁄k]]
    (hker : P.ker.FG) [Algebra.FormallySmooth k S]
    {N s : ℕ} (hdim : ringKrullDim S = s)
    (hambient : Module.finrank (ResidueField S)
      (ResidueField S ⊗[S] P.CotangentSpace) = N)
    (g : Fin (N - s) → P.ker)
    (ambientCoordinates :
      (ResidueField S ⊗[S] P.CotangentSpace) ≃ₗ[ResidueField S]
        (Fin N → ResidueField S))
    (cols : Fin (N - s) → Fin N)
    (hminor : Matrix.det (Matrix.of (fun i j ↦
      ambientCoordinates
        ((P.cotangentComplex.baseChange (ResidueField S))
          ((1 : ResidueField S) ⊗ₜ[S]
            Algebra.Extension.Cotangent.mk (g i))) (cols j))) ≠ 0) :
    Ideal.span (Set.range fun i ↦ ((g i : P.ker) : P.Ring)) = P.ker := by
  let d := Module.finrank (ResidueField S)
    (ResidueField S ⊗[S] Ω[S⁄k])
  have htargetD : Module.finrank (ResidueField S)
      (ResidueField S ⊗[S] Ω[S⁄k]) = d := rfl
  have hfiniteCotangentRing : Module.Finite P.Ring P.Cotangent := by
    have : Module.Finite P.Ring P.ker :=
      ⟨(Submodule.fg_top P.ker).mpr hker⟩
    exact Module.Finite.of_surjective _ Algebra.Extension.Cotangent.mk_surjective
  letI : Module.Finite S P.Cotangent :=
    Module.Finite.of_restrictScalars_finite P.Ring S P.Cotangent
  have hconormal : Module.finrank (ResidueField S)
      (ResidueField S ⊗[S] P.Cotangent) = N - d :=
    finrank_residueTensor_extensionCotangent_eq_sub P hker hambient htargetD
  let v : Fin (N - s) → (ResidueField S ⊗[S] P.Cotangent) :=
    fun i ↦ (1 : ResidueField S) ⊗ₜ[S]
      Algebra.Extension.Cotangent.mk (g i)
  let differential : (ResidueField S ⊗[S] P.Cotangent)
      →ₗ[ResidueField S] (Fin N → ResidueField S) :=
    ambientCoordinates.toLinearMap.comp
      (P.cotangentComplex.baseChange (ResidueField S))
  let restrictCols :
      (Fin N → ResidueField S) →ₗ[ResidueField S]
        (Fin (N - s) → ResidueField S) :=
    LinearMap.funLeft (ResidueField S) (ResidueField S) cols
  have hliImage : LinearIndependent (ResidueField S)
      (fun i ↦ restrictCols (differential (v i))) := by
    have hrows := Matrix.linearIndependent_rows_of_det_ne_zero hminor
    simpa only [Matrix.row, Matrix.of_apply, v, differential, restrictCols,
      LinearMap.funLeft_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply] using hrows
  have hli : LinearIndependent (ResidueField S) v := by
    apply LinearIndependent.of_comp (restrictCols.comp differential)
    simpa only [LinearMap.coe_comp, Function.comp_apply] using hliImage
  have hminorLower : N - s ≤ Module.finrank (ResidueField S)
      (ResidueField S ⊗[S] P.Cotangent) := by
    calc
      N - s = Module.finrank (ResidueField S)
          (Submodule.span (ResidueField S) (Set.range v)) := by
        rw [finrank_span_eq_card hli, Fintype.card_fin]
      _ ≤ Module.finrank (ResidueField S)
          (ResidueField S ⊗[S] P.Cotangent) :=
        Submodule.finrank_le _
  let targetMap := P.toKaehler.baseChange (ResidueField S)
  have htargetSurj : Function.Surjective targetMap := by
    rw [show targetMap = P.toKaehler.baseChange (ResidueField S) from rfl,
      LinearMap.baseChange_eq_ltensor]
    exact P.toKaehler.lTensor_surjective _ P.toKaehler_surjective
  have hdleN : d ≤ N := by
    have hrange : LinearMap.range targetMap = ⊤ :=
      LinearMap.range_eq_top.mpr htargetSurj
    calc
      d = Module.finrank (ResidueField S)
          (ResidueField S ⊗[S] Ω[S⁄k]) := rfl
      _ = Module.finrank (ResidueField S) (LinearMap.range targetMap) := by
        rw [hrange, finrank_top]
      _ ≤ Module.finrank (ResidueField S)
          (ResidueField S ⊗[S] P.CotangentSpace) :=
        targetMap.finrank_range_le
      _ = N := hambient
  have hsled : s ≤ d := by
    have hlower :=
      ringKrullDim_le_finrank_residueTensor_kaehler_of_rationalResidue S e
    rw [hdim] at hlower
    exact_mod_cast hlower
  have hdles : d ≤ s := by
    apply (tsub_le_tsub_iff_left hdleN).mp
    rw [← hconormal]
    exact hminorLower
  have htarget : Module.finrank (ResidueField S)
      (ResidueField S ⊗[S] Ω[S⁄k]) = s := by
    exact htargetD.trans (Nat.le_antisymm hdles hsled)
  exact extension_ker_eq_span_of_smooth_finranks_and_selectedMinor
    P hker hambient htarget g ambientCoordinates cols hminor

end

end TranslatedDepthSeven
