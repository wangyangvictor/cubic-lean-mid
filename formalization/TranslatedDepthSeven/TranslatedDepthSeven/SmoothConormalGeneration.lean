import TranslatedDepthSeven.ConormalNakayama
import TranslatedDepthSeven.SmoothConormalFinrank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Smooth residual conormal generation

This file combines four internal steps:

1. formal smoothness makes the residual cotangent-complex map injective;
2. exactness and the two differential-fibre ranks determine the residual
   conormal dimension;
3. a nonzero selected minor makes the displayed conormal classes linearly
   independent, hence a basis; and
4. Nakayama turns that basis into equality with the exact local kernel ideal.

The target differential-fibre rank is an explicit hypothesis.  No theorem
identifying it with a Krull dimension is assumed here.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct
open KaehlerDifferential

universe u v

private theorem extension_ker_le_span_sup_square_of_cotangent_span
    {k : Type u} {S : Type v} [CommRing k] [CommRing S] [Algebra k S]
    (P : Algebra.Extension k S) {ι : Type*} (g : ι → P.ker)
    (hspan : Submodule.span S
      (Set.range fun i ↦ Algebra.Extension.Cotangent.mk (g i)) = ⊤) :
    P.ker ≤
      (Ideal.span (Set.range (Subtype.val ∘ g)) : Ideal P.Ring) ⊔
        P.ker ^ 2 := by
  let J : Ideal P.Ring := Ideal.span (Set.range (Subtype.val ∘ g))
  have hJI : J ≤ P.ker := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (g i).2
  have hsub : (P.ker : Submodule P.Ring P.Ring) ≤
      (J : Submodule P.Ring P.Ring) ⊔ P.ker • P.ker := by
    rw [← Submodule.comap_le_comap_iff_of_le_range (f := P.ker.subtype) (by simp),
      Submodule.comap_subtype_self,
      Submodule.comap_sup_of_injective P.ker.subtype_injective (by simpa using hJI)
        (by simp [Ideal.mul_le_left]),
      Submodule.comap_smul'' P.ker.subtype_injective (by simp)]
    simp only [Submodule.comap_subtype_self, J]
    rw [← Submodule.coe_subtype, Ideal.span, Set.range_comp, ← Submodule.map_span,
      Submodule.comap_map_eq_of_injective P.ker.subtype_injective,
      ← Algebra.Extension.Cotangent.ker_mk]
    simp only [← LinearMap.map_le_map_iff, Submodule.map_span, ← Set.range_comp,
      Function.comp_def,
      ← Submodule.restrictScalars_span P.Ring S P.algebraMap_surjective]
    rw [hspan, Submodule.restrictScalars_top]
    exact le_top
  simpa only [pow_two, smul_eq_mul] using hsub

private theorem ideal_eq_of_le_sup_self_smul
    {R : Type*} [CommRing R] [Nontrivial R] [IsLocalRing R]
    (J I : Ideal R) (hJI : J ≤ I) (hIfg : I.FG)
    (hImax : I ≤ IsLocalRing.maximalIdeal R)
    (hle : I ≤ J ⊔ I ^ 2) : J = I := by
  have hsq : I ^ 2 ≤ IsLocalRing.maximalIdeal R * I := by
    rw [pow_two]
    exact Ideal.mul_mono hImax le_rfl
  have hle' : (I : Submodule R R) ≤
      (J : Submodule R R) ⊔
        IsLocalRing.maximalIdeal R • (I : Submodule R R) := by
    rw [smul_eq_mul]
    exact hle.trans <| sup_le le_sup_left (hsq.trans le_sup_right)
  apply (IsLocalRing.map_mkQ_eq hJI hIfg).mp
  apply le_antisymm (Submodule.map_mono hJI)
  calc
    Submodule.map
        (Submodule.mkQ
          (IsLocalRing.maximalIdeal R • (I : Submodule R R)))
        (I : Submodule R R) ≤
      Submodule.map
        (Submodule.mkQ
          (IsLocalRing.maximalIdeal R • (I : Submodule R R)))
        ((J : Submodule R R) ⊔
          IsLocalRing.maximalIdeal R • (I : Submodule R R)) :=
      Submodule.map_mono hle'
    _ = Submodule.map
        (Submodule.mkQ
          (IsLocalRing.maximalIdeal R • (I : Submodule R R)))
        (J : Submodule R R) := by
      rw [Submodule.map_sup]
      simp

/-- If displayed kernel elements span the cotangent module of a surjective
local extension, then they generate the exact kernel ideal. -/
theorem extension_ker_eq_span_of_cotangent_span
    {k : Type u} {S : Type v} [CommRing k] [CommRing S] [Nontrivial S] [Algebra k S]
    (P : Algebra.Extension k S) [IsLocalRing P.Ring]
    (hker : P.ker.FG) {ι : Type*} (g : ι → P.ker)
    (hspan : Submodule.span S
      (Set.range fun i ↦ Algebra.Extension.Cotangent.mk (g i)) = ⊤) :
    Ideal.span (Set.range fun i ↦ ((g i : P.ker) : P.Ring)) = P.ker := by
  let J : Ideal P.Ring :=
    Ideal.span (Set.range (Subtype.val ∘ g))
  have hJI : J ≤ P.ker := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (g i).2
  have hleSquare : P.ker ≤ J ⊔ P.ker ^ 2 := by
    exact extension_ker_le_span_sup_square_of_cotangent_span P g hspan
  have hkerMax : P.ker ≤ IsLocalRing.maximalIdeal P.Ring :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top (algebraMap P.Ring S))
  change J = P.ker
  exact ideal_eq_of_le_sup_self_smul J P.ker hJI hker hkerMax hleSquare

/-- The fully internal implication from differential-fibre ranks and a
selected residual Jacobian minor to generation of the exact local kernel.

In the polynomial application, `ambientCoordinates` is the coordinate map
coming from the differentials of the polynomial variables. -/
theorem extension_ker_eq_span_of_smooth_finranks_and_selectedMinor
    {k : Type u} {S : Type v} [CommRing k] [CommRing S] [Nontrivial S]
    [Algebra k S] [IsLocalRing S]
    (P : Algebra.Extension k S) [IsLocalRing P.Ring]
    [Algebra.FormallySmooth k P.Ring]
    [Module.Free P.Ring Ω[P.Ring⁄k]]
    [Module.Finite P.Ring Ω[P.Ring⁄k]]
    (hker : P.ker.FG) [Algebra.FormallySmooth k S]
    {N s : ℕ}
    (hambient : Module.finrank (IsLocalRing.ResidueField S)
      (IsLocalRing.ResidueField S ⊗[S] P.CotangentSpace) = N)
    (htarget : Module.finrank (IsLocalRing.ResidueField S)
      (IsLocalRing.ResidueField S ⊗[S] Ω[S⁄k]) = s)
    (g : Fin (N - s) → P.ker)
    (ambientCoordinates :
      (IsLocalRing.ResidueField S ⊗[S] P.CotangentSpace) ≃ₗ[IsLocalRing.ResidueField S]
        (Fin N → IsLocalRing.ResidueField S))
    (cols : Fin (N - s) → Fin N)
    (hminor : Matrix.det (Matrix.of (fun i j ↦
      ambientCoordinates
        ((P.cotangentComplex.baseChange (IsLocalRing.ResidueField S))
          ((1 : IsLocalRing.ResidueField S) ⊗ₜ[S]
            Algebra.Extension.Cotangent.mk (g i))) (cols j))) ≠ 0) :
    Ideal.span (Set.range fun i ↦ ((g i : P.ker) : P.Ring)) = P.ker := by
  have hfiniteCotangentRing : Module.Finite P.Ring P.Cotangent := by
    have : Module.Finite P.Ring P.ker :=
      ⟨(Submodule.fg_top P.ker).mpr hker⟩
    exact Module.Finite.of_surjective _ Algebra.Extension.Cotangent.mk_surjective
  letI : Module.Finite S P.Cotangent :=
    Module.Finite.of_restrictScalars_finite P.Ring S P.Cotangent
  have hfinrank : Module.finrank (IsLocalRing.ResidueField S)
      (IsLocalRing.ResidueField S ⊗[S] P.Cotangent) = N - s :=
    finrank_residueTensor_extensionCotangent_eq_sub P hker hambient htarget
  let v : Fin (N - s) →
      (IsLocalRing.ResidueField S ⊗[S] P.Cotangent) :=
    fun i ↦ (1 : IsLocalRing.ResidueField S) ⊗ₜ[S]
      Algebra.Extension.Cotangent.mk (g i)
  let d : (IsLocalRing.ResidueField S ⊗[S] P.Cotangent)
      →ₗ[IsLocalRing.ResidueField S]
        (Fin N → IsLocalRing.ResidueField S) :=
    ambientCoordinates.toLinearMap.comp
      (P.cotangentComplex.baseChange (IsLocalRing.ResidueField S))
  let restrictCols :
      (Fin N → IsLocalRing.ResidueField S) →ₗ[IsLocalRing.ResidueField S]
        (Fin (N - s) → IsLocalRing.ResidueField S) :=
    LinearMap.funLeft (IsLocalRing.ResidueField S)
      (IsLocalRing.ResidueField S) cols
  have hliImage : LinearIndependent (IsLocalRing.ResidueField S)
      (fun i ↦ restrictCols (d (v i))) := by
    have hrows := Matrix.linearIndependent_rows_of_det_ne_zero hminor
    simpa only [Matrix.row, Matrix.of_apply, v, d, restrictCols,
      LinearMap.funLeft_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply] using hrows
  have hli : LinearIndependent (IsLocalRing.ResidueField S) v := by
    apply LinearIndependent.of_comp (restrictCols.comp d)
    simpa only [LinearMap.coe_comp, Function.comp_apply] using hliImage
  have hspanK : Submodule.span (IsLocalRing.ResidueField S) (Set.range v) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hli, Fintype.card_fin]
    exact hfinrank.symm
  let b : Module.Basis (Fin (N - s)) (IsLocalRing.ResidueField S)
      (IsLocalRing.ResidueField S ⊗[S] P.Cotangent) :=
    Module.Basis.mk hli hspanK.ge
  have hb : ∀ i, (1 : IsLocalRing.ResidueField S) ⊗ₜ[S]
      Algebra.Extension.Cotangent.mk (g i) = b i := by
    intro i
    change v i = b i
    simp [b, v]
  have hspan : Submodule.span S
      (Set.range fun i ↦ Algebra.Extension.Cotangent.mk (g i)) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis _ b hb
  exact extension_ker_eq_span_of_cotangent_span P hker g hspan

end

end TranslatedDepthSeven
