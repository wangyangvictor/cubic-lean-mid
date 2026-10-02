import TranslatedDepthSeven.SmoothConormalGeneration
import TranslatedDepthSeven.SmoothConormalFinrank
import TranslatedDepthSeven.EquationFamilyTangentBaseChange

/-!
# Selecting local equations at a smooth point

Let a finite family generate the kernel of a surjective local presentation.
If the source and target of the presentation are smooth in the precise local
sense and their residual differential dimensions are `N` and `s`, then
`N - s` members of the given family and `N - s` ambient differential
coordinates have a nonzero selected minor.  Those selected members generate
the entire local kernel.

This is the finite linear-algebra and Nakayama step.  It makes no assertion
about spreading the selected equations to an integral model.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct
open KaehlerDifferential IsLocalRing

universe u v

private theorem span_one_tmul_local_eq_top_of_span_eq_top
    {R S M ι : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [Algebra R S]
    (v : ι → M) (hv : Submodule.span R (Set.range v) = ⊤) :
    Submodule.span S
      (Set.range (fun i ↦ (1 : S) ⊗ₜ[R] v i)) = ⊤ := by
  have hbase :
      (Submodule.span R (Set.range v)).baseChange S =
        (⊤ : Submodule R M).baseChange S :=
    congrArg (fun p : Submodule R M ↦ p.baseChange S) hv
  rw [Submodule.baseChange_span, Submodule.baseChange_top] at hbase
  have himage :
      (TensorProduct.mk R S M 1) '' Set.range v =
        Set.range (fun i ↦ (1 : S) ⊗ₜ[R] v i) := by
    ext x
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨v i, ⟨i, rfl⟩, rfl⟩
  rwa [himage] at hbase

/-- Select an expected-size nonsingular residual Jacobian block from any
finite generating family of the local kernel.  The same selected elements
generate the exact kernel ideal. -/
theorem exists_selected_localKernel_generators_and_minor
    {k : Type u} {S : Type v} [Field k] [CommRing S]
    [Algebra k S] [IsLocalRing S]
    (P : Algebra.Extension k S)
    [IsLocalRing P.Ring]
    [Algebra.FormallySmooth k P.Ring]
    [Module.Free P.Ring Ω[P.Ring⁄k]]
    [Module.Finite P.Ring Ω[P.Ring⁄k]]
    (hker : P.ker.FG)
    [Algebra.FormallySmooth k S]
    {N s n : ℕ}
    (hambient : Module.finrank (ResidueField S)
      (ResidueField S ⊗[S] P.CotangentSpace) = N)
    (htarget : Module.finrank (ResidueField S)
      (ResidueField S ⊗[S] Ω[S⁄k]) = s)
    (F : Fin n → P.Ring)
    (hF : Ideal.span (Set.range F) = P.ker)
    (ambientCoordinates :
      (ResidueField S ⊗[S] P.CotangentSpace) ≃ₗ[ResidueField S]
        (Fin N → ResidueField S)) :
    ∃ rows : Fin (N - s) → Fin n,
      ∃ cols : Fin (N - s) → Fin N,
        Function.Injective rows ∧ Function.Injective cols ∧
          Matrix.det (Matrix.of (fun i j ↦
            ambientCoordinates
              ((P.cotangentComplex.baseChange (ResidueField S))
                ((1 : ResidueField S) ⊗ₜ[S]
                  Algebra.Extension.Cotangent.mk
                    (⟨F (rows i), hF.le
                      (Ideal.subset_span ⟨rows i, rfl⟩)⟩ : P.ker)))
              (cols j))) ≠ 0 ∧
          Ideal.span (Set.range fun i ↦ F (rows i)) = P.ker := by
  classical
  let rel : Fin n → P.ker := fun i ↦
    ⟨F i, hF.le (Ideal.subset_span ⟨i, rfl⟩)⟩
  let V := ResidueField S ⊗[S] P.Cotangent
  let W := ResidueField S ⊗[S] P.CotangentSpace
  let fK : V →ₗ[ResidueField S] W :=
    P.cotangentComplex.baseChange (ResidueField S)
  let w : Fin n → V := fun i ↦
    (1 : ResidueField S) ⊗ₜ[S]
      Algebra.Extension.Cotangent.mk (rel i)
  let v : Fin n → Fin N → ResidueField S := fun i ↦
    ambientCoordinates (fK (w i))
  have hcot : Submodule.span S
      (Set.range fun i ↦ Algebra.Extension.Cotangent.mk (rel i)) = ⊤ := by
    exact Algebra.Extension.Cotangent.span_eq_top_of_span_eq_ker F hF
  have hwspan : Submodule.span (ResidueField S) (Set.range w) = ⊤ := by
    exact span_one_tmul_local_eq_top_of_span_eq_top _ hcot
  have hVfinite : Module.Finite (ResidueField S) V := by
    have hfiniteCotangentRing : Module.Finite P.Ring P.Cotangent := by
      have : Module.Finite P.Ring P.ker :=
        ⟨(Submodule.fg_top P.ker).mpr hker⟩
      exact Module.Finite.of_surjective _
        Algebra.Extension.Cotangent.mk_surjective
    letI : Module.Finite S P.Cotangent :=
      Module.Finite.of_restrictScalars_finite P.Ring S P.Cotangent
    infer_instance
  have hVrank : Module.finrank (ResidueField S) V = N - s := by
    exact finrank_residueTensor_extensionCotangent_eq_sub
      P hker hambient htarget
  have hinj : Function.Injective fK := by
    rw [show fK = P.cotangentComplex.baseChange (ResidueField S) from rfl,
      LinearMap.baseChange_eq_ltensor]
    exact (Algebra.FormallySmooth.iff_injective_lTensor_residueField P hker).mp
      (inferInstance : Algebra.FormallySmooth k S)
  have hfKrange : Module.finrank (ResidueField S)
      (LinearMap.range fK) = N - s := by
    have h := fK.finrank_range_add_finrank_ker
    rw [LinearMap.ker_eq_bot.mpr hinj, finrank_bot, add_zero, hVrank] at h
    exact h
  have hvspan : Submodule.span (ResidueField S) (Set.range v) =
      (LinearMap.range fK).map ambientCoordinates.toLinearMap := by
    calc
      Submodule.span (ResidueField S) (Set.range v) =
          (Submodule.span (ResidueField S) (Set.range w)).map
            (ambientCoordinates.toLinearMap.comp fK) := by
        rw [Submodule.map_span]
        congr 1
        exact Set.range_comp (f := w)
          (g := ambientCoordinates.toLinearMap.comp fK)
      _ = (LinearMap.range fK).map ambientCoordinates.toLinearMap := by
        rw [hwspan, Submodule.map_top, LinearMap.range_comp]
  have hvrank : Module.finrank (ResidueField S)
      (Submodule.span (ResidueField S) (Set.range v)) = N - s := by
    rw [hvspan, LinearEquiv.finrank_map_eq ambientCoordinates, hfKrange]
  obtain ⟨rows, cols, hrows, hcols, hminor⟩ :=
    TangentBaseChange.exists_nonzero_minor_of_finrank_span_ge
      v (by rw [hvrank])
  let g : Fin (N - s) → P.ker := fun i ↦ rel (rows i)
  have hgenerate : Ideal.span
      (Set.range fun i ↦ ((g i : P.ker) : P.Ring)) = P.ker := by
    apply extension_ker_eq_span_of_smooth_finranks_and_selectedMinor
      P hker hambient htarget g ambientCoordinates cols
    simpa only [g, rel, v, w, fK] using hminor
  refine ⟨rows, cols, hrows, hcols, ?_, ?_⟩
  · simpa only [rel, v, w, fK] using hminor
  · simpa only [g, rel] using hgenerate

end

end TranslatedDepthSeven
