import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Smooth.Local
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import TranslatedDepthSeven.SmoothConormalGeneration

/-!
# The unconditional local dimension bridge

For a Noetherian local ring, the minimum number of generators of the
maximal ideal is the dimension of its cotangent space.  Krull's height
theorem then gives the unconditional inequality from Krull dimension to
embedding dimension.

This file deliberately does not assert the reverse inequality.  That is the
regular-local-ring theorem, and is the genuinely missing ingredient in the
present Mathlib route from formal smoothness to a Krull-dimension formula.
-/

namespace TranslatedDepthSeven

noncomputable section

open Module Submodule
open scoped TensorProduct

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The minimum number of generators of the maximal ideal is the vector-space
dimension of `m / m^2`. -/
theorem maximalIdeal_spanFinrank_eq_finrank_cotangentSpace :
    (IsLocalRing.maximalIdeal R).spanFinrank =
      finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) := by
  let m : Ideal R := IsLocalRing.maximalIdeal R
  let K : Type u := IsLocalRing.ResidueField R
  have hmfg : m.FG := IsNoetherian.noetherian m
  apply le_antisymm
  · let b : Basis (Fin (finrank K (IsLocalRing.CotangentSpace R))) K
        (IsLocalRing.CotangentSpace R) := Module.finBasis K _
    let lift : IsLocalRing.CotangentSpace R → m :=
      (m.toCotangent_surjective.hasRightInverse.choose)
    have hlift : Function.RightInverse lift m.toCotangent :=
      m.toCotangent_surjective.hasRightInverse.choose_spec
    let g : Fin (finrank K (IsLocalRing.CotangentSpace R)) → m :=
      fun i ↦ lift (b i)
    have hspanCot : span K (m.toCotangent '' Set.range g) = ⊤ := by
      have hrange : m.toCotangent '' Set.range g = Set.range b := by
        ext x
        constructor
        · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
          exact ⟨i, (hlift (b i)).symm⟩
        · rintro ⟨i, rfl⟩
          exact ⟨g i, ⟨i, rfl⟩, hlift (b i)⟩
      rw [hrange, b.span_eq]
    have hspanSubtype : span R (Set.range g) = ⊤ :=
      IsLocalRing.CotangentSpace.span_image_eq_top_iff.mp hspanCot
    have hspanVal : span R (Set.range fun i ↦ ((g i : m) : R)) = m := by
      have hmap := congrArg (Submodule.map m.subtype) hspanSubtype
      rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at hmap
      have himage : m.subtype '' Set.range g =
          Set.range (fun i ↦ ((g i : m) : R)) := by
        ext x
        constructor
        · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
          exact ⟨i, rfl⟩
        · rintro ⟨i, rfl⟩
          exact ⟨g i, ⟨i, rfl⟩, rfl⟩
      rwa [himage] at hmap
    change m.spanFinrank ≤ finrank K (IsLocalRing.CotangentSpace R)
    rw [← hspanVal]
    have hg : Function.Injective g := by
      intro i j hij
      apply b.injective
      rw [← hlift (b i), ← hlift (b j)]
      exact congrArg m.toCotangent (by simpa only [g] using hij)
    have hgval : Function.Injective (fun i ↦ ((g i : m) : R)) :=
      m.subtype_injective.comp hg
    exact (spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans
      (by rw [Set.ncard_range_of_injective hgval, Nat.card_fin])
  · let generators : Set R := m.generators
    have hgeneratorsFinite : generators.Finite :=
      Submodule.FG.finite_generators hmfg
    letI : Fintype generators := hgeneratorsFinite.fintype
    let g : generators → m := fun x ↦
      ⟨x.1, Submodule.FG.generators_mem m x.2⟩
    have hspanSubtype : span R (Set.range g) = ⊤ := by
      apply (Submodule.map_injective_of_injective m.subtype_injective)
      rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
      have himage : m.subtype '' Set.range g = generators := by
        ext x
        constructor
        · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
          exact i.2
        · intro hx
          exact ⟨g ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
      rw [himage, m.span_generators]
    have hspanCot : span K (Set.range fun i ↦ m.toCotangent (g i)) = ⊤ := by
      change span K (Set.range (m.toCotangent ∘ g)) = ⊤
      rw [Set.range_comp]
      exact IsLocalRing.CotangentSpace.span_image_eq_top_iff.mpr hspanSubtype
    have hle := finrank_le_of_span_eq_top hspanCot
    have hcard : Fintype.card generators = generators.ncard := by
      calc
        Fintype.card generators = generators.toFinset.card :=
          (Set.toFinset_card generators).symm
        _ = generators.ncard :=
          (Set.ncard_eq_toFinset_card generators).symm
    rw [hcard] at hle
    change finrank K (IsLocalRing.CotangentSpace R) ≤ m.spanFinrank
    simpa only [generators, Submodule.FG.generators_ncard hmfg] using hle

/-- Krull dimension is at most embedding dimension for a Noetherian local
ring, expressed using the residual cotangent space. -/
theorem ringKrullDim_le_finrank_cotangentSpace_via_spanFinrank [Nontrivial R] :
    ringKrullDim R ≤
      (finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) :
        WithBot ℕ∞) := by
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    ← maximalIdeal_spanFinrank_eq_finrank_cotangentSpace]
  exact WithBot.coe_le_coe.mpr <| Ideal.height_le_spanFinrank _
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top

section ExtensionEmbeddingDimension

universe v w x

variable {k : Type v} {S : Type w} [CommRing k] [Field S] [Algebra k S]

/-- For a surjection from a Noetherian local ring to a field, the minimum
number of generators of the kernel equals the dimension of the extension's
cotangent module. -/
theorem extension_ker_spanFinrank_eq_finrank_cotangent
    (P : Algebra.Extension.{x} k S) [IsLocalRing P.Ring]
    [IsNoetherianRing P.Ring] :
    P.ker.spanFinrank = finrank S P.Cotangent := by
  have hkerfg : P.ker.FG := IsNoetherian.noetherian P.ker
  letI : Module.Finite S P.Cotangent :=
    Algebra.Extension.Cotangent.finite hkerfg
  apply le_antisymm
  · let b : Basis (Fin (finrank S P.Cotangent)) S P.Cotangent :=
      Module.finBasis S _
    let lift : P.Cotangent → P.ker :=
      Algebra.Extension.Cotangent.mk_surjective.hasRightInverse.choose
    have hlift : Function.RightInverse lift Algebra.Extension.Cotangent.mk :=
      Algebra.Extension.Cotangent.mk_surjective.hasRightInverse.choose_spec
    let g : Fin (finrank S P.Cotangent) → P.ker := fun i ↦ lift (b i)
    have hspanCot : span S
        (Set.range fun i ↦ Algebra.Extension.Cotangent.mk (g i)) = ⊤ := by
      have hrange :
          Set.range (fun i ↦ Algebra.Extension.Cotangent.mk (g i)) = Set.range b := by
        ext z
        constructor
        · rintro ⟨i, rfl⟩
          exact ⟨i, (hlift (b i)).symm⟩
        · rintro ⟨i, rfl⟩
          exact ⟨i, hlift (b i)⟩
      rw [hrange, b.span_eq]
    have hspanVal : Ideal.span (Set.range fun i ↦ ((g i : P.ker) : P.Ring)) =
        P.ker :=
      extension_ker_eq_span_of_cotangent_span P hkerfg g hspanCot
    rw [← hspanVal]
    have hg : Function.Injective g := by
      intro i j hij
      apply b.injective
      rw [← hlift (b i), ← hlift (b j)]
      exact congrArg Algebra.Extension.Cotangent.mk (by simpa only [g] using hij)
    have hgval : Function.Injective (fun i ↦ ((g i : P.ker) : P.Ring)) :=
      P.ker.subtype_injective.comp hg
    exact (spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans
      (by rw [Set.ncard_range_of_injective hgval, Nat.card_fin])
  · let generators : Set P.Ring := P.ker.generators
    have hgeneratorsFinite : generators.Finite :=
      Submodule.FG.finite_generators hkerfg
    letI : Fintype generators := hgeneratorsFinite.fintype
    let g : generators → P.ker := fun z ↦
      ⟨z.1, Submodule.FG.generators_mem P.ker z.2⟩
    have hspanVal : Ideal.span (Set.range fun i ↦ ((g i : P.ker) : P.Ring)) =
        P.ker := by
      have hrange : Set.range (fun i ↦ ((g i : P.ker) : P.Ring)) = generators := by
        ext z
        constructor
        · rintro ⟨i, rfl⟩
          exact i.2
        · intro hz
          exact ⟨⟨z, hz⟩, rfl⟩
      rw [hrange]
      simpa only [generators] using P.ker.span_generators
    have hspanCot : span S
        (Set.range fun i ↦ Algebra.Extension.Cotangent.mk (g i)) = ⊤ :=
      Algebra.Extension.Cotangent.span_eq_top_of_span_eq_ker _ hspanVal
    have hle := finrank_le_of_span_eq_top hspanCot
    have hcard : Fintype.card generators = generators.ncard := by
      calc
        Fintype.card generators = generators.toFinset.card :=
          (Set.toFinset_card generators).symm
        _ = generators.ncard :=
          (Set.ncard_eq_toFinset_card generators).symm
    rw [hcard] at hle
    simpa only [generators, Submodule.FG.generators_ncard hkerfg] using hle

end ExtensionEmbeddingDimension

section ResidualDifferentials

universe v

variable (k : Type v) [CommRing k] [Algebra k R]

/-- The residue map, regarded as an extension over the ground ring. -/
noncomputable def residueExtension :
    Algebra.Extension k (IsLocalRing.ResidueField R) :=
  Algebra.Extension.ofSurjective
    (IsScalarTower.toAlgHom k R (IsLocalRing.ResidueField R))
    IsLocalRing.residue_surjective

/-- If both the local algebra and its residue field are formally smooth over
the ground ring, and the residue field has no relative differentials, the
residual conormal map is an isomorphism.  For a rational point over a field,
the latter two hypotheses are automatic after identifying the residue field
with the ground field. -/
theorem residueExtension_cotangentComplex_bijective
    [Algebra.FormallySmooth k R]
    [Algebra.FormallySmooth k (IsLocalRing.ResidueField R)]
    [Subsingleton Ω[IsLocalRing.ResidueField R⁄k]] :
    Function.Bijective (residueExtension (R := R) k).cotangentComplex := by
  let P := residueExtension (R := R) k
  have hinj : Function.Injective P.cotangentComplex := by
    letI : Algebra.FormallySmooth k P.Ring := by
      change Algebra.FormallySmooth k R
      infer_instance
    obtain ⟨l, hl⟩ :=
      (Algebra.Extension.formallySmooth_iff_split_injection P).mp
        (inferInstance : Algebra.FormallySmooth k (IsLocalRing.ResidueField R))
    apply Function.LeftInverse.injective (g := l)
    intro x
    exact DFunLike.congr_fun hl x
  have hsurj : Function.Surjective P.cotangentComplex := by
    rw [← LinearMap.range_eq_top,
      ← P.exact_cotangentComplex_toKaehler.linearMap_ker_eq]
    have hz : P.toKaehler = 0 := Subsingleton.elim _ _
    rw [hz, LinearMap.ker_zero]
  exact ⟨hinj, hsurj⟩

/-- Numerical form of the residual conormal isomorphism. -/
theorem finrank_residueExtension_cotangent_eq_residualKaehler
    [Algebra.FormallySmooth k R]
    [Algebra.FormallySmooth k (IsLocalRing.ResidueField R)]
    [Subsingleton Ω[IsLocalRing.ResidueField R⁄k]] :
    finrank (IsLocalRing.ResidueField R)
        (residueExtension (R := R) k).Cotangent =
      finrank (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField R ⊗[R] Ω[R⁄k]) := by
  exact (LinearEquiv.ofBijective
    (residueExtension (R := R) k).cotangentComplex
    (residueExtension_cotangentComplex_bijective (R := R) k)).finrank_eq

/-- The same numerical isomorphism with the source written as the usual
cotangent space `m / m^2` of the local ring. -/
theorem finrank_cotangentSpace_eq_residualKaehler
    [Algebra.FormallySmooth k R]
    [Algebra.FormallySmooth k (IsLocalRing.ResidueField R)]
    [Subsingleton Ω[IsLocalRing.ResidueField R⁄k]] :
    finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) =
      finrank (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField R ⊗[R] Ω[R⁄k]) := by
  let P := residueExtension (R := R) k
  have hker : P.ker = IsLocalRing.maximalIdeal R := by
    change RingHom.ker (algebraMap R (IsLocalRing.ResidueField R)) =
      IsLocalRing.maximalIdeal R
    rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ker_residue]
  letI : IsLocalRing P.Ring := by
    change IsLocalRing R
    infer_instance
  letI : IsNoetherianRing P.Ring := by
    change IsNoetherianRing R
    infer_instance
  calc
    finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) =
        (IsLocalRing.maximalIdeal R).spanFinrank :=
      maximalIdeal_spanFinrank_eq_finrank_cotangentSpace.symm
    _ = P.ker.spanFinrank := congrArg Submodule.spanFinrank hker.symm
    _ = finrank (IsLocalRing.ResidueField R) P.Cotangent :=
      extension_ker_spanFinrank_eq_finrank_cotangent P
    _ = finrank (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField R ⊗[R] Ω[R⁄k]) :=
      finrank_residueExtension_cotangent_eq_residualKaehler (R := R) k

/-- The fully proved direction of the smooth local dimension comparison:
Krull dimension is at most the residual differential dimension.  Equality
requires the reverse, regular-local-ring inequality. -/
theorem ringKrullDim_le_finrank_residualKaehler
    [Nontrivial R]
    [Algebra.FormallySmooth k R]
    [Algebra.FormallySmooth k (IsLocalRing.ResidueField R)]
    [Subsingleton Ω[IsLocalRing.ResidueField R⁄k]] :
    ringKrullDim R ≤
      (finrank (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField R ⊗[R] Ω[R⁄k]) : WithBot ℕ∞) := by
  rw [← finrank_cotangentSpace_eq_residualKaehler (R := R) k]
  exact ringKrullDim_le_finrank_cotangentSpace_via_spanFinrank

/-- A standard-smooth algebra of relative dimension `n` has residual
differential dimension `n` after any base change to a residue field. -/
theorem finrank_residualKaehler_of_isStandardSmoothOfRelativeDimension
    [Nontrivial R] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n k R] :
    finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] Ω[R⁄k]) = n := by
  letI : Algebra.IsStandardSmooth k R :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  rw [Module.finrank_baseChange]
  exact Module.finrank_eq_of_rank_eq
    (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n)

end ResidualDifferentials

end

end TranslatedDepthSeven
