import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Krull dimension is bounded by cotangent dimension

For a Noetherian local ring, Krull's height theorem and Nakayama's
description of generators give the standard inequality
`dim R ≤ dim_k m / m²`.
-/

namespace TranslatedDepthSeven

noncomputable section

open IsLocalRing

universe u

/-- The Krull dimension of a Noetherian local ring is at most the dimension
of its Zariski cotangent space. -/
theorem ringKrullDim_le_finrank_cotangentSpace
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ringKrullDim R ≤
      (Module.finrank (ResidueField R) (CotangentSpace R) : WithBot ℕ∞) := by
  let n := Module.finrank (ResidueField R) (CotangentSpace R)
  let b : Module.Basis (Fin n) (ResidueField R) (CotangentSpace R) :=
    Module.finBasis (ResidueField R) (CotangentSpace R)
  choose g hg using fun i ↦ (maximalIdeal R).toCotangent_surjective (b i)
  have hspanSub : Submodule.span R (Set.range g) = ⊤ := by
    apply (CotangentSpace.span_image_eq_top_iff (R := R)).mp
    rw [show (maximalIdeal R).toCotangent '' Set.range g = Set.range b by
      ext x
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, (hg i).symm⟩
      · rintro ⟨i, rfl⟩
        exact ⟨g i, ⟨i, rfl⟩, hg i⟩]
    exact b.span_eq
  let s : Set R := Set.range fun i ↦ ((g i : maximalIdeal R) : R)
  have hs : s.Finite := Set.finite_range _
  have hspanIdeal : Ideal.span s = maximalIdeal R := by
    have hmap := congrArg (Submodule.map (maximalIdeal R).subtype) hspanSub
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at hmap
    have hset : (maximalIdeal R).subtype '' Set.range g = s := by
      ext x
      constructor
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨g i, ⟨i, rfl⟩, rfl⟩
    change Submodule.span R s = (maximalIdeal R : Submodule R R)
    rw [← hset]
    exact hmap
  have hmin : maximalIdeal R ∈ (Ideal.span s).minimalPrimes := by
    rw [hspanIdeal, Ideal.minimalPrimes_eq_subsingleton_self]
    simp
  calc
    ringKrullDim R = (maximalIdeal R).height :=
      (IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)).symm
    _ ≤ (s.ncard : WithBot ℕ∞) :=
      by exact_mod_cast Ideal.height_le_card_of_mem_minimalPrimes_span hs hmin
    _ ≤ (n : WithBot ℕ∞) := by
      exact_mod_cast (show s.ncard ≤ n by
        simpa only [s, ← Set.image_univ, Set.ncard_univ, Nat.card_fin] using
          (Set.ncard_image_le (f := fun i : Fin n ↦ ((g i : maximalIdeal R) : R))
            (s := Set.univ) Set.finite_univ))

end

end TranslatedDepthSeven
