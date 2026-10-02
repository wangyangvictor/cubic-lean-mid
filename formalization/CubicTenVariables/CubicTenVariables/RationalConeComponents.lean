import CubicTenVariables.RationalConeClosure
import HessianTheorem11.ReducedMaximalComponent

/-!
# Rational points on the actual geometric components

A finite irreducible decomposition gives a polynomial principal open that
meets any chosen component and avoids every other component. Density in
the whole closed set then implies density on each actual component.
Applied to the rational closure construction, this yields rational points,
and rational smooth points, in every prescribed nonempty component-open.
No irreducibility of the whole rational closure is assumed and no component
is enlarged or replaced by a rational irreducible component.
-/

noncomputable section
namespace CubicTenVariables.RationalConeComponents

open MvPolynomial HessianTheorem11 Module RationalConeClosure

/-- A polynomial principal open meets the chosen actual component and
is contained in it inside X. It is obtained by separating that component
from each of the other members of a proved finite decomposition. -/
theorem exists_component_separator {n : ℕ} (X Z : Set (GeometricPoint n))
    (hX : AlgebraicallyClosedSet X) (hZ : IsIrreducibleComponent X Z) :
    ∃ f : GeometricPolynomial n, f ∉ vanishingIdeal GeometricField Z ∧
      ∀ x ∈ X, eval x f ≠ 0 → x ∈ Z := by
  classical
  obtain ⟨c, D, hcover, hD⟩ := ReducedMaximalComponent.finite_components X hX
  let I := {i : Fin c // D i ≠ Z}
  have hsep (i : I) : ∃ f : GeometricPolynomial n,
      f ∈ vanishingIdeal GeometricField (D i) ∧ f ∉ vanishingIdeal GeometricField Z := by
    have hnsub : ¬ Z ⊆ D i := by
      intro hs
      exact i.property (hZ.maximal (D i) (hD i).closed (hD i).irreducible hs (hD i).subset)
    obtain ⟨z, hzZ, hzD⟩ := Set.not_subset.mp hnsub
    have hex : ∃ f ∈ vanishingIdeal GeometricField (D i), eval z f ≠ 0 := by
      by_contra! hzero
      exact hzD ((hD i).closed ▸ hzero)
    obtain ⟨f, hfD, hfe⟩ := hex
    exact ⟨f, hfD, fun hfZ => hfe (hfZ z hzZ)⟩
  choose f hfD hfZ using hsep
  let g : GeometricPolynomial n := ∏ i : I, f i
  letI : (vanishingIdeal GeometricField Z).IsPrime := hZ.irreducible
  have hg : g ∉ vanishingIdeal GeometricField Z := by
    intro h
    obtain ⟨i, _, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hfZ i hi
  refine ⟨g, hg, ?_⟩
  intro x hx hne
  rw [hcover] at hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  by_cases he : D i = Z
  · exact he ▸ hi
  · exfalso
    apply hne
    dsimp only [g]
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ (⟨i, he⟩ : I)) (hfD ⟨i, he⟩ x hi)

/-- Density of any point set passes to each actual irreducible component
of a closed affine set. The separator is the open complement of the other
components; primality extends density from this open to the component. -/
theorem closure_inter_component_of_dense {n : ℕ}
    (X A Z : Set (GeometricPoint n)) (hX : AlgebraicallyClosedSet X)
    (hdense : geometricClosure A = X) (hZ : IsIrreducibleComponent X Z) :
    geometricClosure (A ∩ Z) = Z := by
  obtain ⟨f, hf, hopen⟩ := exists_component_separator X Z hX hZ
  apply le_antisymm (geometricClosure_subset_closed Set.inter_subset_right hZ.closed)
  intro z hz g hg
  have hfgA : f * g ∈ vanishingIdeal GeometricField A := by
    intro x hx
    change eval x (f * g) = 0
    rw [map_mul]
    by_cases hfx : eval x f = 0
    · simp [hfx]
    · have hxX : x ∈ X := hdense ▸ subset_geometricClosure A hx
      have hgx := hg x ⟨hx, hopen x hxX hfx⟩
      change eval x g = 0 at hgx
      rw [hgx, mul_zero]
  have hfgX : f * g ∈ vanishingIdeal GeometricField X := by
    rw [← hdense, vanishingIdeal_geometricClosure]
    exact hfgA
  have hfgZ := vanishingIdeal_anti_mono hZ.subset hfgX
  exact ((hZ.irreducible.mem_or_mem hfgZ).resolve_left hf) z hz

/-- Each geometric component of the rational closure has dense actual
rational points, even when the entire closure is reducible. -/
theorem rationalPoints_dense_in_component {n : ℕ}
    (C Z : Set (GeometricPoint n)) (hC : AlgebraicallyClosedSet C)
    (hZ : IsIrreducibleComponent (rationalConeClosure C) Z) :
    geometricClosure (rationalEmbedding '' rationalPoints Z) = Z := by
  have hd := closure_inter_component_of_dense (rationalConeClosure C)
    (rationalEmbedding '' rationalPoints (rationalConeClosure C)) Z
    (rationalConeClosure_closed C) (rationalPoints_dense C hC) hZ
  have he : (rationalEmbedding '' rationalPoints (rationalConeClosure C)) ∩ Z =
      rationalEmbedding '' rationalPoints Z := by
    ext x
    constructor
    · rintro ⟨⟨q, _, rfl⟩, hqZ⟩
      exact ⟨q, hqZ, rfl⟩
    · rintro ⟨q, hqZ, rfl⟩
      exact ⟨⟨q, hZ.subset hqZ, rfl⟩, hqZ⟩
  rwa [he] at hd

/-- Actual rational-point selection in any nonempty relative open of the
chosen component. No whole-closure irreducibility is a premise. -/
theorem exists_rational_point_in_component_open {n : ℕ}
    (C Z : Set (GeometricPoint n)) (hC : AlgebraicallyClosedSet C)
    (hZ : IsIrreducibleComponent (rationalConeClosure C) Z)
    (W : Set (GeometricPoint n)) (hW : RelativelyOpenSet Z W) (hne : W.Nonempty) :
    ∃ x : Fin n → ℚ, rationalEmbedding x ∈ W := by
  obtain ⟨y, hy, hyW⟩ := ReducedGenericImageTangent.dense_inter_open_nonempty
    (rationalPoints_dense_in_component C Z hC hZ) hW hne
  obtain ⟨x, _, rfl⟩ := hy
  exact ⟨x, hyW⟩

/-- Smooth rational-point selection on that exact geometric component,
with its actual reduced tangent dimension and affine Krull dimension. -/
theorem exists_rational_smooth_point_in_component_open {n : ℕ}
    (C Z : Set (GeometricPoint n)) (hC : AlgebraicallyClosedSet C)
    (hZ : IsIrreducibleComponent (rationalConeClosure C) Z)
    (W : Set (GeometricPoint n)) (hW : RelativelyOpenSet Z W) (hne : W.Nonempty) :
    ∃ x : Fin n → ℚ, rationalEmbedding x ∈ W ∧
      affineDimension Z =
        (finrank GeometricField (affineTangentSpace Z (rationalEmbedding x)) : Dimension) := by
  obtain ⟨G⟩ := Unconditional.genericRankOpen.choose Z hZ.closed hZ.irreducible
    (fun _ : Fin 0 => 0)
    (0 : GeometricPoint n →ₗ[GeometricField] Matrix (Fin 0) (Fin 0) GeometricField)
  have hopen := G.isOpen.inter hW
  have hn := ReducedGenericImageTangent.dense_inter_open_nonempty G.dense hW hne
  obtain ⟨x, hxG, hxW⟩ := exists_rational_point_in_component_open C Z hC hZ _ hopen hn
  refine ⟨x, hxW, ?_⟩
  rw [G.smooth _ hxG]
  exact G.dimension_base

/-- When the prescribed open avoids zero, the selected smooth rational
point is nonzero as required for a projective normal. -/
theorem exists_nonzero_rational_smooth_point_in_component_open {n : ℕ}
    (C Z : Set (GeometricPoint n)) (hC : AlgebraicallyClosedSet C)
    (hZ : IsIrreducibleComponent (rationalConeClosure C) Z)
    (W : Set (GeometricPoint n)) (hW : RelativelyOpenSet Z W) (hne : W.Nonempty)
    (hzero : (0 : GeometricPoint n) ∉ W) :
    ∃ x : Fin n → ℚ, x ≠ 0 ∧ rationalEmbedding x ∈ W ∧
      affineDimension Z =
        (finrank GeometricField (affineTangentSpace Z (rationalEmbedding x)) : Dimension) := by
  obtain ⟨x, hx, hsmooth⟩ :=
    exists_rational_smooth_point_in_component_open C Z hC hZ W hW hne
  exact ⟨x, fun hz => hzero (by simpa [hz] using hx), hx, hsmooth⟩

end CubicTenVariables.RationalConeComponents
