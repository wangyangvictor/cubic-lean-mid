import CubicTenVariables.GaussSectionComparison
import CubicTenVariables.TerminalSingularSpan
import CubicTenVariables.GeometryTen

/-!
The all-geometric bad-section bound, using the actual section-singularity
equations and normalized projective dimensions. A large section component
either lies in the Gauss fiber or is one of finitely many large components
of the ambient singular locus. In the latter case its annihilating normals
have the required dimension. No bad-parameter closedness, properness, or
reduction-modulo-primes assertion is used.
-/

noncomputable section
namespace CubicTenVariables.GeometricTerminalBound
open MvPolynomial HessianTheorem11 BibleProjectiveGeometry
open TerminalSectionIncidence TerminalProjectiveDimension
open scoped BigOperators

/-- An irreducible set in a finite closed cover is contained in one member.
This is proved directly by multiplying separating polynomials. -/
theorem subset_one_of_finite_closed_cover {n c : ℕ}
    (Z : Set (GeometricPoint n)) (hiZ : GeometricallyIrreducible Z)
    (D : Fin c → Set (GeometricPoint n)) (hD : ∀ i, AlgebraicallyClosedSet (D i))
    (hsub : Z ⊆ ⋃ i, D i) : ∃ i, Z ⊆ D i := by
  classical
  by_contra hn
  have hsep : ∀ i, ∃ P : GeometricPolynomial n,
      P ∈ vanishingIdeal GeometricField (D i) ∧
      P ∉ vanishingIdeal GeometricField Z := by
    intro i
    have hnot : ¬ Z ⊆ D i := fun h => hn ⟨i, h⟩
    obtain ⟨x, hx, hxi⟩ := Set.not_subset.mp hnot
    have hp : ∃ P ∈ vanishingIdeal GeometricField (D i), eval x P ≠ 0 := by
      by_contra h
      push_neg at h
      exact hxi ((hD i) ▸ h)
    obtain ⟨P, hPi, hPx⟩ := hp
    exact ⟨P, hPi, fun hP => hPx (hP x hx)⟩
  choose P hPi hPZ using hsep
  have hprod : ∏ i, P i ∈ vanishingIdeal GeometricField Z := by
    intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hsub hx)
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hPi i x hxi)
  letI : (vanishingIdeal GeometricField Z).IsPrime := hiZ
  obtain ⟨i, _, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp hprod
  exact hPZ i hi

/-- The large component selected in the singular branch must equal an
actual member of the finite decomposition of the ambient singular locus. -/
theorem singular_component_eq_cover_member {n t c : ℕ} (F : AnisotropicCubic n)
    (hsing : singularDimension F.polynomial ≤ ((t+1 : ℕ) : Dimension))
    (D : Fin c → Set (GeometricPoint n))
    (hcover : singularLocus F.polynomial = ⋃ i, D i)
    (hD : ∀ i, IsIrreducibleComponent (singularLocus F.polynomial) (D i))
    (Z : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z)
    (hiZ : GeometricallyIrreducible Z) (hZs : Z ⊆ singularLocus F.polynomial)
    (hdZ : ((t+1 : ℕ) : Dimension) ≤ affineDimension Z) :
    ∃ i, Z = D i := by
  obtain ⟨i, hi⟩ := subset_one_of_finite_closed_cover Z hiZ D
    (fun j => (hD j).closed) (hcover ▸ hZs)
  refine ⟨i, ?_⟩
  by_contra hne
  have hlt := ReducedStrictDimension.proper_closed Z (D i) hZ (hD i).closed
    (hD i).irreducible (Set.ssubset_iff_subset_ne.mpr ⟨hi, hne⟩)
  have hupper : affineDimension (D i) ≤ ((t+1 : ℕ) : Dimension) :=
    (affineDimension_mono (hD i).subset).trans hsing
  exact (not_lt_of_ge hdZ) (hlt.trans_le hupper)

/-- The actual nonzero bad normals have the claimed affine-closure bound.
The singular dimension premise is affine here; the public endpoint below
expresses it in the manuscript's projective convention. -/
theorem nonzero_badNormals_closure_dimension_le {n t : ℕ} (F : AnisotropicCubic n)
    (hn : 4 ≤ n) (ht : n < 3*t)
    (hsing : singularDimension F.polynomial ≤ ((t+1 : ℕ) : Dimension)) :
    affineDimension (geometricClosure
      {v : GeometricPoint n | (t : Dimension) ≤ projectiveDimension
        (sectionSingularFiber (geometricPolynomial F.polynomial) v) ∧ v ≠ 0}) ≤
      ((n - (t+2) : ℕ) : Dimension) := by
  classical
  let G := geometricPolynomial F.polynomial
  have hG : G.IsHomogeneous 3 := geometric_homogeneous F.homogeneous
  obtain ⟨c, D, hcover, hD⟩ := ReducedMaximalComponent.finite_components
    (singularLocus F.polynomial) (BibleHyperplanes.singularCone_closed G)
  let I := {i : Fin c // ((t+1 : ℕ) : Dimension) ≤ affineDimension (D i)}
  let A : I → Set (GeometricPoint n) := fun i => TerminalSingularSpan.annihilator (D i)
  have hsub : {v : GeometricPoint n | (t : Dimension) ≤ projectiveDimension
      (sectionSingularFiber G v) ∧ v ≠ 0} ⊆
      GaussTerminalBound.badNormals G t ∪ ⋃ i, A i := by
    rintro v ⟨hv, hv0⟩
    have hvdim := (sectionSingularFiber_projective_threshold G hG v t).mp hv
    obtain ⟨Z, hZ, hdim⟩ := ReducedMaximalComponent.maximal_dimension_component
      (sectionSingularFiber G v) (sectionSingularFiber_closed G v)
      ⟨0, zero_mem_sectionSingularFiber G hG v⟩
    have hdZ : ((t+1 : ℕ) : Dimension) ≤ affineDimension Z := hdim ▸ hvdim
    rcases GaussSectionComparison.subset_gaussFiber_or_gradient_zero G v hv0 Z
      hZ.closed hZ.irreducible hZ.subset with hg | hs
    · left
      exact (nat_le_projectiveDimension_iff _ (GaussTerminalBound.fiber_closed G v)
        (GaussTerminalBound.fiber_isAffineCone G hG v) t).mpr
        (hdZ.trans (affineDimension_mono hg))
    · have hZs : Z ⊆ singularLocus F.polynomial := hs
      obtain ⟨i, hi⟩ := singular_component_eq_cover_member F hsing D hcover hD Z
        hZ.closed hZ.irreducible hZs hdZ
      right
      apply Set.mem_iUnion.mpr
      refine ⟨⟨i, hi ▸ hdZ⟩, ?_⟩
      apply (TerminalSingularSpan.mem_annihilator_iff (D i) v).mpr
      intro x hx
      rw [← hi] at hx
      exact (dotProduct_comm x v).trans (hZ.subset hx).2.1
  rw [affineDimension_closure]
  apply (affineDimension_mono hsub).trans
  rw [affineDimension_union]
  apply max_le
  · rw [← affineDimension_closure]
    exact GaussTerminalBound.badNormals_closure_dimension_le F hn ht
  · apply affineDimension_fintype_union_le
    intro i
    exact TerminalSingularSpan.annihilator_dimension_le F ht (D i)
      (hD i).closed (hD i).subset i.property

/-- All geometric normals, in the source's projective dimension and affine
cone conventions: close the nonzero bad normals, then adjoin the origin. -/
theorem geometric_projective_terminal_dimension_le {n t : ℕ} (F : AnisotropicCubic n)
    (hn : 4 ≤ n) (ht : n < 3*t)
    (hsing : projectiveDimension (singularLocus F.polynomial) ≤ (t : Dimension)) :
    affineDimension (geometricClosure
      {v : GeometricPoint n | (t : Dimension) ≤ projectiveDimension
        (sectionSingularFiber (geometricPolynomial F.polynomial) v) ∧ v ≠ 0} ∪ {0}) ≤
      ((n - (t+2) : ℕ) : Dimension) := by
  rw [affineDimension_union, affineDimension_origin]
  apply max_le
  · exact nonzero_badNormals_closure_dimension_le F hn ht
      ((projective_singular_dimension_iff F t).mp hsing)
  · exact_mod_cast Nat.zero_le (n - (t+2))

/-- In ten variables the ambient singular-dimension hypothesis follows
from rational anisotropy, so the fourth-stratum endpoint has no extra premise. -/
theorem ten_fourth_section_cone_dimension_le_four (F : AnisotropicCubic 10) :
    affineDimension (geometricClosure
      {v : GeometricPoint 10 | (4 : Dimension) ≤ projectiveDimension
        (sectionSingularFiber (geometricPolynomial F.polynomial) v) ∧ v ≠ 0} ∪ {0}) ≤
      (4 : Dimension) := by
  simpa using geometric_projective_terminal_dimension_le (t := 4) F
    (by norm_num) (by norm_num) (Geometry.projectiveSingularDimension_le_four F)

end CubicTenVariables.GeometricTerminalBound
