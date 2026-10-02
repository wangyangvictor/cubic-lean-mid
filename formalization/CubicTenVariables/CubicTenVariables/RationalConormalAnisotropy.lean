import CubicTenVariables.RationalComponentDescent
import CubicTenVariables.TerminalContactTangent
import HessianTheorem11.ReducedStrictDimension

/-!
# Rational anisotropy excludes a positive-dimensional rational conormal

The tangent annihilator is the actual orthogonal subspace for the coordinate
pairing. Its rational basis is obtained from density of the rational points
of an actual geometric component of the rational closure. Consequently an
anisotropic rational polynomial cannot vanish on that entire annihilator.

For a closed irreducible cone of positive codimension, containment at every
rational smooth point of a nonempty relative open forces a strict dimension
drop on taking rational closure. The containment premise is explicit: this
module proves the arithmetic exclusion and dimension consequence, not a
singular-support or conormal-containment theorem. No homogeneity of the
polynomial and no literature input are needed for these implications.
-/

noncomputable section
namespace CubicTenVariables.RationalConormalAnisotropy

open MvPolynomial HessianTheorem11 Module
open RationalConeClosure RationalConeComponents RationalComponentDescent

/-- A positive-dimensional subspace with an actual rational-coordinate basis
contains an embedded nonzero rational vector. -/
theorem exists_nonzero_rational_vector {n d : ℕ}
    (T : Submodule GeometricField (GeometricPoint n))
    (b : Basis (Fin d) GeometricField T)
    (hb : ∀ i j, ∃ a : ℚ, algebraMap ℚ GeometricField a = (b i).val j)
    (hd : 0 < d) :
    ∃ x : Fin n → ℚ, x ≠ 0 ∧ rationalEmbedding x ∈ T := by
  classical
  let i : Fin d := ⟨0, hd⟩
  choose x hx using hb i
  have he : rationalEmbedding x = (b i).val := funext hx
  refine ⟨x, ?_, he ▸ (b i).property⟩
  intro hz
  apply b.ne_zero i
  apply Subtype.ext
  simpa only [hz, rationalEmbedding_zero] using he.symm

/-- This uses the zero set of the actual coefficient-extended polynomial,
rather than an abstract label for a cubic hypersurface. -/
theorem rational_subspace_not_subset {n d : ℕ}
    (F : RationalPolynomial n) (hF : Anisotropic F)
    (T : Submodule GeometricField (GeometricPoint n))
    (b : Basis (Fin d) GeometricField T)
    (hb : ∀ i j, ∃ a : ℚ, algebraMap ℚ GeometricField a = (b i).val j)
    (hd : 0 < d) : ¬ (T : Set (GeometricPoint n)) ⊆ cubicLocus F := by
  intro hsub
  obtain ⟨x, hx0, hxT⟩ := exists_nonzero_rational_vector T b hb hd
  have hxF := hsub hxT
  change eval (rationalEmbedding x) (geometricPolynomial F) = 0 at hxF
  have hx : eval x F = 0 := by
    apply (algebraMap ℚ GeometricField).injective
    rw [map_zero, map_eval]
    exact hxF
  exact hx0 (hF x hx)

/-- Density of rational points in each actual geometric component supplies
the rational basis; it is not an extra hypothesis on the annihilator. -/
theorem tangent_annihilator_not_subset {n : ℕ}
    (F : RationalPolynomial n) (hF : Anisotropic F)
    (C Z : Set (GeometricPoint n)) (hC : AlgebraicallyClosedSet C)
    (hZ : IsIrreducibleComponent (rationalConeClosure C) Z)
    (q : Fin n → ℚ)
    (hpos : 0 < finrank GeometricField
      (coordinatePairing.orthogonal (affineTangentSpace Z (rationalEmbedding q)))) :
    ¬ (coordinatePairing.orthogonal (affineTangentSpace Z (rationalEmbedding q)) :
      Set (GeometricPoint n)) ⊆ cubicLocus F := by
  obtain ⟨b, hb⟩ := tangent_annihilator_rational_basis C Z hC hZ q
  exact rational_subspace_not_subset F hF _ b hb hpos

/-- At a rational smooth point, positive codimension gives the required
positive annihilator dimension by the nondegenerate coordinate pairing. -/
theorem smooth_tangent_annihilator_not_subset {n z : ℕ}
    (F : RationalPolynomial n) (hF : Anisotropic F)
    (C Z : Set (GeometricPoint n)) (hC : AlgebraicallyClosedSet C)
    (hZ : IsIrreducibleComponent (rationalConeClosure C) Z)
    (hdim : affineDimension Z = (z : Dimension)) (hz : z < n)
    (q : Fin n → ℚ)
    (hsmooth : affineDimension Z =
      (finrank GeometricField (affineTangentSpace Z (rationalEmbedding q)) : Dimension)) :
    ¬ (coordinatePairing.orthogonal (affineTangentSpace Z (rationalEmbedding q)) :
      Set (GeometricPoint n)) ⊆ cubicLocus F := by
  have ht : finrank GeometricField (affineTangentSpace Z (rationalEmbedding q)) = z := by
    rw [hdim] at hsmooth
    exact_mod_cast hsmooth.symm
  apply tangent_annihilator_not_subset F hF C Z hC hZ q
  rw [TerminalContactTangent.finrank_contact_annihilator, ht]
  exact Nat.sub_pos_of_lt hz

/-- If the conormal containment holds on a nonempty relative open of a
closed irreducible cone of positive codimension, its rational points cannot
be Zariski dense. The conclusion uses the actual rational closure, including
its explicitly adjoined origin. -/
theorem rationalConeClosure_ssubset_of_conormal_on_open {n z : ℕ}
    (F : RationalPolynomial n) (hF : Anisotropic F)
    (D : Set (GeometricPoint n)) (hD : AlgebraicallyClosedSet D)
    (hiD : GeometricallyIrreducible D) (hcD : IsAffineCone D)
    (hdim : affineDimension D = (z : Dimension)) (hz : z < n)
    (O : Set (GeometricPoint n)) (hO : RelativelyOpenSet D O) (hne : O.Nonempty)
    (hconormal : ∀ q : Fin n → ℚ, rationalEmbedding q ∈ O →
      affineDimension D =
        (finrank GeometricField (affineTangentSpace D (rationalEmbedding q)) : Dimension) →
      (coordinatePairing.orthogonal (affineTangentSpace D (rationalEmbedding q)) :
        Set (GeometricPoint n)) ⊆ cubicLocus F) :
    rationalConeClosure D ⊂ D := by
  have hzero : (0 : GeometricPoint n) ∈ D := by
    obtain ⟨x, hx⟩ := hiD.nonempty
    simpa only [zero_smul] using hcD 0 x hx
  have hsub : rationalConeClosure D ⊆ D := by
    intro x hx
    rcases rationalConeClosure_subset D hD hx with hx | hx
    · exact hx
    · rw [Set.mem_singleton_iff] at hx
      simpa only [hx] using hzero
  refine Set.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
  intro he
  have hcomponent : IsIrreducibleComponent (rationalConeClosure D) D := by
    rw [he]
    exact ⟨hD, hiD, Set.Subset.refl _, fun _ _ _ h₁ h₂ => Set.Subset.antisymm h₂ h₁⟩
  obtain ⟨q, hqO, hqs⟩ := exists_rational_smooth_point_in_component_open
    D D hD hcomponent O hO hne
  exact smooth_tangent_annihilator_not_subset F hF D D hD hcomponent hdim hz q hqs
    (hconormal q hqO hqs)

/-- The strict dimension drop is proved internally from the strict closed
subset theorem, with no separate rational-point dimension input. -/
theorem rationalConeClosure_dimension_lt_of_conormal_on_open {n z : ℕ}
    (F : RationalPolynomial n) (hF : Anisotropic F)
    (D : Set (GeometricPoint n)) (hD : AlgebraicallyClosedSet D)
    (hiD : GeometricallyIrreducible D) (hcD : IsAffineCone D)
    (hdim : affineDimension D = (z : Dimension)) (hz : z < n)
    (O : Set (GeometricPoint n)) (hO : RelativelyOpenSet D O) (hne : O.Nonempty)
    (hconormal : ∀ q : Fin n → ℚ, rationalEmbedding q ∈ O →
      affineDimension D =
        (finrank GeometricField (affineTangentSpace D (rationalEmbedding q)) : Dimension) →
      (coordinatePairing.orthogonal (affineTangentSpace D (rationalEmbedding q)) :
        Set (GeometricPoint n)) ⊆ cubicLocus F) :
    affineDimension (rationalConeClosure D) < affineDimension D :=
  ReducedStrictDimension.proper_closed _ D (rationalConeClosure_closed D) hD hiD
    (rationalConeClosure_ssubset_of_conormal_on_open F hF D hD hiD hcD hdim hz O hO
      hne hconormal)

end CubicTenVariables.RationalConormalAnisotropy
