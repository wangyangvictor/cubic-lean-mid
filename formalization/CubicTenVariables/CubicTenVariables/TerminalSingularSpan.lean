import CubicTenVariables.TerminalContactTangent
import HessianTheorem11.UnconditionalDimensionResults
import HessianTheorem11.NormalCrossGenericRank
import HessianTheorem11.ReducedStrictDimension

/-!
Large closed subsets of the actual geometric singular cone have a span
of at least one greater dimension. Their literal annihilating normals form
a closed linear subspace with the terminal dimension bound. The proof uses
rational anisotropy only; no anisotropy over the geometric field is assumed.
-/

noncomputable section
namespace CubicTenVariables.TerminalSingularSpan
open MvPolynomial HessianTheorem11 Module
open scoped BigOperators

theorem submodule_irreducible {n : ℕ}
    (L : Submodule GeometricField (GeometricPoint n)) :
    GeometricallyIrreducible (L : Set (GeometricPoint n)) := by
  have h := geometricallyIrreducible_univ.linearMap_image (submoduleCoordinateMap L)
  simpa only [Set.image_univ, submoduleCoordinateMap_range] using h

/-- Equality of a closed set's dimension with the dimension of its linear
span forces it to be that entire span. Irreducibility of the set is unnecessary. -/
theorem eq_span_of_dimension_ge {n : ℕ} (C : Set (GeometricPoint n))
    (hC : AlgebraicallyClosedSet C)
    (hd : ((finrank GeometricField (Submodule.span GeometricField C) : ℕ) : Dimension) ≤
      affineDimension C) :
    C = (Submodule.span GeometricField C : Set (GeometricPoint n)) := by
  have hsub : C ⊆ (Submodule.span GeometricField C : Set (GeometricPoint n)) :=
    Submodule.subset_span
  by_contra hne
  have hlt := ReducedStrictDimension.proper_closed C (Submodule.span GeometricField C)
    hC (algebraicallyClosedSet_submodule _) (submodule_irreducible _)
    (Set.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  rw [affineDimension_submodule_from_generic_rank Unconditional.genericRankOpen] at hlt
  exact (not_lt_of_ge hd) hlt

/-- The source span bound. This is valid for any closed subset of the
singular cone satisfying the lower dimension bound, not only components. -/
theorem span_finrank_ge {n t : ℕ} (F : AnisotropicCubic n) (ht : n < 3*t)
    (C : Set (GeometricPoint n)) (hC : AlgebraicallyClosedSet C)
    (hCs : C ⊆ singularLocus F.polynomial)
    (hd : ((t+1 : ℕ) : Dimension) ≤ affineDimension C) :
    t+2 ≤ finrank GeometricField (Submodule.span GeometricField C) := by
  let L := Submodule.span GeometricField C
  change t+2 ≤ finrank GeometricField L
  have hsub : C ⊆ (L : Set (GeometricPoint n)) := Submodule.subset_span
  have hdim := affineDimension_mono hsub
  rw [affineDimension_submodule_from_generic_rank Unconditional.genericRankOpen] at hdim
  have hlow : t+1 ≤ finrank GeometricField L := by exact_mod_cast hd.trans hdim
  have htop : finrank GeometricField L ≤ n := by
    simpa using Submodule.finrank_le L
  have hn : 0 < n := by omega
  by_contra hsmall
  have hle : finrank GeometricField L ≤ t+1 := by omega
  have hCd : ((finrank GeometricField L : ℕ) : Dimension) ≤ affineDimension C :=
    (show ((finrank GeometricField L : ℕ) : Dimension) ≤ ((t+1 : ℕ) : Dimension)
      by exact_mod_cast hle).trans hd
  have he := eq_span_of_dimension_ge C hC hCd
  have hLs : (L : Set (GeometricPoint n)) ⊆ singularLocus F.polynomial := by
    rw [← he]
    exact hCs
  have hbound := BibleRestrictions.singular_subspace_finrank_bound F hn L hLs
  omega

/-- Actual normals whose dot product vanishes on the entire geometric span. -/
def annihilator {n : ℕ} (C : Set (GeometricPoint n)) :
    Submodule GeometricField (GeometricPoint n) :=
  coordinatePairing.orthogonal (Submodule.span GeometricField C)

theorem mem_annihilator_iff {n : ℕ} (C : Set (GeometricPoint n)) (v : GeometricPoint n) :
    v ∈ annihilator C ↔ ∀ x ∈ C, dotProduct x v = 0 := by
  constructor
  · intro h x hx
    exact h x (Submodule.subset_span hx)
  · intro h x hx
    change dotProduct x v = 0
    induction hx using Submodule.span_induction with
    | mem x hx => exact h x hx
    | zero => simp
    | add x y hx hy hx0 hy0 => simp [add_dotProduct, hx0, hy0]
    | smul a x hx hx0 => simp [smul_dotProduct, hx0]

theorem annihilator_closed {n : ℕ} (C : Set (GeometricPoint n)) :
    AlgebraicallyClosedSet (annihilator C : Set (GeometricPoint n)) :=
  algebraicallyClosedSet_submodule _

theorem annihilator_finrank {n : ℕ} (C : Set (GeometricPoint n)) :
    finrank GeometricField (annihilator C) =
      n - finrank GeometricField (Submodule.span GeometricField C) :=
  TerminalContactTangent.finrank_contact_annihilator _

/-- The annihilator is a closed subspace of the required affine dimension. -/
theorem annihilator_dimension_le {n t : ℕ} (F : AnisotropicCubic n) (ht : n < 3*t)
    (C : Set (GeometricPoint n)) (hC : AlgebraicallyClosedSet C)
    (hCs : C ⊆ singularLocus F.polynomial)
    (hd : ((t+1 : ℕ) : Dimension) ≤ affineDimension C) :
    affineDimension (annihilator C : Set (GeometricPoint n)) ≤
      ((n - (t+2) : ℕ) : Dimension) := by
  rw [affineDimension_submodule_from_generic_rank Unconditional.genericRankOpen,
    annihilator_finrank]
  have hspan := span_finrank_ge F ht C hC hCs hd
  exact_mod_cast (show n - finrank GeometricField (Submodule.span GeometricField C) ≤
    n - (t+2) by omega)

/-- Fully set-theoretic form: all geometric normals annihilating the
actual singular subset, with no extra span or linearity hypothesis. -/
theorem literal_annihilating_normals_dimension_le {n t : ℕ}
    (F : AnisotropicCubic n) (ht : n < 3*t)
    (C : Set (GeometricPoint n)) (hC : AlgebraicallyClosedSet C)
    (hCs : C ⊆ singularLocus F.polynomial)
    (hd : ((t+1 : ℕ) : Dimension) ≤ affineDimension C) :
    AlgebraicallyClosedSet {v : GeometricPoint n | ∀ x ∈ C, dotProduct x v = 0} ∧
      affineDimension {v : GeometricPoint n | ∀ x ∈ C, dotProduct x v = 0} ≤
        ((n - (t+2) : ℕ) : Dimension) := by
  have he : {v : GeometricPoint n | ∀ x ∈ C, dotProduct x v = 0} =
      (annihilator C : Set (GeometricPoint n)) := by
    ext v
    exact (mem_annihilator_iff C v).symm
  rw [he]
  exact ⟨annihilator_closed C, annihilator_dimension_le F ht C hC hCs hd⟩

end CubicTenVariables.TerminalSingularSpan
