import CubicTenVariables.TerminalGaloisStability
import CubicTenVariables.IntegralClosedSetModel
import CubicTenVariables.GeometricTerminalBound

/-! Fixed integral models of the full geometric bad-normal closures.
These are not identified here with the raw bad-parameter sets. In particular,
this file alone does not provide avoidance for every normal outside the raw
locus, or containment of bad loci after reduction modulo a prime. -/

noncomputable section
namespace CubicTenVariables.TerminalIntegralClosureModels
open MvPolynomial HessianTheorem11 BibleProjectiveGeometry
open TerminalSectionIncidence TerminalProjectiveDimension RationalConeClosure
open RationalComponentDescent AffineProductGeometry

def nonzeroClosure {n : ℕ} (Z : Set (GeometricPoint n)) : Set (GeometricPoint n) :=
  geometricClosure {v | v ∈ Z ∧ v ≠ 0} ∪ {0}

theorem nonzeroClosure_closed {n : ℕ} (Z : Set (GeometricPoint n)) :
    AlgebraicallyClosedSet (nonzeroClosure Z) :=
  (algebraicallyClosedSet_geometricClosure _).union origin_closed

theorem zero_mem_nonzeroClosure {n : ℕ} (Z : Set (GeometricPoint n)) :
    (0 : GeometricPoint n) ∈ nonzeroClosure Z := Or.inr rfl

theorem subset_nonzeroClosure {n : ℕ} (Z : Set (GeometricPoint n)) :
    Z ⊆ nonzeroClosure Z := by
  intro v hv
  by_cases h : v = 0
  · exact Or.inr h
  · exact Or.inl (subset_geometricClosure _ ⟨hv, h⟩)

theorem nonzeroClosure_eq_closure_union_origin {n : ℕ}
    (Z : Set (GeometricPoint n)) :
    nonzeroClosure Z = geometricClosure (Z ∪ {0}) := by
  apply le_antisymm
  · rintro v (hv | hv)
    · exact geometricClosure_mono (fun _ hz => Or.inl hz.1) hv
    · exact subset_geometricClosure _ (Or.inr hv)
  · apply geometricClosure_subset_closed _ (nonzeroClosure_closed Z)
    rintro v (hv | hv)
    · exact subset_nonzeroClosure Z hv
    · exact Or.inr hv

theorem nonzeroClosure_isAffineCone {n : ℕ} (Z : Set (GeometricPoint n))
    (hZ : IsAffineCone Z) : IsAffineCone (nonzeroClosure Z) := by
  rw [nonzeroClosure_eq_closure_union_origin]
  apply geometricClosure_isAffineCone_of_rational_smul
  rintro a x (hx | hx)
  · exact Or.inl (hZ _ x hx)
  · rw [Set.mem_singleton_iff] at hx
    simp only [hx, smul_zero, Set.mem_union, Set.mem_singleton_iff, or_true]

def sectionClosure {n : ℕ} (F : RationalPolynomial n) (t : ℕ) :
    Set (GeometricPoint n) :=
  nonzeroClosure (TerminalBadNormals.badNormals (geometricPolynomial F) t)

def gaussClosure {n : ℕ} (F : RationalPolynomial n) (t : ℕ) :
    Set (GeometricPoint n) :=
  nonzeroClosure (GaussTerminalBound.badNormals (geometricPolynomial F) t)

theorem sectionClosure_eq_projective {n : ℕ} (F : RationalPolynomial n)
    (hF : F.IsHomogeneous 3) (t : ℕ) :
    sectionClosure F t = geometricClosure {v : GeometricPoint n |
      (t : Dimension) ≤ projectiveDimension (sectionSingularFiber (geometricPolynomial F) v)
        ∧ v ≠ 0} ∪ {0} := by
  have he : {v : GeometricPoint n |
      ((t+1 : ℕ) : Dimension) ≤ affineDimension
        (sectionSingularFiber (geometricPolynomial F) v) ∧ v ≠ 0} =
      {v : GeometricPoint n | (t : Dimension) ≤ projectiveDimension
        (sectionSingularFiber (geometricPolynomial F) v) ∧ v ≠ 0} := by
    ext v
    exact and_congr (sectionSingularFiber_projective_threshold _
      (geometric_homogeneous hF) v t).symm Iff.rfl
  exact congrArg (fun Z : Set (GeometricPoint n) => geometricClosure Z ∪ {0}) he

theorem sectionClosure_closed {n : ℕ} (F : RationalPolynomial n) (t : ℕ) :
    AlgebraicallyClosedSet (sectionClosure F t) := nonzeroClosure_closed _

theorem gaussClosure_closed {n : ℕ} (F : RationalPolynomial n) (t : ℕ) :
    AlgebraicallyClosedSet (gaussClosure F t) := nonzeroClosure_closed _

theorem sectionClosure_isAffineCone {n : ℕ} (F : RationalPolynomial n) (t : ℕ) :
    IsAffineCone (sectionClosure F t) :=
  nonzeroClosure_isAffineCone _ (TerminalBadNormals.badNormals_isAffineCone _ t)

theorem gaussBadNormals_isAffineCone {n : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous 3) (t : ℕ) : IsAffineCone (GaussTerminalBound.badNormals F t) := by
  intro a v hv
  have hsub : GaussTerminalBound.fiber F v ⊆ GaussTerminalBound.fiber F (a • v) := by
    intro x hx
    simpa only [point_join, normal_join, one_smul] using
      GaussGraph.graph_bicone_smul F hF (join x v) hx 1 a
  change (t : Dimension) ≤ projectiveDimension (GaussTerminalBound.fiber F v) at hv
  change (t : Dimension) ≤ projectiveDimension (GaussTerminalBound.fiber F (a • v))
  apply hv.trans
  unfold projectiveDimension
  apply iSup_mono
  intro i
  exact affineDimension_mono (fun _ hx => ⟨hsub hx.1, hx.2⟩)

theorem gaussClosure_isAffineCone {n : ℕ} (F : RationalPolynomial n)
    (hF : F.IsHomogeneous 3) (t : ℕ) : IsAffineCone (gaussClosure F t) :=
  nonzeroClosure_isAffineCone _
    (gaussBadNormals_isAffineCone _ (geometric_homogeneous hF) t)

theorem exists_sectionClosure_equations {n : ℕ} (F : RationalPolynomial n) (t : ℕ) :
    ∃ m : ℕ, ∃ G : Fin m → MvPolynomial (Fin n) ℤ,
      Ideal.span (Set.range (fun i => map (Int.castRingHom GeometricField) (G i))) =
        vanishingIdeal GeometricField (sectionClosure F t) ∧
      ∀ x : GeometricPoint n,
        x ∈ sectionClosure F t ↔ ∀ i, eval₂ (Int.castRingHom GeometricField) x (G i) = 0 := by
  apply IntegralClosedSetModel.exists_integral_equations _ (sectionClosure_closed F t)
  intro σ x hx
  have h : galoisPoint σ '' sectionClosure F t = sectionClosure F t :=
    TerminalGaloisStability.sectionBadCone_stable σ F t
  rw [← h]
  exact ⟨x, hx, rfl⟩

theorem exists_gaussClosure_equations {n : ℕ} (F : RationalPolynomial n) (t : ℕ) :
    ∃ m : ℕ, ∃ G : Fin m → MvPolynomial (Fin n) ℤ,
      Ideal.span (Set.range (fun i => map (Int.castRingHom GeometricField) (G i))) =
        vanishingIdeal GeometricField (gaussClosure F t) ∧
      ∀ x : GeometricPoint n,
        x ∈ gaussClosure F t ↔ ∀ i, eval₂ (Int.castRingHom GeometricField) x (G i) = 0 := by
  apply IntegralClosedSetModel.exists_integral_equations _ (gaussClosure_closed F t)
  intro σ x hx
  have h : galoisPoint σ '' gaussClosure F t = gaussClosure F t :=
    TerminalGaloisStability.gaussBadCone_stable σ F t
  rw [← h]
  exact ⟨x, hx, rfl⟩

theorem ten_sectionClosure_dimension (F : AnisotropicCubic 10) :
    affineDimension (sectionClosure F.polynomial 4) ≤ (4 : Dimension) := by
  rw [sectionClosure_eq_projective F.polynomial F.homogeneous]
  exact GeometricTerminalBound.ten_fourth_section_cone_dimension_le_four F

theorem ten_gaussClosure_dimension (F : AnisotropicCubic 10) :
    affineDimension (gaussClosure F.polynomial 5) ≤ (3 : Dimension) := by
  exact GaussTerminalBound.nonzero_badNormals_cone_dimension_le (t := 5) F
    (by norm_num) (by norm_num)

end CubicTenVariables.TerminalIntegralClosureModels
