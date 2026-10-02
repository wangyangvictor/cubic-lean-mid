import CubicTenVariables.HomogeneousFamilyBadLocus
import CubicTenVariables.SectionHomogeneousFamily
import CubicTenVariables.TerminalFifthComparison

/-! Closedness of the actual section bad-normal loci and identification of
the terminal closure models with the raw loci, with the origin adjoined.
The fifth Gauss locus is treated by its proved comparison with sections. -/

noncomputable section
namespace CubicTenVariables.TerminalBadParameterClosed
open MvPolynomial HessianTheorem11 BibleProjectiveGeometry
open TerminalIntegralClosureModels TerminalSectionIncidence RationalConeClosure

/-- The actual section fiber-dimension locus is closed, before any closure
is imposed on its definition. The proof uses finite monomial certificates. -/
theorem section_badNormals_closed {n : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous 3) (t : ℕ) :
    AlgebraicallyClosedSet (TerminalBadNormals.badNormals F t) := by
  have he (v : GeometricPoint n) :
      HomogeneousFamilyBadLocus.fiber (SectionHomogeneousFamily.equation F) v =
        sectionSingularFiber F v := SectionHomogeneousFamily.specialized_zeroSet F v
  have h := HomogeneousFamilyBadLocus.badParameters_closed
    (SectionHomogeneousFamily.equation F) SectionHomogeneousFamily.degree
    (SectionHomogeneousFamily.equation_isHomogeneous F hF)
    SectionHomogeneousFamily.degree_pos t
  simpa only [HomogeneousFamilyBadLocus.badParameters, he] using h

theorem nonzeroClosure_eq_of_closed {n : ℕ} (Z : Set (GeometricPoint n))
    (hZ : AlgebraicallyClosedSet Z) : nonzeroClosure Z = Z ∪ {0} :=
  (nonzeroClosure_eq_closure_union_origin Z).trans (hZ.union origin_closed)

/-- The section closure adds exactly the deliberately adjoined origin;
it adds no other geometric or rational normal. -/
theorem sectionClosure_eq_badNormals_union_origin {n : ℕ}
    (F : RationalPolynomial n) (hF : F.IsHomogeneous 3) (t : ℕ) :
    sectionClosure F t = TerminalBadNormals.badNormals (geometricPolynomial F) t ∪ {0} :=
  nonzeroClosure_eq_of_closed _
    (section_badNormals_closed _ (geometric_homogeneous hF) t)

theorem mem_sectionClosure_iff {n : ℕ}
    (F : RationalPolynomial n) (hF : F.IsHomogeneous 3) (t : ℕ) (v : GeometricPoint n) :
    v ∈ sectionClosure F t ↔ v = 0 ∨
      (t : Dimension) ≤ projectiveDimension (sectionSingularFiber (geometricPolynomial F) v) := by
  rw [sectionClosure_eq_badNormals_union_origin F hF t]
  change (((t+1 : ℕ) : Dimension) ≤ affineDimension
    (sectionSingularFiber (geometricPolynomial F) v) ∨ v = 0) ↔ _
  rw [← TerminalProjectiveDimension.sectionSingularFiber_projective_threshold _
    (geometric_homogeneous hF) v t, or_comm]

/-- For n=10, the fifth Gauss closure is the raw fifth Gauss locus with
the origin adjoined. Its identification uses the section family only. -/
theorem gaussClosure_eq_badNormals_union_origin (F : AnisotropicCubic 10) :
    gaussClosure F.polynomial 5 =
      GaussTerminalBound.badNormals (geometricPolynomial F.polynomial) 5 ∪ {0} := by
  rw [← TerminalFifthComparison.ten_fifth_closures_eq F,
    sectionClosure_eq_badNormals_union_origin F.polynomial F.homogeneous 5]
  ext v
  by_cases hv : v = 0
  · simp only [Set.mem_union, Set.mem_singleton_iff, hv, or_true]
  · exact or_congr (TerminalFifthComparison.ten_fifth_bad_iff F v hv) Iff.rfl

theorem mem_ten_gaussClosure_iff (F : AnisotropicCubic 10) (v : GeometricPoint 10) :
    v ∈ gaussClosure F.polynomial 5 ↔ v = 0 ∨
      (5 : Dimension) ≤ projectiveDimension
        (GaussTerminalBound.fiber (geometricPolynomial F.polynomial) v) := by
  rw [gaussClosure_eq_badNormals_union_origin]
  change (((5 : ℕ) : Dimension) ≤ projectiveDimension
    (GaussTerminalBound.fiber (geometricPolynomial F.polynomial) v) ∨ v = 0) ↔ _
  norm_num only [Nat.cast_ofNat]
  exact or_comm

end CubicTenVariables.TerminalBadParameterClosed
