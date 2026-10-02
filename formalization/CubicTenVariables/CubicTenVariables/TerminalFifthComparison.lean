import CubicTenVariables.TerminalIntegralClosureModels

/-! Above the ambient singular dimension, the section and Gauss bad-normal
loci coincide at nonzero normals. At n=10 this replaces the fifth Gauss locus
by the fifth locus of the explicit section-incidence family. -/

noncomputable section
namespace CubicTenVariables.TerminalFifthComparison
open MvPolynomial HessianTheorem11 BibleProjectiveGeometry
open TerminalSectionIncidence TerminalProjectiveDimension
open TerminalIntegralClosureModels

theorem section_bad_iff_gauss_bad {n t : ℕ} (F : AnisotropicCubic n)
    (hsing : singularDimension F.polynomial ≤ (t : Dimension))
    (v : GeometricPoint n) (hv : v ≠ 0) :
    v ∈ TerminalBadNormals.badNormals (geometricPolynomial F.polynomial) t ↔
      v ∈ GaussTerminalBound.badNormals (geometricPolynomial F.polynomial) t := by
  let G := geometricPolynomial F.polynomial
  have hG : G.IsHomogeneous 3 := geometric_homogeneous F.homogeneous
  constructor
  · intro hbad
    obtain ⟨Z,hZ,hdim⟩ := ReducedMaximalComponent.maximal_dimension_component
      (sectionSingularFiber G v) (sectionSingularFiber_closed G v)
      ⟨0,zero_mem_sectionSingularFiber G hG v⟩
    have hdZ : ((t+1 : ℕ) : Dimension) ≤ affineDimension Z := hdim ▸ hbad
    rcases GaussSectionComparison.subset_gaussFiber_or_gradient_zero G v hv Z
      hZ.closed hZ.irreducible hZ.subset with hg | hs
    · exact (nat_le_projectiveDimension_iff _ (GaussTerminalBound.fiber_closed G v)
        (GaussTerminalBound.fiber_isAffineCone G hG v) t).mpr
        (hdZ.trans (affineDimension_mono hg))
    · have hsub : Z ⊆ singularLocus F.polynomial := hs
      have hle : ((t+1 : ℕ) : Dimension) ≤ (t : Dimension) :=
        hdZ.trans ((affineDimension_mono hsub).trans hsing)
      exact (not_le_of_gt (show (t : Dimension) < ((t+1 : ℕ) : Dimension) by
        exact_mod_cast Nat.lt_succ_self t) hle).elim
  · intro hbad
    have hd := (nat_le_projectiveDimension_iff _ (GaussTerminalBound.fiber_closed G v)
      (GaussTerminalBound.fiber_isAffineCone G hG v) t).mp hbad
    exact hd.trans (affineDimension_mono
      (GaussTerminalBound.fiber_subset_sectionSingularFiber G hG v))

/-- Only rational anisotropy and the cubic hypotheses packaged in F remain;
the strict ambient-singular threshold is proved in ten variables. -/
theorem ten_fifth_bad_iff (F : AnisotropicCubic 10)
    (v : GeometricPoint 10) (hv : v ≠ 0) :
    v ∈ TerminalBadNormals.badNormals (geometricPolynomial F.polynomial) 5 ↔
      v ∈ GaussTerminalBound.badNormals (geometricPolynomial F.polynomial) 5 := by
  apply section_bad_iff_gauss_bad F _ v hv
  exact (projective_singular_dimension_iff F 4).mp
    (Geometry.projectiveSingularDimension_le_four F)

/-- Equality of the full geometric closures, with the origin convention
retained. No raw-parameter closedness premise is needed for this comparison. -/
theorem ten_fifth_closures_eq (F : AnisotropicCubic 10) :
    sectionClosure F.polynomial 5 = gaussClosure F.polynomial 5 := by
  have he : {v : GeometricPoint 10 |
      v ∈ TerminalBadNormals.badNormals (geometricPolynomial F.polynomial) 5 ∧ v ≠ 0} =
      {v : GeometricPoint 10 |
      v ∈ GaussTerminalBound.badNormals (geometricPolynomial F.polynomial) 5 ∧ v ≠ 0} := by
    ext v
    constructor
    · rintro ⟨h,hv⟩
      exact ⟨(ten_fifth_bad_iff F v hv).mp h,hv⟩
    · rintro ⟨h,hv⟩
      exact ⟨(ten_fifth_bad_iff F v hv).mpr h,hv⟩
  exact congrArg (fun Z : Set (GeometricPoint 10) => geometricClosure Z ∪ {0}) he

end CubicTenVariables.TerminalFifthComparison
