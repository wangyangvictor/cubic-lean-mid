import CubicTenVariables.ProjectiveMicrolocalDepth
import CubicTenVariables.GeometryTen
import CubicTenVariables.HyperplaneFrames
import HessianTheorem11.UnconditionalCutDimension

/-! A uniform characteristic-zero bound for every nonzero normal. Cutting
the singular cone of a hyperplane section by one normal derivative places
it in the ambient singular cone. The already proved homogeneous cut theorem
and the ten-variable ambient dimension bound therefore give dimension six.
No Zak statement, finite-field estimate, or new literature input is used. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.MicrolocalUniversalDepthBound
open MvPolynomial HessianTheorem11
open ProjectiveMicrolocalData ProjectiveMicrolocalDepth
open BihomogeneousIncidenceFamily FiniteIncidenceDepth

/-- Every actual nonzero-normal hyperplane section has singular cone of
affine dimension at most six. The hyperplane frame is constructed. -/
theorem section_fiber_dimension_le_six (F : MvPolynomial (Fin 10) ℤ)
    (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (v : GeometricPoint 10) (hv : v ≠ 0) :
    affineDimension (TerminalSectionIncidence.sectionSingularFiber
      (geometricPolynomial (map (Int.castRingHom ℚ) F)) v) ≤ (6 : Dimension) := by
  let A : AnisotropicCubic 10 := ⟨map (Int.castRingHom ℚ) F,hhom.map _,hAn⟩
  obtain ⟨B,hB,hRange⟩ := HyperplaneFrames.exists_frame (n := 9) v hv
  have hs : affineDimension (BibleHyperplanes.singularCone
      (geometricPolynomial A.polynomial)) ≤ (5 : Dimension) :=
    CubicTenVariables.Geometry.singularDimension_le_five A
  have hd := BibleHyperplanes.section_singular_dimension_le
    UnconditionalCutDimension.homogeneousCutDimensionInput B hB
      (geometricPolynomial A.polynomial) (geometric_homogeneous A.homogeneous) hs
  rw [← TerminalSectionIncidence.frame_singularCone_image_eq_fiber
    (geometricPolynomial A.polynomial) (geometric_homogeneous A.homogeneous) v hv B hRange]
  change affineDimension (B.mulVecLin '' BibleHyperplanes.singularCone
    (PolynomialRestriction.restrict B (geometricPolynomial A.polynomial))) ≤ (6 : Dimension)
  rw [affineDimension_linearMap_image B.mulVecLin hB]
  exact hd

/-- The same bound holds for the literal polynomial microlocal incidence
fiber, using only its supplied incidence containment. -/
theorem fiber_dimension_le_six {t : ℕ} {F : MvPolynomial (Fin 10) ℤ}
    {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
    (h : Geometry F f) (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (v : GeometricPoint 10) (hv : v ≠ 0) :
    affineDimension (fiber f GeometricField v) ≤ (6 : Dimension) := by
  rw [← pointFiber_geometricIncidence]
  exact (affineDimension_mono
    (ConormalTerminalComparison.pointFiber_subset_section _ _
      (incidence_subset_section h) v)).trans
        (section_fiber_dimension_le_six F hhom hAn v hv)

/-- In particular, the actual geometric depth-seven locus has no nonzero
normal. No assertion about whether the origin belongs is necessary. -/
theorem depth_seven_subset_origin {t : ℕ} {F : MvPolynomial (Fin 10) ℤ}
    {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
    (h : Geometry F f) (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F)) :
    depth f 7 ⊆ ({0} : Set (GeometricPoint 10)) := by
  rw [depth_eq_fiber_dimension]
  intro v hv
  change v = 0
  by_contra hne
  have hn : (7 : Dimension) ≤ (6 : Dimension) :=
    hv.trans (fiber_dimension_le_six h hhom hAn v hne)
  norm_num at hn

theorem depth_ge_seven_subset_origin {t j : ℕ} {F : MvPolynomial (Fin 10) ℤ}
    {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
    (h : Geometry F f) (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F)) (hj : 7 ≤ j) :
    depth f j ⊆ ({0} : Set (GeometricPoint 10)) :=
  (depth_antitone hj).trans (depth_seven_subset_origin h hhom hAn)

end CubicTenVariables.MicrolocalUniversalDepthBound
