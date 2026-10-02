import HessianTheorem11.UnconditionalWeightDescent
import HessianTheorem11.ReducedClosedOrbitZero
import HessianTheorem11.BibleHyperplanes
import HessianTheorem11.BibleProjectiveGeometry
import HessianTheorem11.BibleHyperplaneRank
import HessianTheorem11.BibleLowRank
import HessianTheorem11.BibleVertex
import HessianTheorem11.BibleRestrictions
import HessianTheorem11.NormalCrossGenericRank

/-! The geometric hyperplane conclusions in Theorem I.1.1(iii). Every
section is the actual pullback along an injective hyperplane frame. Projective
dimension is computed on actual normalized affine charts, and is invariant
under injective changes of coordinates. -/

noncomputable section
namespace HessianTheorem11.BibleHyperplanes
open MvPolynomial Module Matrix PolynomialRestriction BibleProjectiveGeometry

/-- The projective singular dimension is independent of coordinates on the
same actual linear section. The proof identifies both images with the
annihilator of the ambient differential on their common subspace. -/
theorem section_singular_dimension_eq_of_same_range
    (AP : AffineProjectiveDimensionInput) {m k n : ℕ}
    (B : Matrix (Fin n) (Fin m) GeometricField) (hB : Function.Injective B.mulVec)
    (C : Matrix (Fin n) (Fin k) GeometricField) (hC : Function.Injective C.mulVec)
    (hBC : LinearMap.range B.mulVecLin = LinearMap.range C.mulVecLin)
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3) :
    projectiveDimension (singularCone (restrict B F)) =
      projectiveDimension (singularCone (restrict C F)) := by
  have he : B.mulVec '' singularCone (restrict B F) =
      C.mulVec '' singularCone (restrict C F) := by
    rw [frame_singular_image, frame_singular_image, hBC]
  calc
    projectiveDimension (singularCone (restrict B F)) =
        projectiveDimension (B.mulVec '' singularCone (restrict B F)) :=
      (projectiveDimension_linearMap_image AP B.mulVecLin hB _ (singularCone_closed _)
        (singularCone_cone _ (homogeneous_restrict B F hF))).symm
    _ = projectiveDimension (C.mulVec '' singularCone (restrict C F)) := congrArg _ he
    _ = projectiveDimension (singularCone (restrict C F)) :=
      projectiveDimension_linearMap_image AP C.mulVecLin hC _ (singularCone_closed _)
        (singularCone_cone _ (homogeneous_restrict C F hF))

/-- Vertex points of the actual hyperplane equation lie on the ambient cubic
and have ambient Hessian rank at most two. -/
theorem section_vertex_image_on_rank_two {m : ℕ}
    (B : Matrix (Fin (m+1)) (Fin m) GeometricField) (hB : Function.Injective B.mulVec)
    (F : GeometricPolynomial (m+1)) (hF : F.IsHomogeneous 3)
    (u : GeometricPoint m)
    (hu : u ∈ BibleVertex.affineVertex (restrict B F) (homogeneous_restrict B F hF)) :
    eval (B.mulVec u) F = 0 ∧ (hessian F (B.mulVec u)).rank ≤ 2 := by
  have hh : hessian (restrict B F) u = 0 := hu
  constructor
  · rw [← eval_restrict, eval_cubic_eq_polarization (homogeneous_restrict B F hF)]
    simp [polarization, hh]
  · apply rank_le_two_of_hyperplane_restriction_zero B hB _
    rw [← hessian_restrict, hh]

theorem section_vertex_affine_dimension_le
    (AC : AffineComponentsInput) (GP : GenericConePointSelectionInput)
    (DT : SymmetricDeterminantalTangentInput) {m : ℕ}
    (B : Matrix (Fin (m+1)) (Fin m) GeometricField) (hB : Function.Injective B.mulVec)
    (F : GeometricPolynomial (m+1)) (hF : F.IsHomogeneous 3) (hsemi : WeightSemistable F) :
    affineDimension (BibleVertex.affineVertex (restrict B F)
      (homogeneous_restrict B F hF) : Set (GeometricPoint m)) ≤ 2 := by
  apply le_trans (affineDimension_le_of_image_subset B hB _
    {x | eval x F = 0 ∧ (hessian F x).rank ≤ 2} ?_)
    (BibleLowRank.on_cubic_rank_two_dimension_le AC GP DT F hF hsemi)
  exact section_vertex_image_on_rank_two B hB F hF

theorem section_vertex_finrank_le
    (AC : AffineComponentsInput) (GP : GenericConePointSelectionInput)
    (DT : SymmetricDeterminantalTangentInput) (GR : GenericRankOpenInput) {m : ℕ}
    (B : Matrix (Fin (m+1)) (Fin m) GeometricField) (hB : Function.Injective B.mulVec)
    (F : GeometricPolynomial (m+1)) (hF : F.IsHomogeneous 3) (hsemi : WeightSemistable F) :
    finrank GeometricField (BibleVertex.affineVertex (restrict B F)
      (homogeneous_restrict B F hF)) ≤ 2 := by
  have h := section_vertex_affine_dimension_le AC GP DT B hB F hF hsemi
  rw [affineDimension_submodule_from_generic_rank GR] at h
  exact_mod_cast h

theorem section_vertex_projective_dimension_le
    (AP : AffineProjectiveDimensionInput)
    (AC : AffineComponentsInput) (GP : GenericConePointSelectionInput)
    (DT : SymmetricDeterminantalTangentInput) {m : ℕ}
    (B : Matrix (Fin (m+1)) (Fin m) GeometricField) (hB : Function.Injective B.mulVec)
    (F : GeometricPolynomial (m+1)) (hF : F.IsHomogeneous 3) (hsemi : WeightSemistable F) :
    projectiveDimension (BibleVertex.affineVertex (restrict B F)
      (homogeneous_restrict B F hF) : Set (GeometricPoint m)) ≤ 1 := by
  apply projectiveDimension_le AP _ (algebraicallyClosedSet_submodule _)
    (fun a x hx => Submodule.smul_mem _ a hx)
  exact section_vertex_affine_dimension_le AC GP DT B hB F hF hsemi

/-- In twelve ambient variables the full geometric hyperplane package:
irreducible cubic equation, projective singular locus dimension at most six,
and projective maximal vertex dimension at most one. -/
theorem geometric_hyperplane_section
    (HI : HomogeneousCutDimensionInput) (AP : AffineProjectiveDimensionInput)
    (GR : GenericRankOpenInput) (AC : AffineComponentsInput)
    (GP : GenericConePointSelectionInput) (DT : SymmetricDeterminantalTangentInput)
    (F : GeometricPolynomial 12) (hF : F.IsHomogeneous 3) (hsemi : WeightSemistable F)
    (hs : affineDimension (singularCone F) ≤ 6)
    (B : Matrix (Fin 12) (Fin 11) GeometricField) (hB : Function.Injective B.mulVec) :
    Irreducible (restrict B F) ∧
      projectiveDimension (singularCone (restrict B F)) ≤ 6 ∧
      projectiveDimension (BibleVertex.affineVertex (restrict B F)
        (homogeneous_restrict B F hF) : Set (GeometricPoint 11)) ≤ 1 := by
  refine ⟨section_irreducible HI GR B hB F hF hs (by norm_num), ?_,
    section_vertex_projective_dimension_le AP AC GP DT B hB F hF hsemi⟩
  apply projectiveDimension_le AP _ (singularCone_closed _)
    (singularCone_cone _ (homogeneous_restrict B F hF))
  exact section_singular_dimension_le HI B hB F hF hs

/-- The homogeneous coordinate ring of every geometric hyperplane section
is a domain; this records scheme-theoretic reducedness and integrality. -/
theorem hyperplane_coordinateRing_isDomain
    (HI : HomogeneousCutDimensionInput) (GR : GenericRankOpenInput)
    (F : GeometricPolynomial 12) (hF : F.IsHomogeneous 3)
    (hs : affineDimension (singularCone F) ≤ 6)
    (B : Matrix (Fin 12) (Fin 11) GeometricField) (hB : Function.Injective B.mulVec) :
    IsDomain (GeometricPolynomial 11 ⧸ Ideal.span {restrict B F}) := by
  have hi := section_irreducible HI GR B hB F hF hs (by norm_num)
  letI : (Ideal.span {restrict B F}).IsPrime :=
    (Ideal.span_singleton_prime hi.ne_zero).mpr hi.prime
  infer_instance

/-- The maximal vertex bounds for every geometric hyperplane of an actual
twelve-variable rational anisotropic cubic. -/
theorem section_vertex_dimension_twelve
    (AC : AffineComponentsInput) (GP : GenericConePointSelectionInput)
    (DT : SymmetricDeterminantalTangentInput) (GR : GenericRankOpenInput)
    (AP : AffineProjectiveDimensionInput)
    (F : AnisotropicCubic 12)
    (B : Matrix (Fin 12) (Fin 11) GeometricField) (hB : Function.Injective B.mulVec) :
    finrank GeometricField (BibleVertex.affineVertex (restrict B (geometricPolynomial F.polynomial))
      (homogeneous_restrict B _ (geometric_homogeneous F.homogeneous))) ≤ 2 ∧
    projectiveDimension (BibleVertex.affineVertex (restrict B (geometricPolynomial F.polynomial))
      (homogeneous_restrict B _ (geometric_homogeneous F.homogeneous)) :
        Set (GeometricPoint 11)) ≤ 1 := by
  have hsemi := UnconditionalWeightDescent.anisotropic_geometric_weightSemistable F
    (by norm_num)
  exact ⟨section_vertex_finrank_le AC GP DT GR B hB _
    (geometric_homogeneous F.homogeneous) hsemi,
    section_vertex_projective_dimension_le AP AC GP DT B hB _
      (geometric_homogeneous F.homogeneous) hsemi⟩

/-- Irreducibility here gives a nonempty geometric projective section,
as expected for a cubic equation in eleven variables. -/
theorem section_projective_nonempty
    (AD : AffineHypersurfaceDimensionInput) (P : GeometricPolynomial 11)
    (hP : Irreducible P) : (projectiveLocus (polynomialHypersurface P)).Nonempty := by
  have he : ∃ x ∈ polynomialHypersurface P, x ≠ 0 := by
    by_contra h
    push_neg at h
    have hs : polynomialHypersurface P ⊆ {0} := by
      intro x hx
      exact Set.mem_singleton_iff.mpr (h x hx)
    have hd := affineDimension_mono hs
    rw [AD.hypersurface P hP, affineDimension_singleton] at hd
    norm_num at hd
  obtain ⟨x, hx, hx0⟩ := he
  exact ⟨Projectivization.mk GeometricField x hx0, x, hx, hx0, rfl⟩

end HessianTheorem11.BibleHyperplanes
