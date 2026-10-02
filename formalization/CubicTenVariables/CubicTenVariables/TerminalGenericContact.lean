import CubicTenVariables.TerminalContactTangent
import CubicTenVariables.TerminalSectionIncidence
import HessianTheorem11.UnconditionalDimensionResults

/-!
# Generic contact annihilators from proved generic image tangency

For actual polynomial maps P,Q on an irreducible closed affine set Y,
the equations F(P)=0 and Q·P=0 imply the contact calculation on a
nonempty dense open. Surjectivity onto the tangent of the actual image
closure is supplied by the proved generic-rank/image-tangent theorem;
the radial vector is supplied by the affine-cone property of that closure.
No generic smoothness interface, rational point, rational descent,
fiber-dimension bound, or terminal-stratum dimension estimate is assumed.
-/

noncomputable section
namespace CubicTenVariables.TerminalGenericContact

open MvPolynomial HessianTheorem11 Matrix PolynomialRestriction
open TerminalContactTangent TerminalSectionIncidence

/-- The contact annihilator conclusion holds on an actual nonempty dense
open. The proportionality scalar is nonzero; neither a tangent-lifting
hypothesis nor a generic-image-tangent input is a premise. -/
theorem exists_dense_open_contact_annihilator {m n : ℕ}
    (F : GeometricPolynomial n) (P Q : Fin n → GeometricPolynomial m)
    (Y : Set (GeometricPoint m)) (hY : AlgebraicallyClosedSet Y)
    (hiY : GeometricallyIrreducible Y)
    (hF : ∀ y ∈ Y, eval (polynomialMap P y) F = 0)
    (hpair : ∀ y ∈ Y, dotProduct (polynomialMap Q y) (polynomialMap P y) = 0)
    (W : Set (GeometricPoint m)) (hW : RelativelyOpenSet Y W)
    (hdW : geometricClosure W = Y)
    (hcontact : ∀ y ∈ W, ∃ α : GeometricField, α ≠ 0 ∧
      gradient F (polynomialMap P y) = α • polynomialMap Q y)
    (hcone : IsAffineCone (geometricClosure (polynomialMap Q '' Y))) :
    ∃ O : Set (GeometricPoint m), RelativelyOpenSet Y O ∧ O ⊆ W ∧
      geometricClosure O = Y ∧ O.Nonempty ∧
      ∀ y ∈ O,
        affineTangentSpace (geometricClosure (polynomialMap Q '' Y)) (polynomialMap Q y) =
          LinearMap.range ((polynomialMapDifferential Q y).domRestrict
            (affineTangentSpace Y y)) ∧
        polynomialMap P y ∈ coordinatePairing.orthogonal
          (affineTangentSpace (geometricClosure (polynomialMap Q '' Y)) (polynomialMap Q y)) ∧
        ∀ z ∈ coordinatePairing.orthogonal
          (affineTangentSpace (geometricClosure (polynomialMap Q '' Y)) (polynomialMap Q y)),
          dotProduct z (gradient F (polynomialMap P y)) = 0 := by
  obtain ⟨G⟩ := (ReducedGenericImageTangent.genericImageTangentInput
    Unconditional.genericRankOpen).choose Y hY hiY Q W hW hdW
  refine ⟨G.openSet, G.isOpen, G.subset, G.dense, G.nonempty, ?_⟩
  intro y hy
  obtain ⟨α, hα, hg⟩ := hcontact y (G.subset hy)
  have hyY : y ∈ Y := by
    rw [← G.dense]
    exact subset_geometricClosure _ hy
  have hradial : polynomialMap Q y ∈
      affineTangentSpace (geometricClosure (polynomialMap Q '' Y)) (polynomialMap Q y) :=
    hcone.radial_tangent _ (subset_geometricClosure _ ⟨y, hyY, rfl⟩)
  exact ⟨G.image_tangent y hy,
    contact_restriction_singular F P Q Y hF hpair y α hα hg _
      (G.image_tangent y hy).le hradial⟩

/-- Literal incidence and nonzero pointwise gradients supply the nonzero
proportionality factors, so the preceding result can be applied without
any chosen factors as input. -/
theorem exists_dense_open_contact_annihilator_of_incidence {m n : ℕ}
    (F : GeometricPolynomial n) (P Q : Fin n → GeometricPolynomial m)
    (Y : Set (GeometricPoint m)) (hY : AlgebraicallyClosedSet Y)
    (hiY : GeometricallyIrreducible Y)
    (hinc : ∀ y ∈ Y,
      (polynomialMap P y, polynomialMap Q y) ∈ affineSectionSingularIncidence F)
    (W : Set (GeometricPoint m)) (hW : RelativelyOpenSet Y W)
    (hdW : geometricClosure W = Y)
    (hnormal : ∀ y ∈ W, polynomialMap Q y ≠ 0)
    (hgradient : ∀ y ∈ W, gradient F (polynomialMap P y) ≠ 0)
    (hcone : IsAffineCone (geometricClosure (polynomialMap Q '' Y))) :
    ∃ O : Set (GeometricPoint m), RelativelyOpenSet Y O ∧ O ⊆ W ∧
      geometricClosure O = Y ∧ O.Nonempty ∧
      ∀ y ∈ O,
        affineTangentSpace (geometricClosure (polynomialMap Q '' Y)) (polynomialMap Q y) =
          LinearMap.range ((polynomialMapDifferential Q y).domRestrict
            (affineTangentSpace Y y)) ∧
        polynomialMap P y ∈ coordinatePairing.orthogonal
          (affineTangentSpace (geometricClosure (polynomialMap Q '' Y)) (polynomialMap Q y)) ∧
        ∀ z ∈ coordinatePairing.orthogonal
          (affineTangentSpace (geometricClosure (polynomialMap Q '' Y)) (polynomialMap Q y)),
          dotProduct z (gradient F (polynomialMap P y)) = 0 := by
  apply exists_dense_open_contact_annihilator F P Q Y hY hiY
    (fun y hy => (hinc y hy).1) (fun y hy => (hinc y hy).2.1) W hW hdW _ hcone
  intro y hy
  have hyY : y ∈ Y := by
    rw [← hdW]
    exact subset_geometricClosure _ hy
  have hspan := (minors_iff_mem_span (polynomialMap Q y)
    (gradient F (polynomialMap P y)) (hnormal y hy)).mp (hinc y hyY).2.2
  obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.mp hspan
  refine ⟨α, ?_, hα.symm⟩
  intro hz
  exact hgradient y hy (by simpa [hz] using hα.symm)

/-- On the same type of actual dense open, every frame spanning the
annihilator of the base tangent identifies the contact point with a
singular point of the actual restricted polynomial, retaining F=0.
The frame may vary with the point, and no rationality is asserted. -/
theorem exists_dense_open_restricted_singular_images {m n : ℕ}
    (F : GeometricPolynomial n) (P Q : Fin n → GeometricPolynomial m)
    (Y : Set (GeometricPoint m)) (hY : AlgebraicallyClosedSet Y)
    (hiY : GeometricallyIrreducible Y)
    (hinc : ∀ y ∈ Y,
      (polynomialMap P y, polynomialMap Q y) ∈ affineSectionSingularIncidence F)
    (W : Set (GeometricPoint m)) (hW : RelativelyOpenSet Y W)
    (hdW : geometricClosure W = Y)
    (hnormal : ∀ y ∈ W, polynomialMap Q y ≠ 0)
    (hgradient : ∀ y ∈ W, gradient F (polynomialMap P y) ≠ 0)
    (hcone : IsAffineCone (geometricClosure (polynomialMap Q '' Y))) :
    ∃ O : Set (GeometricPoint m), RelativelyOpenSet Y O ∧ O ⊆ W ∧
      geometricClosure O = Y ∧ O.Nonempty ∧
      ∀ y ∈ O, ∀ (d : ℕ) (B : Matrix (Fin n) (Fin d) GeometricField),
        LinearMap.range B.mulVecLin = coordinatePairing.orthogonal
          (affineTangentSpace (geometricClosure (polynomialMap Q '' Y)) (polynomialMap Q y)) →
        polynomialMap P y ∈ B.mulVec '' hypersurfaceSingularLocus (restrict B F) := by
  obtain ⟨O, ho, hsub, hd, hne, hc⟩ :=
    exists_dense_open_contact_annihilator_of_incidence F P Q Y hY hiY hinc
      W hW hdW hnormal hgradient hcone
  refine ⟨O, ho, hsub, hd, hne, ?_⟩
  intro y hy d B hB
  have hyY : y ∈ Y := by
    rw [← hd]
    exact subset_geometricClosure _ hy
  obtain ⟨_, hp, hg⟩ := hc y hy
  rw [← hB] at hp
  obtain ⟨u, hu⟩ := hp
  change B.mulVec u = polynomialMap P y at hu
  refine ⟨u, ⟨?_, ?_⟩, hu⟩
  · change eval u (restrict B F) = 0
    rw [eval_restrict, hu]
    exact (hinc y hyY).1
  · apply (TerminalSectionIncidence.gradient_restrict_zero_iff B F u).mpr
    intro z
    rw [hu]
    apply hg
    rw [← hB]
    exact ⟨z, rfl⟩

end CubicTenVariables.TerminalGenericContact
