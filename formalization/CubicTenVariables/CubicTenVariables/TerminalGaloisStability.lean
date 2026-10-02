import CubicTenVariables.TerminalBadNormals
import CubicTenVariables.GaussTerminalBound
import CubicTenVariables.GaloisAffineTransport

/-! Galois covariance of the actual terminal fibers, graph and bad normals.
All closures below are geometric closures of the actual geometric loci. -/

noncomputable section
namespace CubicTenVariables.TerminalGaloisStability
open MvPolynomial HessianTheorem11 Matrix BibleProjectiveGeometry
open RationalComponentDescent GaloisAffineTransport TerminalSectionIncidence
open AffineProductGeometry
open scoped BigOperators

variable {n : ℕ}

@[simp] theorem galoisPoint_zero (σ : GeometricField ≃ₐ[ℚ] GeometricField) :
    galoisPoint σ (0 : GeometricPoint n) = 0 := by
  ext i
  exact map_zero σ

@[simp] theorem galoisPoint_eq_zero_iff (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (x : GeometricPoint n) : galoisPoint σ x = 0 ↔ x = 0 := by
  simpa only [galoisPoint_zero] using
    (show galoisPoint σ x = galoisPoint σ (0 : GeometricPoint n) ↔ x = 0 from
      (pointEquiv σ).injective.eq_iff)

theorem galoisPoint_smul (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (a : GeometricField) (x : GeometricPoint n) :
    galoisPoint σ (a • x) = σ a • galoisPoint σ x := by
  ext i
  exact map_mul σ a (x i)

theorem galoisPoint_join (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (x v : GeometricPoint n) :
    galoisPoint σ (join x v) = join (galoisPoint σ x) (galoisPoint σ v) := by
  ext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;>
    simp only [galoisPoint, join, Fin.addCases_left, Fin.addCases_right]

theorem gradient_coefficientMap (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (F : GeometricPolynomial n) (x : GeometricPoint n) :
    gradient (map σ.toRingHom F) (galoisPoint σ x) = galoisPoint σ (gradient F x) := by
  ext i
  simpa only [gradient, pderiv_map] using eval_coefficientMap σ (pderiv i F) x

theorem dotProduct_galois (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (x v : GeometricPoint n) :
    dotProduct (galoisPoint σ v) (galoisPoint σ x) = σ (dotProduct v x) := by
  simp only [dotProduct, galoisPoint, map_sum, map_mul]

private theorem image_eq_of_mem_iff (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (A B : Set (GeometricPoint n))
    (h : ∀ x, galoisPoint σ x ∈ B ↔ x ∈ A) : galoisPoint σ '' A = B := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact (h y).2 hy
  · intro hx
    refine ⟨galoisPoint σ.symm x, (h _).1 ?_, galoisPoint_apply_symm σ x⟩
    simpa only [galoisPoint_apply_symm] using hx

/-- All three actual section-singularity equations commute with conjugation. -/
theorem sectionSingularFiber_mem_iff (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (F : GeometricPolynomial n) (v x : GeometricPoint n) :
    galoisPoint σ x ∈ sectionSingularFiber (map σ.toRingHom F) (galoisPoint σ v) ↔
      x ∈ sectionSingularFiber F v := by
  change (eval (galoisPoint σ x) (map σ.toRingHom F) = 0 ∧
    dotProduct (galoisPoint σ v) (galoisPoint σ x) = 0 ∧
    normalMinors (galoisPoint σ v) (gradient (map σ.toRingHom F) (galoisPoint σ x))) ↔ _
  rw [eval_coefficientMap, dotProduct_galois, gradient_coefficientMap]
  simp only [normalMinors, galoisPoint, ← map_mul, ← map_sub, map_eq_zero]
  rfl

theorem sectionSingularFiber_image (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (F : GeometricPolynomial n) (v : GeometricPoint n) :
    galoisPoint σ '' sectionSingularFiber F v =
      sectionSingularFiber (map σ.toRingHom F) (galoisPoint σ v) :=
  image_eq_of_mem_iff σ _ _ (sectionSingularFiber_mem_iff σ F v)

/-- Normalized projective charts commute with the semilinear point action. -/
theorem affineChart_image (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (Z : Set (GeometricPoint n)) (i : Fin n) :
    affineChart (galoisPoint σ '' Z) i = galoisPoint σ '' affineChart Z i := by
  ext y
  constructor
  · rintro ⟨⟨x,hx,rfl⟩,hi⟩
    refine ⟨x,⟨hx,?_⟩,rfl⟩
    exact σ.injective (hi.trans (map_one σ).symm)
  · rintro ⟨x,⟨hx,hi⟩,rfl⟩
    refine ⟨⟨x,hx,rfl⟩,?_⟩
    change σ (x i) = 1
    rw [hi, map_one]

/-- This is the actual chart-defined projective dimension, including empty sets. -/
theorem projectiveDimension_image (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (Z : Set (GeometricPoint n)) :
    projectiveDimension (galoisPoint σ '' Z) = projectiveDimension Z := by
  simp only [projectiveDimension, affineChart_image, affineDimension_image]

/-- The literal polynomially parametrized Gauss image is covariant. -/
theorem gaussParametrization_image (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (F : GeometricPolynomial n) :
    galoisPoint σ '' (polynomialMap (GaussGraph.parametrization F) '' GaussGraph.source F) =
      polynomialMap (GaussGraph.parametrization (map σ.toRingHom F)) ''
        GaussGraph.source (map σ.toRingHom F) := by
  rw [GaussGraph.image_eq_literal, GaussGraph.image_eq_literal]
  ext p
  constructor
  · rintro ⟨q,⟨x,hx,a,rfl⟩,rfl⟩
    refine ⟨galoisPoint σ x, ?_, σ a, ?_⟩
    · rw [eval_coefficientMap, hx, map_zero]
    · rw [galoisPoint_join, galoisPoint_smul, gradient_coefficientMap]
  · rintro ⟨x,hx,a,rfl⟩
    refine ⟨join (galoisPoint σ.symm x) (σ.symm a • gradient F (galoisPoint σ.symm x)),
      ⟨galoisPoint σ.symm x, ?_, σ.symm a, rfl⟩, ?_⟩
    · apply σ.injective
      rw [map_zero, ← eval_coefficientMap, galoisPoint_apply_symm]
      exact hx
    · rw [galoisPoint_join, galoisPoint_smul, ← gradient_coefficientMap,
        galoisPoint_apply_symm, σ.apply_symm_apply]

/-- The actual closed affine Gauss graph commutes with coefficient conjugation. -/
theorem gaussGraph_image (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (F : GeometricPolynomial n) :
    galoisPoint σ '' GaussGraph.graph F = GaussGraph.graph (map σ.toRingHom F) := by
  rw [GaussGraph.graph, ← geometricClosure_image, gaussParametrization_image]
  rfl

theorem gaussFiber_mem_iff (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (F : GeometricPolynomial n) (v x : GeometricPoint n) :
    galoisPoint σ x ∈ GaussTerminalBound.fiber (map σ.toRingHom F) (galoisPoint σ v) ↔
      x ∈ GaussTerminalBound.fiber F v := by
  change join (galoisPoint σ x) (galoisPoint σ v) ∈ GaussGraph.graph (map σ.toRingHom F) ↔ _
  rw [← galoisPoint_join, ← gaussGraph_image]
  exact (pointEquiv σ).injective.mem_set_image

theorem gaussFiber_image (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (F : GeometricPolynomial n) (v : GeometricPoint n) :
    galoisPoint σ '' GaussTerminalBound.fiber F v =
      GaussTerminalBound.fiber (map σ.toRingHom F) (galoisPoint σ v) :=
  image_eq_of_mem_iff σ _ _ (gaussFiber_mem_iff σ F v)

theorem sectionBadNormals_image (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (F : GeometricPolynomial n) (t : ℕ) :
    galoisPoint σ '' TerminalBadNormals.badNormals F t =
      TerminalBadNormals.badNormals (map σ.toRingHom F) t := by
  apply image_eq_of_mem_iff
  intro v
  change ((t+1 : ℕ) : Dimension) ≤ affineDimension (sectionSingularFiber (map σ.toRingHom F) (galoisPoint σ v)) ↔ _
  rw [← sectionSingularFiber_image, affineDimension_image]
  rfl

theorem gaussBadNormals_image (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (F : GeometricPolynomial n) (t : ℕ) :
    galoisPoint σ '' GaussTerminalBound.badNormals F t =
      GaussTerminalBound.badNormals (map σ.toRingHom F) t := by
  apply image_eq_of_mem_iff
  intro v
  change (t : Dimension) ≤ projectiveDimension (GaussTerminalBound.fiber (map σ.toRingHom F) (galoisPoint σ v)) ↔ _
  rw [← gaussFiber_image, projectiveDimension_image]
  rfl

@[simp] theorem coefficientMap_geometricPolynomial
    (σ : GeometricField ≃ₐ[ℚ] GeometricField) (F : RationalPolynomial n) :
    map σ.toRingHom (geometricPolynomial F) = geometricPolynomial F := by
  ext d
  simp only [geometricPolynomial, coeff_map]
  exact σ.commutes (coeff d F)

theorem sectionSingularFiber_rational (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (F : RationalPolynomial n) (v : GeometricPoint n) :
    galoisPoint σ '' sectionSingularFiber (geometricPolynomial F) v =
      sectionSingularFiber (geometricPolynomial F) (galoisPoint σ v) := by
  simpa only [coefficientMap_geometricPolynomial] using
    sectionSingularFiber_image σ (geometricPolynomial F) v

theorem gaussGraph_stable (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (F : RationalPolynomial n) :
    galoisPoint σ '' GaussGraph.graph (geometricPolynomial F) =
      GaussGraph.graph (geometricPolynomial F) := by
  simpa only [coefficientMap_geometricPolynomial] using gaussGraph_image σ (geometricPolynomial F)

theorem gaussFiber_rational (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (F : RationalPolynomial n) (v : GeometricPoint n) :
    galoisPoint σ '' GaussTerminalBound.fiber (geometricPolynomial F) v =
      GaussTerminalBound.fiber (geometricPolynomial F) (galoisPoint σ v) := by
  simpa only [coefficientMap_geometricPolynomial] using gaussFiber_image σ (geometricPolynomial F) v

theorem sectionBadNormals_stable (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (F : RationalPolynomial n) (t : ℕ) :
    galoisPoint σ '' TerminalBadNormals.badNormals (geometricPolynomial F) t =
      TerminalBadNormals.badNormals (geometricPolynomial F) t := by
  simpa only [coefficientMap_geometricPolynomial] using sectionBadNormals_image σ (geometricPolynomial F) t

theorem gaussBadNormals_stable (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (F : RationalPolynomial n) (t : ℕ) :
    galoisPoint σ '' GaussTerminalBound.badNormals (geometricPolynomial F) t =
      GaussTerminalBound.badNormals (geometricPolynomial F) t := by
  simpa only [coefficientMap_geometricPolynomial] using gaussBadNormals_image σ (geometricPolynomial F) t

theorem nonzero_image (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (Z : Set (GeometricPoint n)) :
    galoisPoint σ '' {v | v ∈ Z ∧ v ≠ 0} = {v | v ∈ galoisPoint σ '' Z ∧ v ≠ 0} := by
  ext y
  constructor
  · rintro ⟨x,⟨hx,hx0⟩,rfl⟩
    exact ⟨⟨x,hx,rfl⟩, fun h => hx0 ((galoisPoint_eq_zero_iff σ x).1 h)⟩
  · rintro ⟨⟨x,hx,rfl⟩,hx0⟩
    exact ⟨x,⟨hx,fun h => hx0 ((galoisPoint_eq_zero_iff σ x).2 h)⟩,rfl⟩

/-- Delete zero, take geometric closure, and adjoin zero: all three
operations commute with the actual semilinear point action. -/
theorem nonzeroClosure_image (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (Z : Set (GeometricPoint n)) :
    galoisPoint σ '' (geometricClosure {v | v ∈ Z ∧ v ≠ 0} ∪ {0}) =
      geometricClosure {v | v ∈ galoisPoint σ '' Z ∧ v ≠ 0} ∪ {0} := by
  rw [Set.image_union, ← geometricClosure_image, nonzero_image,
    Set.image_singleton, galoisPoint_zero]

theorem sectionBadCone_stable (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (F : RationalPolynomial n) (t : ℕ) :
    galoisPoint σ '' (geometricClosure {v : GeometricPoint n |
      ((t+1 : ℕ) : Dimension) ≤ affineDimension (sectionSingularFiber (geometricPolynomial F) v) ∧ v ≠ 0} ∪ {0}) =
      geometricClosure {v : GeometricPoint n |
        ((t+1 : ℕ) : Dimension) ≤ affineDimension (sectionSingularFiber (geometricPolynomial F) v) ∧ v ≠ 0} ∪ {0} := by
  have h := nonzeroClosure_image σ (TerminalBadNormals.badNormals (geometricPolynomial F) t)
  rw [sectionBadNormals_stable] at h
  exact h

theorem gaussBadCone_stable (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (F : RationalPolynomial n) (t : ℕ) :
    galoisPoint σ '' (geometricClosure {v : GeometricPoint n |
      (t : Dimension) ≤ projectiveDimension (GaussTerminalBound.fiber (geometricPolynomial F) v) ∧ v ≠ 0} ∪ {0}) =
      geometricClosure {v : GeometricPoint n |
        (t : Dimension) ≤ projectiveDimension (GaussTerminalBound.fiber (geometricPolynomial F) v) ∧ v ≠ 0} ∪ {0} := by
  have h := nonzeroClosure_image σ (GaussTerminalBound.badNormals (geometricPolynomial F) t)
  rw [gaussBadNormals_stable] at h
  exact h

end CubicTenVariables.TerminalGaloisStability
