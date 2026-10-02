import TranslatedDepthSeven.ProjectiveConeJoin

/-!
# A translated projective cone as an explicit join

Fix `y₀ : σ → ℚ` and `m ≠ 0`.  The homogeneous linear automorphism

`(s,y) ↦ (s, s y₀ + m y)`

sends the vector `(m,-y₀)` to `(m,0)`, and fixes the hyperplane at infinity
pointwise on projective space.  This file proves the resulting literal
set-theoretic identity: the common projective zero locus of the homogeneous
affine pullbacks of the lifted equations is exactly the union of the source
vertex `[(m,-y₀)]` and the projective lines joining it to the original
projective zero locus at infinity.

No assertion about closure, components, dimension, degree, or schemes is
made here.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped LinearAlgebra.Projectivization

open Finset MvPolynomial

variable {σ : Type*}

/-- The source vertex vector `(m,-y₀)` for the homogeneous affine map
`(s,y) ↦ (s,s y₀+m y)`. -/
def translatedProjectiveConeVertexVector
    (y₀ : σ → ℚ) (m : ℚ) : Option σ → ℚ
  | none => m
  | some i => -y₀ i

theorem translatedProjectiveConeVertexVector_ne_zero
    (y₀ : σ → ℚ) (m : ℚ) (hm : m ≠ 0) :
    translatedProjectiveConeVertexVector y₀ m ≠ 0 := by
  intro h
  apply hm
  have hnone := congrFun h none
  simpa [translatedProjectiveConeVertexVector] using hnone

/-- The actual rational projective point represented by `(m,-y₀)`. -/
def translatedProjectiveConeVertexPoint
    (y₀ : σ → ℚ) (m : ℚ) (hm : m ≠ 0) :
    ℙ ℚ (Option σ → ℚ) :=
  Projectivization.mk ℚ (translatedProjectiveConeVertexVector y₀ m)
    (translatedProjectiveConeVertexVector_ne_zero y₀ m hm)

/-- On vectors, the homogeneous affine map sends `(m,-y₀)` exactly to
`m(1,0)`. -/
theorem homogeneousAffineLinearEquiv_translatedProjectiveConeVertexVector
    (y₀ : σ → ℚ) (m : ℚ) (hm : m ≠ 0) :
    homogeneousAffineLinearEquiv y₀ m hm
        (translatedProjectiveConeVertexVector y₀ m) =
      m • (projectiveConeVertexVector : Option σ → ℚ) := by
  funext j
  cases j with
  | none => simp [translatedProjectiveConeVertexVector,
      projectiveConeVertexVector]
  | some i =>
      simp [translatedProjectiveConeVertexVector,
        projectiveConeVertexVector]
      ring

/-- On vectors with homogenizing coordinate zero, the homogeneous affine
map is exactly scalar multiplication by `m`. -/
theorem homogeneousAffineLinearEquiv_projectiveInfinityVector
    (y₀ : σ → ℚ) (m : ℚ) (hm : m ≠ 0) (z : σ → ℚ) :
    homogeneousAffineLinearEquiv y₀ m hm (projectiveInfinityVector z) =
      m • projectiveInfinityVector z := by
  funext j
  cases j with
  | none => simp [projectiveInfinityVector]
  | some i => simp [projectiveInfinityVector]

/-- Projectively, the source vertex is carried exactly to the coordinate
vertex. -/
theorem projectiveAffineMap_translatedProjectiveConeVertexPoint
    (y₀ : σ → ℚ) (m : ℚ) (hm : m ≠ 0) :
    projectiveAffineMap y₀ m hm
        (translatedProjectiveConeVertexPoint y₀ m hm) =
      (projectiveConeVertexPoint : ℙ ℚ (Option σ → ℚ)) := by
  unfold translatedProjectiveConeVertexPoint projectiveConeVertexPoint
  rw [projectiveAffineMap_mk]
  apply (Projectivization.mk_eq_mk_iff' ℚ _ _ _ _).mpr
  refine ⟨m, ?_⟩
  exact
    (homogeneousAffineLinearEquiv_translatedProjectiveConeVertexVector
      y₀ m hm).symm

/-- Exact transport of every projective line through the source vertex and
a displayed point at infinity. -/
theorem projectiveAffineMap_mem_rationalProjectiveLine_iff
    (y₀ : σ → ℚ) (m : ℚ) (hm : m ≠ 0)
    (z : σ → ℚ) (P : ℙ ℚ (Option σ → ℚ)) :
    projectiveAffineMap y₀ m hm P ∈
        rationalProjectiveLine projectiveConeVertexVector
          (projectiveInfinityVector z) ↔
      P ∈ rationalProjectiveLine
        (translatedProjectiveConeVertexVector y₀ m)
        (projectiveInfinityVector z) := by
  induction P using Projectivization.ind with
  | h v hv =>
      rw [projectiveAffineMap_mk]
      rw [mk_mem_rationalProjectiveLine_iff,
        mk_mem_rationalProjectiveLine_iff]
      constructor
      · rintro ⟨a, b, hab⟩
        refine ⟨a / m, b / m, ?_⟩
        apply (homogeneousAffineLinearEquiv y₀ m hm).injective
        rw [map_add, map_smul, map_smul]
        rw [homogeneousAffineLinearEquiv_translatedProjectiveConeVertexVector,
          homogeneousAffineLinearEquiv_projectiveInfinityVector]
        simpa [smul_smul, hm] using hab
      · rintro ⟨a, b, hab⟩
        refine ⟨a * m, b * m, ?_⟩
        rw [← hab, map_add, map_smul, map_smul]
        rw [homogeneousAffineLinearEquiv_translatedProjectiveConeVertexVector,
          homogeneousAffineLinearEquiv_projectiveInfinityVector]
        simp [smul_smul, mul_comm]

/-- The preceding pointwise statement as an exact equality of sets: the
projective affine automorphism carries the entire source line onto the
corresponding coordinate-vertex line. -/
theorem projectiveAffineMap_image_rationalProjectiveLine
    (y₀ : σ → ℚ) (m : ℚ) (hm : m ≠ 0) (z : σ → ℚ) :
    projectiveAffineMap y₀ m hm ''
        (rationalProjectiveLine
          (translatedProjectiveConeVertexVector y₀ m)
          (projectiveInfinityVector z) :
            Set (ℙ ℚ (Option σ → ℚ))) =
      (rationalProjectiveLine projectiveConeVertexVector
        (projectiveInfinityVector z) : Set (ℙ ℚ (Option σ → ℚ))) := by
  ext Q
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact (projectiveAffineMap_mem_rationalProjectiveLine_iff
      y₀ m hm z P).mpr hP
  · intro hQ
    obtain ⟨P, rfl⟩ := (projectiveAffineMap_bijective y₀ m hm).2 Q
    exact ⟨P,
      (projectiveAffineMap_mem_rationalProjectiveLine_iff
        y₀ m hm z P).mp hQ, rfl⟩

/-- The literal union of `[(m,-y₀)]` and all projective lines joining it to
points of `Z` embedded in the hyperplane at infinity. -/
def projectiveJoinWithTranslatedVertex
    (y₀ : σ → ℚ) (m : ℚ) (hm : m ≠ 0)
    (Z : Set (ℙ ℚ (σ → ℚ))) : Set (ℙ ℚ (Option σ → ℚ)) :=
  {P | P = translatedProjectiveConeVertexPoint y₀ m hm ∨
    ∃ (z : σ → ℚ) (hz : z ≠ 0),
      Projectivization.mk ℚ z hz ∈ Z ∧
      P ∈ rationalProjectiveLine
        (translatedProjectiveConeVertexVector y₀ m)
        (projectiveInfinityVector z)}

/-- Exact transport of the literal translated join to the coordinate-
vertex join. -/
theorem projectiveAffineMap_mem_projectiveJoinWithCoordinateVertex_iff
    (y₀ : σ → ℚ) (m : ℚ) (hm : m ≠ 0)
    (Z : Set (ℙ ℚ (σ → ℚ))) (P : ℙ ℚ (Option σ → ℚ)) :
    projectiveAffineMap y₀ m hm P ∈
        projectiveJoinWithCoordinateVertex Z ↔
      P ∈ projectiveJoinWithTranslatedVertex y₀ m hm Z := by
  constructor
  · rintro (hvertex | ⟨z, hz, hzZ, hline⟩)
    · left
      apply projectiveAffineMap_injective y₀ m hm
      exact hvertex.trans
        (projectiveAffineMap_translatedProjectiveConeVertexPoint
          y₀ m hm).symm
    · exact Or.inr ⟨z, hz, hzZ,
        (projectiveAffineMap_mem_rationalProjectiveLine_iff
          y₀ m hm z P).mp hline⟩
  · rintro (hvertex | ⟨z, hz, hzZ, hline⟩)
    · left
      rw [hvertex]
      exact projectiveAffineMap_translatedProjectiveConeVertexPoint y₀ m hm
    · exact Or.inr ⟨z, hz, hzZ,
        (projectiveAffineMap_mem_rationalProjectiveLine_iff
          y₀ m hm z P).mpr hline⟩

/-- The finite family obtained by applying the literal homogeneous affine
pullback `(s,y) ↦ (s,s y₀+m y)` to every lifted original equation. -/
def translatedProjectiveConeLiftEquationFamily
    (y₀ : σ → ℚ) (m : ℚ) (hm : m ≠ 0)
    (equations : Finset (MvPolynomial σ ℤ)) :
    Finset (MvPolynomial (Option σ) ℚ) :=
  finiteFamilyHomogeneousAffineChange y₀ m hm
    (projectiveConeLiftEquationFamily equations)

/-- The common projective zero locus of the homogeneous affine pullbacks is
exactly the explicit join with source vertex `[(m,-y₀)]`. -/
theorem finiteProjectiveCommonZeroLocus_translatedProjectiveConeLiftEquationFamily
    (equations : Finset (MvPolynomial σ ℤ))
    (degree : MvPolynomial σ ℤ → ℕ)
    (hhom : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    (hpositive : ∀ f ∈ equations, 0 < degree f)
    (y₀ : σ → ℚ) (m : ℚ) (hm : m ≠ 0) :
    finiteProjectiveCommonZeroLocus
        (translatedProjectiveConeLiftEquationFamily y₀ m hm equations) =
      projectiveJoinWithTranslatedVertex y₀ m hm
        (integralProjectiveConeZeroSetOver ℚ equations) := by
  have hliftHomogeneous :
      ∀ g ∈ projectiveConeLiftEquationFamily equations,
        ∃ d : ℕ, g.IsHomogeneous d := by
    intro g hg
    obtain ⟨f, hf, _hgf, hgHomogeneous⟩ :=
      projectiveConeLiftEquationFamily_each_isHomogeneous
        equations degree hhom hg
    exact ⟨degree f, hgHomogeneous⟩
  ext P
  calc
    P ∈ finiteProjectiveCommonZeroLocus
          (translatedProjectiveConeLiftEquationFamily y₀ m hm equations) ↔
        projectiveAffineMap y₀ m hm P ∈
          finiteProjectiveCommonZeroLocus
            (projectiveConeLiftEquationFamily equations) := by
      exact (projectiveAffineMap_mem_finiteProjectiveCommonZeroLocus_iff
        y₀ m hm (projectiveConeLiftEquationFamily equations)
        hliftHomogeneous P).symm
    _ ↔ projectiveAffineMap y₀ m hm P ∈
          projectiveConeOverIntegralEquations equations := by
      rw [finiteProjectiveCommonZeroLocus_projectiveConeLiftEquationFamily
        equations degree hhom]
    _ ↔ projectiveAffineMap y₀ m hm P ∈
          projectiveJoinWithCoordinateVertex
            (integralProjectiveConeZeroSetOver ℚ equations) := by
      rw [projectiveConeOverIntegralEquations_eq_join
        equations degree hhom hpositive]
    _ ↔ P ∈ projectiveJoinWithTranslatedVertex y₀ m hm
          (integralProjectiveConeZeroSetOver ℚ equations) :=
      projectiveAffineMap_mem_projectiveJoinWithCoordinateVertex_iff
        y₀ m hm (integralProjectiveConeZeroSetOver ℚ equations) P

end

end TranslatedDepthSeven
