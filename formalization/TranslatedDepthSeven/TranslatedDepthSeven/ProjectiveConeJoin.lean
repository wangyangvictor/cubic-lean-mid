import TranslatedDepthSeven.HomogeneousCone
import TranslatedDepthSeven.HomogeneousIdealBridge
import TranslatedDepthSeven.RationalProjectiveLine

/-!
# A projective cone as an explicit join

Let `Z` be the projective common zero locus of a finite family of positive-
degree homogeneous integral equations.  Adjoin one unused homogeneous
coordinate.  This file proves, on actual Mathlib projective points, that the
resulting projective common zero locus is exactly the union of the coordinate
vertex and the projective lines joining that vertex to `Z` in the hyperplane
at infinity.

This is the static set-theoretic identity used in the translated model.  No
claim about projective closure, components, degree, dimension, or schemes is
made here.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped LinearAlgebra.Projectivization

open Finset MvPolynomial

variable {σ : Type*}

/-- The vector `(1,0)` defining the coordinate vertex after one homogeneous
coordinate has been adjoined. -/
def projectiveConeVertexVector : Option σ → ℚ
  | none => 1
  | some _ => 0

theorem projectiveConeVertexVector_ne_zero :
    (projectiveConeVertexVector : Option σ → ℚ) ≠ 0 := by
  intro h
  have hnone := congrFun h none
  norm_num [projectiveConeVertexVector] at hnone

/-- The coordinate vertex in the enlarged projective space. -/
def projectiveConeVertexPoint : ℙ ℚ (Option σ → ℚ) :=
  Projectivization.mk ℚ projectiveConeVertexVector
    projectiveConeVertexVector_ne_zero

/-- Embed a vector in the hyperplane at infinity of the enlarged vector
space. -/
def projectiveInfinityVector (z : σ → ℚ) : Option σ → ℚ
  | none => 0
  | some i => z i

theorem projectiveInfinityVector_ne_zero {z : σ → ℚ} (hz : z ≠ 0) :
    projectiveInfinityVector z ≠ 0 := by
  intro h
  apply hz
  funext i
  have hi := congrFun h (some i)
  simpa [projectiveInfinityVector] using hi

/-- The literal union of the coordinate vertex and all actual projective
lines joining it to points of `Z` embedded at infinity. -/
def projectiveJoinWithCoordinateVertex
    (Z : Set (ℙ ℚ (σ → ℚ))) : Set (ℙ ℚ (Option σ → ℚ)) :=
  {P | P = projectiveConeVertexPoint ∨
    ∃ (z : σ → ℚ) (hz : z ≠ 0),
      Projectivization.mk ℚ z hz ∈ Z ∧
      P ∈ rationalProjectiveLine projectiveConeVertexVector
        (projectiveInfinityVector z)}

/-- The projective set obtained by imposing the original equations only on
the non-homogenizing coordinates of a displayed nonzero representative. -/
def projectiveConeOverIntegralEquations
    (equations : Finset (MvPolynomial σ ℤ)) :
    Set (ℙ ℚ (Option σ → ℚ)) :=
  {P | ∃ (v : Option σ → ℚ) (hv : v ≠ 0),
    P = Projectivization.mk ℚ v hv ∧
      (fun i => v (some i)) ∈
        integralAffineConeZeroSetOver ℚ equations}

/-- Extend integral coefficients to `ℚ` and place every original variable in
the non-homogenizing coordinates.  The new coordinate does not occur. -/
def projectiveConeLiftEquation (f : MvPolynomial σ ℤ) :
    MvPolynomial (Option σ) ℚ :=
  MvPolynomial.rename some (MvPolynomial.map (Int.castRingHom ℚ) f)

/-- The literal finite family of lifted equations. -/
def projectiveConeLiftEquationFamily
    (equations : Finset (MvPolynomial σ ℤ)) :
    Finset (MvPolynomial (Option σ) ℚ) := by
  classical
  exact equations.image projectiveConeLiftEquation

theorem projectiveConeLiftEquation_isHomogeneous
    (f : MvPolynomial σ ℤ) (d : ℕ) (hf : f.IsHomogeneous d) :
    (projectiveConeLiftEquation f).IsHomogeneous d :=
  (hf.map _).rename_isHomogeneous

theorem projectiveConeLiftEquationFamily_each_isHomogeneous
    (equations : Finset (MvPolynomial σ ℤ))
    (degree : MvPolynomial σ ℤ → ℕ)
    (hhom : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    {g : MvPolynomial (Option σ) ℚ}
    (hg : g ∈ projectiveConeLiftEquationFamily equations) :
    ∃ f ∈ equations,
      g = projectiveConeLiftEquation f ∧ g.IsHomogeneous (degree f) := by
  classical
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
  exact ⟨f, hf, rfl,
    projectiveConeLiftEquation_isHomogeneous f (degree f) (hhom f hf)⟩

/-- Positive-degree homogeneous equations vanish at the zero vector after
extension of coefficients to `ℚ`. -/
theorem zero_mem_integralAffineConeZeroSetOver_of_positiveDegree
    (equations : Finset (MvPolynomial σ ℤ))
    (degree : MvPolynomial σ ℤ → ℕ)
    (hhom : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    (hpositive : ∀ f ∈ equations, 0 < degree f) :
    (0 : σ → ℚ) ∈ integralAffineConeZeroSetOver ℚ equations := by
  intro f hf
  let fℚ := MvPolynomial.map (Int.castRingHom ℚ) f
  have hfℚ : fℚ.IsHomogeneous (degree f) := (hhom f hf).map _
  have hscale := eval_smul_of_isHomogeneous
    fℚ (0 : σ → ℚ) 0 (degree f) hfℚ
  have hdne : degree f ≠ 0 := Nat.ne_of_gt (hpositive f hf)
  simpa [fℚ, hdne] using hscale

/-- A displayed representative belongs to the enlarged projective cone
exactly when its non-homogenizing coordinate vector satisfies the original
equations. -/
theorem mk_mem_projectiveConeOverIntegralEquations_iff
    (equations : Finset (MvPolynomial σ ℤ))
    (degree : MvPolynomial σ ℤ → ℕ)
    (hhom : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    (v : Option σ → ℚ) (hv : v ≠ 0) :
    Projectivization.mk ℚ v hv ∈
        projectiveConeOverIntegralEquations equations ↔
      (fun i => v (some i)) ∈
        integralAffineConeZeroSetOver ℚ equations := by
  constructor
  · rintro ⟨w, hw, hvw, hwzero⟩
    obtain ⟨a, ha⟩ :=
      (Projectivization.mk_eq_mk_iff' ℚ v w hv hw).mp hvw
    have hscaled :=
      smul_mem_integralAffineConeZeroSetOver equations degree hhom hwzero a
    have hcoordinates :
        (fun i => a * w (some i)) = (fun i => v (some i)) := by
      funext i
      simpa only [Pi.smul_apply, smul_eq_mul] using congrFun ha (some i)
    simpa only [hcoordinates] using hscaled
  · intro hvzero
    exact ⟨v, hv, rfl, hvzero⟩

/-- The representative-based cone is exactly the common projective zero
locus of the literal lifted equation family. -/
theorem finiteProjectiveCommonZeroLocus_projectiveConeLiftEquationFamily
    (equations : Finset (MvPolynomial σ ℤ))
    (degree : MvPolynomial σ ℤ → ℕ)
    (hhom : ∀ f ∈ equations, f.IsHomogeneous (degree f)) :
    finiteProjectiveCommonZeroLocus
        (projectiveConeLiftEquationFamily equations) =
      projectiveConeOverIntegralEquations equations := by
  classical
  ext P
  induction P using Projectivization.ind with
  | h v hv =>
      rw [mk_mem_projectiveConeOverIntegralEquations_iff
        equations degree hhom]
      constructor
      · intro hP f hf
        have hmem : projectiveConeLiftEquation f ∈
            projectiveConeLiftEquationFamily equations :=
          Finset.mem_image.mpr ⟨f, hf, rfl⟩
        have hzero := hP _ hmem
        rw [mk_mem_homogeneousProjectiveHypersurface_iff
          (projectiveConeLiftEquation f) (degree f)
          (projectiveConeLiftEquation_isHomogeneous
            f (degree f) (hhom f hf)) v hv] at hzero
        simpa [projectiveConeLiftEquation, MvPolynomial.eval_rename,
          MvPolynomial.eval_map, Function.comp_def] using hzero
      · intro hvzero g hg
        obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
        rw [mk_mem_homogeneousProjectiveHypersurface_iff
          (projectiveConeLiftEquation f) (degree f)
          (projectiveConeLiftEquation_isHomogeneous
            f (degree f) (hhom f hf)) v hv]
        simpa [projectiveConeLiftEquation, MvPolynomial.eval_rename,
          MvPolynomial.eval_map, Function.comp_def] using
          hvzero f hf

/-- The exact join identity for the projective cone over a positive-degree
homogeneous equation family. -/
theorem projectiveConeOverIntegralEquations_eq_join
    (equations : Finset (MvPolynomial σ ℤ))
    (degree : MvPolynomial σ ℤ → ℕ)
    (hhom : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    (hpositive : ∀ f ∈ equations, 0 < degree f) :
    projectiveConeOverIntegralEquations equations =
      projectiveJoinWithCoordinateVertex
        (integralProjectiveConeZeroSetOver ℚ equations) := by
  ext P
  constructor
  · intro hP
    induction P using Projectivization.ind with
    | h v hv =>
        have hvcone : (fun i => v (some i)) ∈
            integralAffineConeZeroSetOver ℚ equations :=
          (mk_mem_projectiveConeOverIntegralEquations_iff
            equations degree hhom v hv).mp hP
        let z : σ → ℚ := fun i => v (some i)
        by_cases hz : z = 0
        · left
          apply (Projectivization.mk_eq_mk_iff' ℚ v
            projectiveConeVertexVector hv
            projectiveConeVertexVector_ne_zero).mpr
          refine ⟨v none, ?_⟩
          funext j
          cases j with
          | none => simp [projectiveConeVertexVector]
          | some i =>
              have hi := congrFun hz i
              simpa [z, projectiveConeVertexVector] using hi.symm
        · right
          refine ⟨z, hz, ?_, ?_⟩
          · exact (mk_mem_integralProjectiveConeZeroSetOver_iff
              equations degree hhom z hz).mpr hvcone
          · exact (mk_mem_rationalProjectiveLine_iff
              projectiveConeVertexVector (projectiveInfinityVector z) v hv).mpr
              ⟨v none, 1, by
                funext j
                cases j with
                | none => simp [projectiveConeVertexVector,
                    projectiveInfinityVector]
                | some i => simp [z, projectiveConeVertexVector,
                    projectiveInfinityVector]⟩
  · intro hP
    rcases hP with hvertex | ⟨z, hz, hzZ, hline⟩
    · rw [hvertex]
      unfold projectiveConeVertexPoint
      rw [mk_mem_projectiveConeOverIntegralEquations_iff
        equations degree hhom]
      simpa [projectiveConeVertexVector] using
        (zero_mem_integralAffineConeZeroSetOver_of_positiveDegree
          equations degree hhom hpositive)
    · induction P using Projectivization.ind with
      | h v hv =>
          obtain ⟨a, b, hab⟩ :=
            (mk_mem_rationalProjectiveLine_iff
              projectiveConeVertexVector (projectiveInfinityVector z) v hv).mp
              hline
          rw [mk_mem_projectiveConeOverIntegralEquations_iff
            equations degree hhom]
          have hzcone : z ∈ integralAffineConeZeroSetOver ℚ equations :=
            (mk_mem_integralProjectiveConeZeroSetOver_iff
              equations degree hhom z hz).mp hzZ
          have hbcone :=
            smul_mem_integralAffineConeZeroSetOver equations degree hhom hzcone b
          have hcoordinates :
              (fun i => v (some i)) = (fun i => b * z i) := by
            funext i
            have hi := congrFun hab (some i)
            simpa [projectiveConeVertexVector, projectiveInfinityVector] using
              hi.symm
          simpa only [hcoordinates] using hbcone

end

end TranslatedDepthSeven
