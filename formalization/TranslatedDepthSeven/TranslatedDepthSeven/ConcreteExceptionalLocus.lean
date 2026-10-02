import TranslatedDepthSeven.ConcreteIntegralCount
import TranslatedDepthSeven.FiniteEquationMinimalComponents
import TranslatedDepthSeven.HomogeneousMinimalComponents
import TranslatedDepthSeven.ProjectiveLinearSection
import TranslatedDepthSeven.PublishedCountingTheorems
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The literal exceptional locus in the translated depth-seven statement

This file defines the exceptional locus directly from the fixed homogeneous
integral equations.  A rational linear section is a full-row-rank rational
matrix.  In accordance with the manuscript, its irreducible components are
the actual minimal prime ideals *after extension to an algebraic closure of
`ℚ`*.  Dimension and degree are read from the literal homogeneous Hilbert
function.  Thus two Galois-conjugate geometric components are never silently
merged into one rational component with the sum of their degrees.

No component selection, exceptional-set membership, or counting estimate is
an input to any definition below.
-/

namespace TranslatedDepthSeven

noncomputable section

set_option synthInstance.maxHeartbeats 200000

open scoped LinearAlgebra.Projectivization

open Matrix MvPolynomial

/-- Extend a literal finite family of integral equations to `ℚ`. -/
def rationalizedEquationFinset {n : ℕ}
    (equations : Finset (MvPolynomial (Fin n) ℤ)) :
    Finset (MvPolynomial (Fin n) ℚ) := by
  classical
  exact equations.image (MvPolynomial.map (Int.castRingHom ℚ))

/-- The literal equation family for the intersection with the rational
linear space cut out by the rows of `A`. -/
def rationalLinearSectionEquationFinset {c n : ℕ}
    (equations : Finset (MvPolynomial (Fin n) ℤ))
    (A : Matrix (Fin c) (Fin n) ℚ) :
    Finset (MvPolynomial (Fin n) ℚ) :=
  rationalizedEquationFinset equations ∪
    rationalMatrixRowLinearEquationFamily A

/-- The fixed algebraic closure in which geometric components are taken. -/
abbrev Qbar := AlgebraicClosure ℚ

/-- Extend the literal rational section equations to `Qbar`. -/
def geometricLinearSectionEquationFinset {c n : ℕ}
    (equations : Finset (MvPolynomial (Fin n) ℤ))
    (A : Matrix (Fin c) (Fin n) ℚ) :
    Finset (MvPolynomial (Fin n) Qbar) := by
  classical
  exact (rationalLinearSectionEquationFinset equations A).image
    (MvPolynomial.map (algebraMap ℚ Qbar))

/-- A rational projective point lies on the geometric component `P` after
coefficient extension to `Qbar`.  Homogeneity of `P`, proved from the
homogeneous input equations, makes this independent of the representative. -/
def ProjectivePointVanishesOnGeometricIdeal {n : ℕ}
    (P : Ideal (MvPolynomial (Fin n) Qbar))
    (x : Projectivization ℚ (Fin n → ℚ)) : Prop :=
  (fun i ↦ algebraMap ℚ Qbar (x.rep i)) ∈ affineIdealZeroLocus P

/-- The irrelevant coordinate ideal over the algebraic closure. -/
def geometricIrrelevantCoordinateIdeal (n : ℕ) :
    Ideal (MvPolynomial (Fin n) Qbar) :=
  Ideal.span
    (Set.range (MvPolynomial.X : Fin n → MvPolynomial (Fin n) Qbar))

/-- Literal projective dimension and degree from the eventual homogeneous
Hilbert function.  Here `Fin 13` is the coordinate set of `P^12`. -/
def HasGeometricProjectiveDimensionDegree
    (P : Ideal (MvPolynomial (Fin 13) Qbar)) (r d : ℕ) : Prop :=
  Published.HasProjectiveDimensionDegree (N := 12) P r d

/-- A literal projective component of the section defined by `A`: an actual
minimal prime of the displayed equation family which does not contain the
irrelevant ideal. -/
def IsProjectiveSectionComponent {c n : ℕ}
    (equations : Finset (MvPolynomial (Fin n) ℤ))
    (A : Matrix (Fin c) (Fin n) ℚ)
    (P : Ideal (MvPolynomial (Fin n) Qbar)) : Prop :=
  P ∈ finiteEquationMinimalPrimes
      (geometricLinearSectionEquationFinset equations A) ∧
    ¬ geometricIrrelevantCoordinateIdeal n ≤ P

/-- The component conditions occurring in the definition of
`Upsilon_H(Z)`.  The natural numbers here are the literal projective
dimensions read from the homogeneous Hilbert polynomial. -/
def IsDepthSevenExceptionalComponent {c : ℕ}
    (P : Ideal (MvPolynomial (Fin 13) Qbar)) : Prop :=
  (1 ≤ c ∧ c ≤ 3 ∧
      ((∃ r d : ℕ,
          HasGeometricProjectiveDimensionDegree P r d ∧ 5 - c < r) ∨
        (∃ d : ℕ,
          HasGeometricProjectiveDimensionDegree P (5 - c) d ∧ d ≤ 7))) ∨
    (c = 4 ∧
      ∃ r d : ℕ,
        HasGeometricProjectiveDimensionDegree P r d ∧ 1 < r)

/-- Literal membership in the finite-height union of exceptional section
components.  The matrix itself is quantified, with full row rank and the
primitive Plücker-height bound displayed. -/
def MemDepthSevenExceptionalLocus
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (heightBound : ℕ)
    (x : Projectivization ℚ (Fin 13 → ℚ)) : Prop :=
  ∃ c : ℕ, 1 ≤ c ∧ c ≤ 4 ∧
    ∃ A : Matrix (Fin c) (Fin 13) ℚ,
      A.rank = c ∧ rationalProjectiveLinearHeight A ≤ heightBound ∧
      ∃ P : Ideal (MvPolynomial (Fin 13) Qbar),
        IsProjectiveSectionComponent equations A P ∧
        IsDepthSevenExceptionalComponent (c := c) P ∧
        ProjectivePointVanishesOnGeometricIdeal P x

/-- A geometric section component whose projective dimension is larger than
the expected dimension `5 - c` is one of the literal depth-seven exceptional
components.  This is the dimension branch of the definition, stated without
any replacement of the component by a set-theoretic or rational surrogate. -/
theorem isDepthSevenExceptionalComponent_of_dimension_gt_expected
    {c r d : ℕ} {P : Ideal (MvPolynomial (Fin 13) Qbar)}
    (hc1 : 1 ≤ c) (hc3 : c ≤ 3)
    (hP : HasGeometricProjectiveDimensionDegree P r d)
    (hr : 5 - c < r) :
    IsDepthSevenExceptionalComponent (c := c) P := by
  left
  refine ⟨hc1, hc3, Or.inl ?_⟩
  exact ⟨r, d, hP, hr⟩

/-- A four-dimensional geometric component of a codimension-three rational
section is exceptional by the dimension branch.  In the low-degree fourfold
argument, the degree bound is used only to construct the rational `P^9`
section; this final exceptional-locus step uses the literal dimension data. -/
theorem isDepthSevenExceptionalComponent_of_codimThree_fourfold
    {P : Ideal (MvPolynomial (Fin 13) Qbar)} {d : ℕ}
    (hP : HasGeometricProjectiveDimensionDegree P 4 d) :
    IsDepthSevenExceptionalComponent (c := 3) P := by
  apply isDepthSevenExceptionalComponent_of_dimension_gt_expected
    (c := 3) (r := 4) (d := d)
  · omega
  · omega
  · exact hP
  · omega

/-- More generally, every codimension-three section component of projective
dimension at least four is exceptional.  This is the form used when the
low-degree fourfold is merely contained in an excess component of the
section, rather than being that component itself. -/
theorem isDepthSevenExceptionalComponent_of_codimThree_dimension_ge_four
    {P : Ideal (MvPolynomial (Fin 13) Qbar)} {r d : ℕ}
    (hP : HasGeometricProjectiveDimensionDegree P r d)
    (hr : 4 ≤ r) :
    IsDepthSevenExceptionalComponent (c := 3) P := by
  apply isDepthSevenExceptionalComponent_of_dimension_gt_expected
    (c := 3) (r := r) (d := d)
  · omega
  · omega
  · exact hP
  · omega

/-- A literal large-dimensional component of a bounded-height rational
linear section supplies a point of the depth-seven exceptional locus. -/
theorem memDepthSevenExceptionalLocus_of_dimension_gt_expected
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (heightBound : ℕ)
    {c r d : ℕ} (hc1 : 1 ≤ c) (hc4 : c ≤ 4)
    (A : Matrix (Fin c) (Fin 13) ℚ)
    (hA : A.rank = c)
    (hheight : rationalProjectiveLinearHeight A ≤ heightBound)
    (P : Ideal (MvPolynomial (Fin 13) Qbar))
    (hcomponent : IsProjectiveSectionComponent equations A P)
    (hP : HasGeometricProjectiveDimensionDegree P r d)
    (hc3 : c ≤ 3) (hr : 5 - c < r)
    (x : Projectivization ℚ (Fin 13 → ℚ))
    (hx : ProjectivePointVanishesOnGeometricIdeal P x) :
    MemDepthSevenExceptionalLocus equations heightBound x := by
  refine ⟨c, hc1, hc4, A, hA, hheight, P, hcomponent, ?_, hx⟩
  exact isDepthSevenExceptionalComponent_of_dimension_gt_expected
    hc1 hc3 hP hr

/-- The exact codimension-three conclusion needed after a low-degree
fourfold has been placed in a rational bounded-height `P^9`.  The input
`hcomponent` is the actual minimal prime of the displayed section equations,
and `hx` is literal membership of the chosen rational projective point in
that geometric component. -/
theorem memDepthSevenExceptionalLocus_of_codimThree_fourfold_component
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (heightBound : ℕ)
    (A : Matrix (Fin 3) (Fin 13) ℚ)
    (hA : A.rank = 3)
    (hheight : rationalProjectiveLinearHeight A ≤ heightBound)
    (P : Ideal (MvPolynomial (Fin 13) Qbar))
    (hcomponent : IsProjectiveSectionComponent equations A P)
    {d : ℕ} (hP : HasGeometricProjectiveDimensionDegree P 4 d)
    (x : Projectivization ℚ (Fin 13 → ℚ))
    (hx : ProjectivePointVanishesOnGeometricIdeal P x) :
    MemDepthSevenExceptionalLocus equations heightBound x := by
  apply memDepthSevenExceptionalLocus_of_dimension_gt_expected
    equations heightBound (c := 3) (r := 4) (d := d)
    (A := A) (P := P) (x := x)
  · omega
  · omega
  · exact hA
  · exact hheight
  · exact hcomponent
  · exact hP
  · omega
  · omega
  · exact hx

/-- The bounded-height codimension-three conclusion in the excess-component
case.  A low-degree fourfold contained in the component supplies the lower
bound `4 ≤ r` by the missing geometric dimension-monotonicity bridge. -/
theorem memDepthSevenExceptionalLocus_of_codimThree_component_of_dimension_ge_four
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (heightBound : ℕ)
    (A : Matrix (Fin 3) (Fin 13) ℚ)
    (hA : A.rank = 3)
    (hheight : rationalProjectiveLinearHeight A ≤ heightBound)
    (P : Ideal (MvPolynomial (Fin 13) Qbar))
    (hcomponent : IsProjectiveSectionComponent equations A P)
    {r d : ℕ} (hP : HasGeometricProjectiveDimensionDegree P r d)
    (hr : 4 ≤ r)
    (x : Projectivization ℚ (Fin 13 → ℚ))
    (hx : ProjectivePointVanishesOnGeometricIdeal P x) :
    MemDepthSevenExceptionalLocus equations heightBound x := by
  apply memDepthSevenExceptionalLocus_of_dimension_gt_expected
    equations heightBound (c := 3) (r := r) (d := d)
    (A := A) (P := P) (x := x)
  · omega
  · omega
  · exact hA
  · exact hheight
  · exact hcomponent
  · exact hP
  · omega
  · omega
  · exact hx

/-- The low-degree version of the preceding conclusion.  The degree bound
is deliberately retained in the theorem statement to match the source
branch, even though the exceptional-locus definition already excludes this
component through its excessive dimension. -/
theorem memDepthSevenExceptionalLocus_of_codimThree_fourfold_component_of_degree_le_three
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (heightBound : ℕ)
    (A : Matrix (Fin 3) (Fin 13) ℚ)
    (hA : A.rank = 3)
    (hheight : rationalProjectiveLinearHeight A ≤ heightBound)
    (P : Ideal (MvPolynomial (Fin 13) Qbar))
    (hcomponent : IsProjectiveSectionComponent equations A P)
    {d : ℕ} (hP : HasGeometricProjectiveDimensionDegree P 4 d)
    (_hdegree : d ≤ 3)
    (x : Projectivization ℚ (Fin 13 → ℚ))
    (hx : ProjectivePointVanishesOnGeometricIdeal P x) :
    MemDepthSevenExceptionalLocus equations heightBound x := by
  exact memDepthSevenExceptionalLocus_of_codimThree_fourfold_component
    equations heightBound A hA hheight P hcomponent hP x hx

/-- A concrete homogeneous equation family is linear when its generated
homogeneous ideal is literally the row-linear ideal of a full-rank rational
matrix.  Ideal equality, rather than equality of rational point sets, rules
out the possibility that a nonlinear scheme merely has the same `ℚ`-points
as a contained linear subspace. -/
def EquationFamilyDefinesLinearProjectiveSpace
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) : Prop :=
  ∃ c : ℕ, ∃ A : Matrix (Fin c) (Fin 13) ℚ,
    A.rank = c ∧
      finiteEquationIdeal (rationalizedEquationFinset equations) =
        finiteEquationIdeal (rationalMatrixRowLinearEquationFamily A)

/-- The exact projective class of a nonzero integral vector. -/
def integralProjectiveClass {n : ℕ} (x : IntVector n) (hx : x ≠ 0) :
    Projectivization ℚ (Fin n → ℚ) :=
  Projectivization.mk ℚ (fun i ↦ (x i : ℚ))
    (intCast_ne_zero (K := ℚ) hx)

/-- The literal counted finite set in the translated depth-seven theorem,
using the exceptional locus above rather than an arbitrary supplied family
of closed pieces. -/
def depthSevenTranslatedPointFinset
    (p : Parameters)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (CF : ℕ) : Finset (IntVector 13) := by
  classical
  exact (integerSupNormBox 13 ⌈p.B + p.L⌉₊).filter fun x ↦
    p.InTranslatedBox (fun i ↦ (x i : ℝ)) ∧
      p.InResidueClass x ∧
      IntegralCommonZero equations x ∧
      ∃ hx : x ≠ 0,
        ¬ EquationFamilyDefinesLinearProjectiveSpace equations ∧
        ¬ MemDepthSevenExceptionalLocus equations
          ⌈p.H ^ CF⌉₊ (integralProjectiveClass x hx)

/-- Exact membership formula for the literal target finite set. -/
theorem mem_depthSevenTranslatedPointFinset_iff
    (p : Parameters)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (CF : ℕ) (x : IntVector 13) :
    x ∈ depthSevenTranslatedPointFinset p equations CF ↔
      p.InTranslatedBox (fun i ↦ (x i : ℝ)) ∧
      p.InResidueClass x ∧
      IntegralCommonZero equations x ∧
      ∃ hx : x ≠ 0,
        ¬ EquationFamilyDefinesLinearProjectiveSpace equations ∧
        ¬ MemDepthSevenExceptionalLocus equations
          ⌈p.H ^ CF⌉₊ (integralProjectiveClass x hx) := by
  classical
  constructor
  · intro hx
    have h := (Finset.mem_filter.mp hx).2
    exact h
  · rintro ⟨hbox, hres, hzero, hx, hlinear, hexceptional⟩
    apply Finset.mem_filter.mpr
    refine ⟨mem_integerSupNormBox_of_mem_translatedBox p x hbox,
      hbox, hres, hzero, hx, hlinear, hexceptional⟩

end

end TranslatedDepthSeven
