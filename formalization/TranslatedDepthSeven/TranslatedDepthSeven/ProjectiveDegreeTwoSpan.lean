import TranslatedDepthSeven.ProjectiveDegreeOneSpan

/-!
# Projective degree at most two and the rational linear span

The only standard projective-geometric input used in this file is the
classical degree--span inequality

`dim Span(X) <= dim(X) + deg(X) - 1`.

Rather than packaging that result as a new opaque interface, every theorem
below accepts its literal ideal-theoretic consequence as a hypothesis.  In
the case needed by the depth-seven argument, a projective fourfold of degree
at most two in `P^12` has at least seven independent rational linear
equations; only two are used.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The degree--span inequality immediately supplies two rational linear
equations for a geometrically integral projective fourfold of degree at
most two in `P^12`.

The hypothesis `hDegreeSpan` is the exact algebraic translation of
`dim Span(X) <= dim(X) + deg(X) - 1`: in `P^N` the vector space of linear
forms in the geometrically prime homogeneous ideal has dimension at least
`N + 1 - r - d` for an integral projective variety of dimension `r` and
degree `d`. -/
theorem two_le_finrank_rationalLinearFormsInIdeal_of_degree_le_two
    (hDegreeSpan :
      ∀ (N r d : ℕ)
        (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
        I.IsPrime →
        (I.map (MvPolynomial.map
          (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime →
        I.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
        IsSaturatedByProjectiveIrrelevantIdeal I →
        HasProjectiveDimensionDegree I r d →
        N + 1 - r - d ≤
          Module.finrank ℚ (rationalLinearFormsInIdeal I))
    (I : Ideal (MvPolynomial (Fin 13) ℚ))
    (hIprime : I.IsPrime)
    (hIgeometric : (I.map (MvPolynomial.map
      (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime)
    (hIhomogeneous :
      I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ))
    (hIsaturated : IsSaturatedByProjectiveIrrelevantIdeal I)
    {d : ℕ} (hprojective : HasProjectiveDimensionDegree I 4 d)
    (hd : d ≤ 2) :
    2 ≤ Module.finrank ℚ (rationalLinearFormsInIdeal I) := by
  have hspan := hDegreeSpan 12 4 d I hIprime hIgeometric hIhomogeneous hIsaturated
    hprojective
  have htwo : 2 ≤ 12 + 1 - 4 - d := by omega
  exact htwo.trans hspan

/-- Uniform bounded-height codimension-two rational spaces containing a
fixed finite family of geometrically integral projective fourfolds of
degree at most two.  All choices are made before any box, modulus, or
residue class is introduced. -/
theorem exists_uniform_twoRow_linearSpan_of_finite_degreeAtMostTwo_fourfolds
    (hDegreeSpan :
      ∀ (N r d : ℕ)
        (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
        I.IsPrime →
        (I.map (MvPolynomial.map
          (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime →
        I.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
        IsSaturatedByProjectiveIrrelevantIdeal I →
        HasProjectiveDimensionDegree I r d →
        N + 1 - r - d ≤
          Module.finrank ℚ (rationalLinearFormsInIdeal I))
    {alpha : Type*} (components : Finset alpha)
    (ideal : alpha → Ideal (MvPolynomial (Fin 13) ℚ))
    (degree : alpha → ℕ)
    (hprime : ∀ Q ∈ components, (ideal Q).IsPrime)
    (hgeometric : ∀ Q ∈ components,
      ((ideal Q).map (MvPolynomial.map
        (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime)
    (hhomogeneous : ∀ Q ∈ components,
      (ideal Q).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ))
    (hsaturated : ∀ Q ∈ components,
      IsSaturatedByProjectiveIrrelevantIdeal (ideal Q))
    (hprojective : ∀ Q ∈ components,
      HasProjectiveDimensionDegree (ideal Q) 4 (degree Q))
    (hdegree : ∀ Q ∈ components, degree Q ≤ 2) :
    ∃ C : ℕ, ∀ Q ∈ components,
      ∃ v : Fin 2 → Fin 13 → ℚ,
        LinearIndependent ℚ v ∧
        (rationalLinearFormMatrix v).rank = 2 ∧
        (∀ i, rationalMatrixRowLinearPolynomial
          (rationalLinearFormMatrix v) i ∈ ideal Q) ∧
        rationalProjectiveLinearHeight
          (rationalLinearFormMatrix v) ≤ C := by
  apply exists_uniform_twoRow_linearSpan_of_finite components ideal
  intro Q hQ
  exact two_le_finrank_rationalLinearFormsInIdeal_of_degree_le_two
    hDegreeSpan (ideal Q) (hprime Q hQ) (hgeometric Q hQ) (hhomogeneous Q hQ)
      (hsaturated Q hQ) (hprojective Q hQ) (hdegree Q hQ)

end

end TranslatedDepthSeven
