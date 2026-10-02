import TranslatedDepthSeven.JacobianExceptionalProjectiveSplit

/-!
# Literal degree split of the residual Jacobian-exceptional components

The projective-component reduction leaves only actual nonirrelevant minimal
primes with five normalization parameters.  This file partitions that
finite list using the literal Hilbert-function predicate already occurring
in the published counting statements.  It does not assume that the general
Hilbert-polynomial existence theorem has been formalized.

The three pieces are:

* a certified projective fourfold of degree at most seven;
* a certified projective fourfold not in the preceding piece (hence every
  displayed degree certificate has degree at least eight);
* a component for which no projective degree certificate has yet been
  constructed in Lean.

This is an exact finite partition, not a geometric interface.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

local instance jacobianExceptionalDegreeSplitClassicalDecidablePred
    {A : Type*} (q : A → Prop) : DecidablePred q := Classical.decPred q

/-- A residual component for which the literal eventual Hilbert polynomial
has been certified, with no a priori restriction on its degree. -/
def HasCertifiedProjectiveDegree
    {equations : Finset (MvPolynomial (Fin 13) ℚ)}
    (Q : JacobianExceptionalComponent equations) : Prop :=
  ∃ d : ℕ, HasProjectiveDimensionDegree Q.1 4 d

/-- The certified degree-at-most-seven residual components. -/
noncomputable def lowDegreeTopProjectiveJacobianExceptionalComponents
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d) :
    Finset (JacobianExceptionalComponent equations) :=
  (topProjectiveJacobianExceptionalComponents equations hhomogeneous).filter
    fun Q ↦ ∃ d : ℕ,
      HasProjectiveDimensionDegree Q.1 4 d ∧ d ≤ 7

/-- The certified residual components not belonging to the low-degree
piece.  The theorem below proves directly that every degree certificate on
such a component has degree at least eight. -/
noncomputable def highDegreeTopProjectiveJacobianExceptionalComponents
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d) :
    Finset (JacobianExceptionalComponent equations) :=
  (topProjectiveJacobianExceptionalComponents equations hhomogeneous).filter
    fun Q ↦
      Q ∉ lowDegreeTopProjectiveJacobianExceptionalComponents
        equations hhomogeneous ∧
      HasCertifiedProjectiveDegree Q

/-- The exact residual list on which the eventual Hilbert polynomial itself
has not yet been constructed. -/
noncomputable def uncertifiedTopProjectiveJacobianExceptionalComponents
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d) :
    Finset (JacobianExceptionalComponent equations) :=
  (topProjectiveJacobianExceptionalComponents equations hhomogeneous).filter
    fun Q ↦ ¬ HasCertifiedProjectiveDegree Q

theorem degree_ge_eight_of_mem_highDegreeTopProjectiveJacobianExceptionalComponents
    {equations : Finset (MvPolynomial (Fin 13) ℚ)}
    {hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d}
    {Q : JacobianExceptionalComponent equations}
    (hQ : Q ∈ highDegreeTopProjectiveJacobianExceptionalComponents
      equations hhomogeneous)
    {d : ℕ} (hdegree : HasProjectiveDimensionDegree Q.1 4 d) :
    8 ≤ d := by
  have hQdata := Finset.mem_filter.mp hQ
  have hnotlow := hQdata.2.1
  by_contra hd
  apply hnotlow
  apply Finset.mem_filter.mpr
  exact ⟨hQdata.1, d, hdegree, by omega⟩

/-- The three displayed lists form an exact partition of the residual list,
at the level of every finite sum. -/
theorem sum_topProjectiveJacobianExceptionalComponents_eq_degreeSplit
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    (weight : JacobianExceptionalComponent equations → ℕ) :
    (∑ Q ∈ topProjectiveJacobianExceptionalComponents
        equations hhomogeneous, weight Q) =
      (∑ Q ∈ lowDegreeTopProjectiveJacobianExceptionalComponents
          equations hhomogeneous, weight Q) +
      (∑ Q ∈ highDegreeTopProjectiveJacobianExceptionalComponents
          equations hhomogeneous, weight Q) +
      ∑ Q ∈ uncertifiedTopProjectiveJacobianExceptionalComponents
          equations hhomogeneous, weight Q := by
  classical
  let top := topProjectiveJacobianExceptionalComponents
    equations hhomogeneous
  let low : JacobianExceptionalComponent equations → Prop := fun Q ↦
    ∃ d : ℕ, HasProjectiveDimensionDegree Q.1 4 d ∧ d ≤ 7
  let certified : JacobianExceptionalComponent equations → Prop := fun Q ↦
    HasCertifiedProjectiveDegree Q
  have hfirst := Finset.sum_filter_add_sum_filter_not
    top low weight
  have hsecond := Finset.sum_filter_add_sum_filter_not
    (top.filter fun Q ↦ ¬ low Q) certified weight
  rw [← hsecond] at hfirst
  have hlow : top.filter low =
      lowDegreeTopProjectiveJacobianExceptionalComponents
        equations hhomogeneous := by
    rfl
  have hhigh : (top.filter fun Q ↦ ¬ low Q).filter certified =
      highDegreeTopProjectiveJacobianExceptionalComponents
        equations hhomogeneous := by
    ext Q
    simp only [Finset.mem_filter, top, low, certified,
      highDegreeTopProjectiveJacobianExceptionalComponents,
      lowDegreeTopProjectiveJacobianExceptionalComponents]
    constructor
    · rintro ⟨⟨hQtop, hnotlow⟩, hcertified⟩
      refine ⟨hQtop, ?_, hcertified⟩
      intro hQlow
      exact hnotlow hQlow.2
    · rintro ⟨hQtop, hnotmem, hcertified⟩
      refine ⟨⟨hQtop, ?_⟩, hcertified⟩
      intro hlowQ
      exact hnotmem ⟨hQtop, hlowQ⟩
  have huncertified :
      (top.filter fun Q ↦ ¬ low Q).filter (fun Q ↦ ¬ certified Q) =
        uncertifiedTopProjectiveJacobianExceptionalComponents
          equations hhomogeneous := by
    ext Q
    simp only [Finset.mem_filter, top, low, certified,
      uncertifiedTopProjectiveJacobianExceptionalComponents]
    constructor
    · tauto
    · rintro ⟨hQtop, hnotcertified⟩
      refine ⟨⟨hQtop, ?_⟩, hnotcertified⟩
      intro hlowQ
      apply hnotcertified
      obtain ⟨d, hd, _⟩ := hlowQ
      exact ⟨d, hd⟩
  rw [hlow, hhigh, huncertified] at hfirst
  simpa only [Nat.add_assoc] using hfirst.symm

/-- Once a literal projective degree certificate has been constructed for
every residual component, the uncertified list is empty. -/
theorem uncertifiedTopProjectiveJacobianExceptionalComponents_eq_empty
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    (hcertified : ∀ Q ∈ topProjectiveJacobianExceptionalComponents
        equations hhomogeneous, HasCertifiedProjectiveDegree Q) :
    uncertifiedTopProjectiveJacobianExceptionalComponents
      equations hhomogeneous = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro Q hQ
  have hQdata := Finset.mem_filter.mp hQ
  exact hQdata.2 (hcertified Q hQdata.1)

/-- Under the same exact Hilbert-degree existence hypothesis, the residual
sum consists only of the degree-at-most-seven and degree-at-least-eight
pieces. -/
theorem sum_topProjectiveJacobianExceptionalComponents_eq_low_add_high
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    (hcertified : ∀ Q ∈ topProjectiveJacobianExceptionalComponents
        equations hhomogeneous, HasCertifiedProjectiveDegree Q)
    (weight : JacobianExceptionalComponent equations → ℕ) :
    (∑ Q ∈ topProjectiveJacobianExceptionalComponents
        equations hhomogeneous, weight Q) =
      (∑ Q ∈ lowDegreeTopProjectiveJacobianExceptionalComponents
          equations hhomogeneous, weight Q) +
      ∑ Q ∈ highDegreeTopProjectiveJacobianExceptionalComponents
          equations hhomogeneous, weight Q := by
  have hsplit :=
    sum_topProjectiveJacobianExceptionalComponents_eq_degreeSplit
      equations hhomogeneous weight
  rw [uncertifiedTopProjectiveJacobianExceptionalComponents_eq_empty
    equations hhomogeneous hcertified] at hsplit
  simpa only [Finset.notMem_empty, Finset.sum_empty, add_zero] using hsplit

/-! ## The sharper degree split used by the final argument -/

/-- The certified projective fourfold components of degree at most two. -/
noncomputable def degreeAtMostTwoTopProjectiveJacobianExceptionalComponents
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d) :
    Finset (JacobianExceptionalComponent equations) :=
  (topProjectiveJacobianExceptionalComponents equations hhomogeneous).filter
    fun Q ↦ ∃ d : ℕ,
      HasProjectiveDimensionDegree Q.1 4 d ∧ d ≤ 2

/-- The certified components outside the preceding list.  Every displayed
degree certificate on this list has degree at least three. -/
noncomputable def degreeAtLeastThreeTopProjectiveJacobianExceptionalComponents
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d) :
    Finset (JacobianExceptionalComponent equations) :=
  (topProjectiveJacobianExceptionalComponents equations hhomogeneous).filter
    fun Q ↦
      Q ∉ degreeAtMostTwoTopProjectiveJacobianExceptionalComponents
        equations hhomogeneous ∧
      HasCertifiedProjectiveDegree Q

theorem degree_ge_three_of_mem_degreeAtLeastThreeTopProjective
    {equations : Finset (MvPolynomial (Fin 13) ℚ)}
    {hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d}
    {Q : JacobianExceptionalComponent equations}
    (hQ : Q ∈ degreeAtLeastThreeTopProjectiveJacobianExceptionalComponents
      equations hhomogeneous)
    {d : ℕ} (hdegree : HasProjectiveDimensionDegree Q.1 4 d) :
    3 ≤ d := by
  have hQdata := Finset.mem_filter.mp hQ
  have hnotlow := hQdata.2.1
  by_contra hd
  apply hnotlow
  apply Finset.mem_filter.mpr
  exact ⟨hQdata.1, d, hdegree, by omega⟩

/-- Exact degree-at-most-two / degree-at-least-three / uncertified
partition of the residual component sum. -/
theorem sum_topProjectiveJacobianExceptionalComponents_eq_degreeTwoSplit
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    (weight : JacobianExceptionalComponent equations → ℕ) :
    (∑ Q ∈ topProjectiveJacobianExceptionalComponents
        equations hhomogeneous, weight Q) =
      (∑ Q ∈ degreeAtMostTwoTopProjectiveJacobianExceptionalComponents
          equations hhomogeneous, weight Q) +
      (∑ Q ∈ degreeAtLeastThreeTopProjectiveJacobianExceptionalComponents
          equations hhomogeneous, weight Q) +
      ∑ Q ∈ uncertifiedTopProjectiveJacobianExceptionalComponents
          equations hhomogeneous, weight Q := by
  classical
  let top := topProjectiveJacobianExceptionalComponents
    equations hhomogeneous
  let low : JacobianExceptionalComponent equations → Prop := fun Q ↦
    ∃ d : ℕ, HasProjectiveDimensionDegree Q.1 4 d ∧ d ≤ 2
  let certified : JacobianExceptionalComponent equations → Prop := fun Q ↦
    HasCertifiedProjectiveDegree Q
  have hfirst := Finset.sum_filter_add_sum_filter_not top low weight
  have hsecond := Finset.sum_filter_add_sum_filter_not
    (top.filter fun Q ↦ ¬ low Q) certified weight
  rw [← hsecond] at hfirst
  have hlow : top.filter low =
      degreeAtMostTwoTopProjectiveJacobianExceptionalComponents
        equations hhomogeneous := by rfl
  have hhigh : (top.filter fun Q ↦ ¬ low Q).filter certified =
      degreeAtLeastThreeTopProjectiveJacobianExceptionalComponents
        equations hhomogeneous := by
    ext Q
    simp only [Finset.mem_filter, top, low, certified,
      degreeAtLeastThreeTopProjectiveJacobianExceptionalComponents,
      degreeAtMostTwoTopProjectiveJacobianExceptionalComponents]
    constructor
    · rintro ⟨⟨hQtop, hnotlow⟩, hcertified⟩
      refine ⟨hQtop, ?_, hcertified⟩
      intro hQlow
      exact hnotlow hQlow.2
    · rintro ⟨hQtop, hnotmem, hcertified⟩
      refine ⟨⟨hQtop, ?_⟩, hcertified⟩
      intro hlowQ
      exact hnotmem ⟨hQtop, hlowQ⟩
  have huncertified :
      (top.filter fun Q ↦ ¬ low Q).filter (fun Q ↦ ¬ certified Q) =
        uncertifiedTopProjectiveJacobianExceptionalComponents
          equations hhomogeneous := by
    ext Q
    simp only [Finset.mem_filter, top, low, certified,
      uncertifiedTopProjectiveJacobianExceptionalComponents]
    constructor
    · tauto
    · rintro ⟨hQtop, hnotcertified⟩
      refine ⟨⟨hQtop, ?_⟩, hnotcertified⟩
      intro hlowQ
      apply hnotcertified
      obtain ⟨d, hd, _⟩ := hlowQ
      exact ⟨d, hd⟩
  rw [hlow, hhigh, huncertified] at hfirst
  simpa only [Nat.add_assoc] using hfirst.symm

end

end TranslatedDepthSeven
