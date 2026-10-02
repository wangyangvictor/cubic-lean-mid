import TranslatedDepthSeven.FiniteEquationMinimalComponents

/-!
# Components through a point of a finite equation family

For a finite polynomial family over a field in finitely many variables, this
file forms the literal finite set of minimal-prime components whose ideals
are contained in the evaluation kernel of a displayed point.  That set is
nonempty exactly when the point satisfies the original equations.

A classical choice from this finite set gives a static component label.  If
two such labels differ, the point lies on the zero locus of the supremum of
the two component ideals.  The later geometric argument must still prove the
dimension and degree bounds for that proper intersection.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

universe u v

variable {K : Type u} {σ : Type v} [Field K] [Fintype σ]

/-- The finite set of minimal-prime components of `equations` which contain
the displayed affine point. -/
def finiteEquationComponentsThroughPoint
    (equations : Finset (MvPolynomial σ K)) (z : σ → K) :
    Finset (Ideal (MvPolynomial σ K)) := by
  classical
  exact (finiteEquationMinimalPrimes equations).filter fun Q ↦
    Q ≤ RingHom.ker (MvPolynomial.eval z)

@[simp]
theorem mem_finiteEquationComponentsThroughPoint_iff
    (equations : Finset (MvPolynomial σ K)) (z : σ → K)
    (Q : Ideal (MvPolynomial σ K)) :
    Q ∈ finiteEquationComponentsThroughPoint equations z ↔
      Q ∈ finiteEquationMinimalPrimes equations ∧
        Q ≤ RingHom.ker (MvPolynomial.eval z) := by
  classical
  simp [finiteEquationComponentsThroughPoint]

/-- Every point of the displayed common zero locus lies on at least one
minimal-prime component. -/
theorem finiteEquationComponentsThroughPoint_nonempty_of_mem
    (equations : Finset (MvPolynomial σ K)) (z : σ → K)
    (hz : z ∈ finiteAffineCommonZeroLocus equations) :
    (finiteEquationComponentsThroughPoint equations z).Nonempty := by
  classical
  let P : Ideal (MvPolynomial σ K) :=
    RingHom.ker (MvPolynomial.eval z)
  letI : P.IsPrime := RingHom.ker_isPrime (MvPolynomial.eval z)
  have hIP : finiteEquationIdeal equations ≤ P := by
    rw [← affineIdealZeroLocus_finiteEquationIdeal] at hz
    intro f hf
    change MvPolynomial.eval z f = 0
    exact hz f hf
  obtain ⟨Q, hQ, hQP⟩ := exists_finiteMinimalPrime_le hIP
  exact ⟨Q,
    (mem_finiteEquationComponentsThroughPoint_iff equations z Q).2
      ⟨hQ, hQP⟩⟩

/-- Conversely, a component through the point forces all the original
equations to vanish there. -/
theorem mem_finiteAffineCommonZeroLocus_of_componentsThroughPoint_nonempty
    (equations : Finset (MvPolynomial σ K)) (z : σ → K)
    (h : (finiteEquationComponentsThroughPoint equations z).Nonempty) :
    z ∈ finiteAffineCommonZeroLocus equations := by
  classical
  obtain ⟨Q, hQ⟩ := h
  have hQspec :=
    (mem_finiteEquationComponentsThroughPoint_iff equations z Q).1 hQ
  rw [← affineIdealZeroLocus_finiteEquationIdeal]
  intro f hf
  have hIf : f ∈ Q := (le_of_mem_finiteMinimalPrimes hQspec.1) hf
  exact RingHom.mem_ker.mp (hQspec.2 hIf)

/-- Exact nonemptiness criterion for the finite list of components through a
point. -/
theorem finiteEquationComponentsThroughPoint_nonempty_iff
    (equations : Finset (MvPolynomial σ K)) (z : σ → K) :
    (finiteEquationComponentsThroughPoint equations z).Nonempty ↔
      z ∈ finiteAffineCommonZeroLocus equations :=
  ⟨mem_finiteAffineCommonZeroLocus_of_componentsThroughPoint_nonempty
      equations z,
    finiteEquationComponentsThroughPoint_nonempty_of_mem equations z⟩

/-- A static component label: `none` off the displayed locus, and one actual
minimal-prime component through the point on the locus. -/
def selectedFiniteEquationComponent
    (equations : Finset (MvPolynomial σ K)) (z : σ → K) :
    Option (Ideal (MvPolynomial σ K)) :=
  if h : (finiteEquationComponentsThroughPoint equations z).Nonempty then
    some h.choose
  else
    none

/-- The selected label is absent exactly off the displayed common zero
locus. -/
theorem selectedFiniteEquationComponent_eq_none_iff
    (equations : Finset (MvPolynomial σ K)) (z : σ → K) :
    selectedFiniteEquationComponent equations z = none ↔
      z ∉ finiteAffineCommonZeroLocus equations := by
  classical
  by_cases h : (finiteEquationComponentsThroughPoint equations z).Nonempty
  · have hz :=
      mem_finiteAffineCommonZeroLocus_of_componentsThroughPoint_nonempty
        equations z h
    simp [selectedFiniteEquationComponent, h, hz]
  · have hz : z ∉ finiteAffineCommonZeroLocus equations := by
      intro hz
      exact h
        (finiteEquationComponentsThroughPoint_nonempty_of_mem equations z hz)
    simp [selectedFiniteEquationComponent, h, hz]

/-- Every nonempty selected label is an actual minimal-prime component and
its ideal vanishes at the point. -/
theorem selectedFiniteEquationComponent_spec
    (equations : Finset (MvPolynomial σ K)) (z : σ → K)
    {Q : Ideal (MvPolynomial σ K)}
    (hQ : selectedFiniteEquationComponent equations z = some Q) :
    Q ∈ finiteEquationMinimalPrimes equations ∧
      Q ≤ RingHom.ker (MvPolynomial.eval z) := by
  classical
  unfold selectedFiniteEquationComponent at hQ
  split at hQ
  next h =>
    have hmem : h.choose ∈
        finiteEquationComponentsThroughPoint equations z := h.choose_spec
    have hEq : h.choose = Q := Option.some.inj hQ
    simpa [hEq] using
      (mem_finiteEquationComponentsThroughPoint_iff
        equations z h.choose).1 hmem
  next h => simp at hQ

/-- If two selected component labels occur at the same point, that point lies
on the literal ideal-theoretic intersection of the two components. -/
theorem mem_affineIdealZeroLocus_sup_of_two_selected_components
    (equations₁ equations₂ : Finset (MvPolynomial σ K)) (z : σ → K)
    {Q₁ Q₂ : Ideal (MvPolynomial σ K)}
    (hQ₁ : selectedFiniteEquationComponent equations₁ z = some Q₁)
    (hQ₂ : selectedFiniteEquationComponent equations₂ z = some Q₂) :
    z ∈ affineIdealZeroLocus (Q₁ ⊔ Q₂) := by
  have h₁ := (selectedFiniteEquationComponent_spec equations₁ z hQ₁).2
  have h₂ := (selectedFiniteEquationComponent_spec equations₂ z hQ₂).2
  intro f hf
  exact RingHom.mem_ker.mp ((sup_le h₁ h₂) hf)

end

end TranslatedDepthSeven
