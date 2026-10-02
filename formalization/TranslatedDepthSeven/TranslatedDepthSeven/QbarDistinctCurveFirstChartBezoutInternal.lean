import TranslatedDepthSeven.ProjectiveExteriorPointSeparatorInternal
import TranslatedDepthSeven.ProjectiveCurveSeparatorBridgeInternal
import TranslatedDepthSeven.IsolatedVertexQuotientEdgeBezout
import Mathlib.RingTheory.Nullstellensatz

/-!
# Distinct projective curves: the reduced first-chart Bézout bound

No intersection-degree or bounded-equation premise is assumed here.  An
exterior point supplies linear normalization parameters vanishing there.
The monic relation for the first homogeneous coordinate, followed by its
homogeneous component, gives a separating equation of degree at most the
second curve's degree.  The already proved hypersurface Hilbert-function
inequality then gives the product of degrees.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

/-- A proper homogeneous equation is nonzero at a normalized point of any
nonempty first chart of an integral projective variety. -/
theorem exists_firstChartPoint_nonzero_of_not_mem_prime
    {K : Type*} [Field K] [IsAlgClosed K] {N k : ℕ}
    (P : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hP : P.IsPrime)
    (hPhom : P.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K))
    (hX : X 0 ∉ P)
    (f : MvPolynomial (Fin (N + 1)) K)
    (hfhom : f.IsHomogeneous k) (hf : f ∉ P) :
    ∃ y : Fin (N + 1) → K,
      y 0 = 1 ∧ y ∈ affineIdealZeroLocus P ∧ eval y f ≠ 0 := by
  classical
  letI : P.IsPrime := hP
  have hproduct : f * X 0 ∉ P := fun h ↦ (hP.mem_or_mem h).elim hf hX
  have hex : ∃ x ∈ MvPolynomial.zeroLocus K P, eval x (f * X 0) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hproduct
    rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := K) P]
    intro x hx
    simpa only [MvPolynomial.aeval_eq_eval] using h x hx
  obtain ⟨x, hx, hnonzero⟩ := hex
  have hmul : eval x f * x 0 ≠ 0 := by simpa using hnonzero
  have hx0 : x 0 ≠ 0 := (mul_ne_zero_iff.1 hmul).2
  have hfx : eval x f ≠ 0 := (mul_ne_zero_iff.1 hmul).1
  let y : Fin (N + 1) → K := fun i ↦ (x 0)⁻¹ * x i
  refine ⟨y, by simp [y, hx0], ?_, ?_⟩
  · apply smul_mem_affineIdealZeroLocus_of_isHomogeneous P hPhom
    intro g hg
    simpa only [MvPolynomial.aeval_eq_eval] using hx g hg
  · change eval (fun i ↦ (x 0)⁻¹ * x i) f ≠ 0
    rw [eval_smul_of_isHomogeneous f x (x 0)⁻¹ k hfhom]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hx0)) hfx

/-- Reduced first-chart Bézout for distinct integral projective curves over
an algebraically closed field of characteristic zero, proved internally. -/
theorem exists_distinct_projectiveCurve_firstChart_spanningFamily
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {N d e : ℕ}
    (P Q : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hP : P.IsPrime) (hQ : Q.IsPrime)
    (hPhom : P.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K))
    (hQhom : Q.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K))
    (hPdegree : HasProjectiveDimensionDegree P 1 d)
    (hQdegree : HasProjectiveDimensionDegree Q 1 e)
    (hne : P ≠ Q) :
    ∃ v : Fin (d * e) →
        (MvPolynomial (Fin (N + 1)) K ⧸
          ((P ⊔ Q) ⊔ Ideal.span ({X 0 - C 1} : Set _)).radical),
      Submodule.span K (Set.range v) = ⊤ := by
  classical
  letI : P.IsPrime := hP
  letI : Q.IsPrime := hQ
  by_cases hX : X 0 ∈ P
  · let J := (P ⊔ Q) ⊔ Ideal.span
      ({X 0 - C 1} : Set (MvPolynomial (Fin (N + 1)) K))
    have hXJ : X 0 ∈ J :=
      (show P ≤ J from le_sup_of_le_left le_sup_left) hX
    have hrelation : X 0 - C 1 ∈ J :=
      (show Ideal.span ({X 0 - C 1} : Set _) ≤ J from le_sup_right)
        (Ideal.subset_span (by simp))
    have hJ : J = ⊤ := by
      apply J.eq_top_of_isUnit_mem (J.sub_mem hXJ hrelation)
      simpa only [sub_sub_cancel, map_one] using
        (isUnit_one : IsUnit (1 : MvPolynomial (Fin (N + 1)) K))
    have hradical : J.radical = ⊤ := by rw [hJ, Ideal.radical_top]
    haveI : Subsingleton (MvPolynomial (Fin (N + 1)) K ⧸ J.radical) :=
      Ideal.Quotient.subsingleton_iff.2 hradical
    refine ⟨fun _ ↦ 0, ?_⟩
    exact Subsingleton.elim _ _
  · have hnotle : ¬ Q ≤ P :=
      (incomparable_of_distinct_primes_same_finite_quotient_dimension
        P Q (s := 2) hne (by simpa using hPdegree.1)
          (by simpa using hQdegree.1)).2
    obtain ⟨k, f, hfhom, hfQ, hfP⟩ :=
      exists_homogeneous_form_mem_not_mem_of_not_le P Q hQhom hnotle
    obtain ⟨y, hy0, hyP, hfy⟩ :=
      exists_firstChartPoint_nonzero_of_not_mem_prime P hP hPhom hX f hfhom hfP
    obtain ⟨l, G, hle, hGhom, hGQ, hGy⟩ :=
      exists_homogeneous_projectiveDegree_separator_at_firstChartPoint
        Q hQ hQhom hQdegree y hy0 ⟨f, hfQ, hfy⟩
    have hGP : G ∉ P := by
      intro h
      have hzero := hyP G h
      rw [hGy] at hzero
      exact one_ne_zero hzero
    exact exists_firstChart_curveIntersection_spanningFamily_of_separator
      P Q hP hPdegree G hGhom hGP hGQ hle

/-- The literal isolated-vertex quotient intersection input, with no
remaining mathematical assumption. -/
theorem qbarDistinctProjectiveCurveFirstChartBezout_internal :
    StandardAG.QbarDistinctProjectiveCurveFirstChartBezout := by
  intro N d e P Q hP hQ hPhom hQhom hPdegree hQdegree hne
  exact exists_distinct_projectiveCurve_firstChart_spanningFamily
    P Q hP hQ hPhom hQhom hPdegree hQdegree hne

end

end TranslatedDepthSeven
