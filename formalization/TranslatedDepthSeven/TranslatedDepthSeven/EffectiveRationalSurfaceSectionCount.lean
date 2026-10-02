import TranslatedDepthSeven.EffectiveAffineCurveCount
import TranslatedDepthSeven.ProjectiveSurfaceRationalAffineSection

/-!
# Degree-effective counting on a rational surface section

This file applies the degree-effective rational affine-curve estimate to
the actual minimal prime ideals of a rational affine chart.  The degree-one
part is retained as a literal finite union.  The nonlinear contribution has
polynomial dependence on the *current* total component-degree mass, so the
cutting degree is allowed to vary with the height.

The final specialization uses the internal rational surface-section
Bezout theorem.  It has no bounded-cutting-degree parameter and introduces
no new geometric premise.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 300000

/-- The members of a finite integral point set which vanish on a rational
affine ideal. -/
def finitePointsOnRationalAffineIdeal {N : ℕ}
    (X : Finset (IntVector N))
    (Q : Ideal (MvPolynomial (Fin N) ℚ)) : Finset (IntVector N) := by
  classical
  exact X.filter fun z ↦
    (fun i ↦ (z i : ℚ)) ∈ affineIdealZeroLocus Q

@[simp]
theorem mem_finitePointsOnRationalAffineIdeal_iff {N : ℕ}
    (X : Finset (IntVector N))
    (Q : Ideal (MvPolynomial (Fin N) ℚ)) (z : IntVector N) :
    z ∈ finitePointsOnRationalAffineIdeal X Q ↔
      z ∈ X ∧ (fun i ↦ (z i : ℚ)) ∈ affineIdealZeroLocus Q := by
  classical
  simp [finitePointsOnRationalAffineIdeal]

/-- The literal subset of `X` lying on at least one rational degree-one
affine curve component of `J`. -/
def finitePointsOnRationalLinearCurveComponents {N : ℕ}
    (J : Ideal (MvPolynomial (Fin N) ℚ))
    (X : Finset (IntVector N)) : Finset (IntVector N) := by
  classical
  exact (finiteMinimalPrimes J).biUnion fun Q ↦
    if HasAffineHilbertDimensionDegree Q 1 1 then
      finitePointsOnRationalAffineIdeal X Q
    else ∅

/-- The actual rational minimal components not certified to be degree-one
affine curves. -/
def nonlinearRationalAffineComponents {N : ℕ}
    (J : Ideal (MvPolynomial (Fin N) ℚ)) :
    Finset (Ideal (MvPolynomial (Fin N) ℚ)) := by
  classical
  exact (finiteMinimalPrimes J).filter fun Q ↦
    ¬ HasAffineHilbertDimensionDegree Q 1 1

/-- Strict integral box membership together with rational vanishing gives
membership in the literal point set used by the effective curve theorem. -/
theorem intPoint_mem_rationalPilaIntegralPoints_of_mem_zeroLocus
    {N : ℕ} (Q : Ideal (MvPolynomial (Fin N) ℚ))
    (H : ℝ) (z : IntVector N)
    (hbox : ∀ i, |(z i : ℝ)| < H)
    (hzero : (fun i ↦ (z i : ℚ)) ∈ affineIdealZeroLocus Q) :
    z ∈ rationalPilaIntegralPoints Q H := by
  classical
  rw [rationalPilaIntegralPoints, Finset.mem_filter]
  refine ⟨?_, hbox, hzero⟩
  rw [mem_integerSupNormBox_iff]
  intro i
  have hceil : H ≤ (⌈H⌉₊ : ℝ) := Nat.le_ceil H
  have habs : ((z i).natAbs : ℝ) ≤ (⌈H⌉₊ : ℝ) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using
      (le_of_lt (hbox i)).trans hceil
  exact_mod_cast habs

/-- A total degree-mass bound controls the number of components, because
every displayed Hilbert degree is positive. -/
theorem nonlinearRationalAffineComponents_card_le_degreeMass
    {N E : ℕ} (J : Ideal (MvPolynomial (Fin N) ℚ))
    (degree : Ideal (MvPolynomial (Fin N) ℚ) → ℕ)
    (hcomponents : ∀ Q ∈ finiteMinimalPrimes J,
      HasAffineHilbertDimensionDegree Q 1 (degree Q))
    (hmass : ∑ Q ∈ finiteMinimalPrimes J, degree Q ≤ E) :
    (nonlinearRationalAffineComponents J).card ≤ E := by
  classical
  calc
    (nonlinearRationalAffineComponents J).card =
        ∑ _Q ∈ nonlinearRationalAffineComponents J, 1 := by simp
    _ ≤ ∑ Q ∈ nonlinearRationalAffineComponents J, degree Q := by
      apply Finset.sum_le_sum
      intro Q hQ
      have hQmin : Q ∈ finiteMinimalPrimes J := (Finset.mem_filter.mp hQ).1
      exact (hcomponents Q hQmin).2.1
    _ ≤ ∑ Q ∈ finiteMinimalPrimes J, degree Q := by
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ ≤ E := hmass

/-- Each displayed component degree is at most the total degree mass. -/
theorem componentDegree_le_degreeMass
    {N E : ℕ} (J : Ideal (MvPolynomial (Fin N) ℚ))
    (degree : Ideal (MvPolynomial (Fin N) ℚ) → ℕ)
    (hmass : ∑ Q ∈ finiteMinimalPrimes J, degree Q ≤ E)
    {Q : Ideal (MvPolynomial (Fin N) ℚ)}
    (hQ : Q ∈ finiteMinimalPrimes J) :
    degree Q ≤ E := by
  have hterm : degree Q ≤
      ∑ R ∈ finiteMinimalPrimes J, degree R := by
    exact Finset.single_le_sum
      (fun R _ ↦ Nat.zero_le (degree R)) hQ
  exact hterm.trans hmass

/-- Degree-effective component aggregation.  The constant depends only on
the ambient affine dimension.  In particular it is chosen before `E`, the
ideal, all component degrees, the point set, and the height. -/
theorem exists_uniform_rationalAffineCurveComponents_effectiveCount
    (hCurve : CDHNV2025Corollary22)
    {N : ℕ} (hN : 2 ≤ N) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (E : ℕ) (J : Ideal (MvPolynomial (Fin N) ℚ))
        (degree : Ideal (MvPolynomial (Fin N) ℚ) → ℕ),
        (∀ Q ∈ finiteMinimalPrimes J,
          HasAffineHilbertDimensionDegree Q 1 (degree Q)) →
        (∑ Q ∈ finiteMinimalPrimes J, degree Q ≤ E) →
        ∀ (X : Finset (IntVector N)),
          (∀ z ∈ X,
            (fun i ↦ (z i : ℚ)) ∈ affineIdealZeroLocus J) →
          ∀ H : ℝ, 1 < H →
            (∀ z ∈ X, ∀ i, |(z i : ℝ)| < H) →
            (X.card : ℝ) ≤
              ((finitePointsOnRationalLinearCurveComponents J X).card : ℝ) +
                c * (E : ℝ) ^ (4 : ℕ) * H ^ (1 / 2 : ℝ) *
                  (Real.log H + (E : ℝ)) := by
  classical
  obtain ⟨c, hc, hcurve⟩ := cDHNV2025_curve_halfPower hCurve hN
  refine ⟨c, hc, ?_⟩
  intro E J degree hcomponents hmass X hXzero H hH hXbox
  let nonlinearUnion : Finset (IntVector N) :=
    (nonlinearRationalAffineComponents J).biUnion fun Q ↦
      finitePointsOnRationalAffineIdeal X Q
  have hcover : X ⊆ finitePointsOnRationalLinearCurveComponents J X ∪
      nonlinearUnion := by
    intro z hz
    let T : Ideal (MvPolynomial (Fin N) ℚ) :=
      RingHom.ker (MvPolynomial.eval (fun i ↦ (z i : ℚ)))
    letI : T.IsPrime := RingHom.ker_isPrime _
    have hJT : J ≤ T := by
      intro f hf
      exact RingHom.mem_ker.mpr (hXzero z hz f hf)
    obtain ⟨Q, hQ, hQT⟩ := exists_finiteMinimalPrime_le hJT
    by_cases hlinear : HasAffineHilbertDimensionDegree Q 1 1
    · apply Finset.mem_union_left
      rw [finitePointsOnRationalLinearCurveComponents]
      refine Finset.mem_biUnion.mpr ⟨Q, hQ, ?_⟩
      simp only [if_pos hlinear]
      exact (mem_finitePointsOnRationalAffineIdeal_iff X Q z).mpr
        ⟨hz, fun f hf ↦ RingHom.mem_ker.mp (hQT hf)⟩
    · apply Finset.mem_union_right
      refine Finset.mem_biUnion.mpr ⟨Q, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨hQ, hlinear⟩
      · exact (mem_finitePointsOnRationalAffineIdeal_iff X Q z).mpr
          ⟨hz, fun f hf ↦ RingHom.mem_ker.mp (hQT hf)⟩
  have hcardCover : X.card ≤
      (finitePointsOnRationalLinearCurveComponents J X).card +
        nonlinearUnion.card :=
    calc
      X.card ≤
          (finitePointsOnRationalLinearCurveComponents J X ∪
            nonlinearUnion).card := Finset.card_le_card hcover
      _ ≤ (finitePointsOnRationalLinearCurveComponents J X).card +
          nonlinearUnion.card := Finset.card_union_le _ _
  have hcomponentCard : (nonlinearRationalAffineComponents J).card ≤ E :=
    nonlinearRationalAffineComponents_card_le_degreeMass
      J degree hcomponents hmass
  have hhalf : 0 ≤ H ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (by linarith : 0 ≤ H) _
  have hlog : 0 ≤ Real.log H := Real.log_nonneg hH.le
  have hnonlinearCard : (nonlinearUnion.card : ℝ) ≤
      c * (E : ℝ) ^ (4 : ℕ) * H ^ (1 / 2 : ℝ) *
        (Real.log H + (E : ℝ)) := by
    have hnat : nonlinearUnion.card ≤
        ∑ Q ∈ nonlinearRationalAffineComponents J,
          (finitePointsOnRationalAffineIdeal X Q).card := by
      exact Finset.card_biUnion_le
    have hsum :
        (∑ Q ∈ nonlinearRationalAffineComponents J,
          ((finitePointsOnRationalAffineIdeal X Q).card : ℝ)) ≤
        ∑ _Q ∈ nonlinearRationalAffineComponents J,
          c * (E : ℝ) ^ (3 : ℕ) * H ^ (1 / 2 : ℝ) *
            (Real.log H + (E : ℝ)) := by
      apply Finset.sum_le_sum
      intro Q hQ
      have hQmin : Q ∈ finiteMinimalPrimes J :=
        (Finset.mem_filter.mp hQ).1
      have hQnot : ¬ HasAffineHilbertDimensionDegree Q 1 1 :=
        (Finset.mem_filter.mp hQ).2
      have hQdata := hcomponents Q hQmin
      have hdpos : 0 < degree Q := hQdata.2.1
      have hdne : degree Q ≠ 1 := by
        intro hd
        apply hQnot
        simpa only [hd] using hQdata
      have hd : 2 ≤ degree Q := by omega
      have hdE : degree Q ≤ E :=
        componentDegree_le_degreeMass J degree hmass hQmin
      have hsubset : finitePointsOnRationalAffineIdeal X Q ⊆
          rationalPilaIntegralPoints Q H := by
        intro z hz
        have hzspec :=
          (mem_finitePointsOnRationalAffineIdeal_iff X Q z).mp hz
        exact intPoint_mem_rationalPilaIntegralPoints_of_mem_zeroLocus
          Q H z (hXbox z hzspec.1) hzspec.2
      have hsource := hcurve (degree Q) hd Q hQdata H hH
      have hdegreeCast : (degree Q : ℝ) ≤ (E : ℝ) := by
        exact_mod_cast hdE
      have hdegreePow : (degree Q : ℝ) ^ (3 : ℕ) ≤
          (E : ℝ) ^ (3 : ℕ) := by
        exact pow_le_pow_left₀ (by positivity) hdegreeCast 3
      have hlogDegree : Real.log H + (degree Q : ℝ) ≤
          Real.log H + (E : ℝ) := add_le_add_right hdegreeCast _
      calc
        ((finitePointsOnRationalAffineIdeal X Q).card : ℝ) ≤
            ((rationalPilaIntegralPoints Q H).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsubset
        _ ≤ c * (degree Q : ℝ) ^ (3 : ℕ) *
              H ^ (1 / 2 : ℝ) *
              (Real.log H + (degree Q : ℝ)) := hsource
        _ ≤ c * (E : ℝ) ^ (3 : ℕ) * H ^ (1 / 2 : ℝ) *
              (Real.log H + (E : ℝ)) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hdegreePow hc.le) hhalf)
            hlogDegree (by positivity)
            (mul_nonneg
              (mul_nonneg hc.le (by positivity)) hhalf)
    have hcardCast :
        ((nonlinearRationalAffineComponents J).card : ℝ) ≤ (E : ℝ) := by
      exact_mod_cast hcomponentCard
    have hcommonNonneg : 0 ≤
        c * (E : ℝ) ^ (3 : ℕ) * H ^ (1 / 2 : ℝ) *
          (Real.log H + (E : ℝ)) := by positivity
    calc
      (nonlinearUnion.card : ℝ) ≤
          ∑ Q ∈ nonlinearRationalAffineComponents J,
            ((finitePointsOnRationalAffineIdeal X Q).card : ℝ) := by
        exact_mod_cast hnat
      _ ≤ ∑ _Q ∈ nonlinearRationalAffineComponents J,
          c * (E : ℝ) ^ (3 : ℕ) * H ^ (1 / 2 : ℝ) *
            (Real.log H + (E : ℝ)) := hsum
      _ = ((nonlinearRationalAffineComponents J).card : ℝ) *
          (c * (E : ℝ) ^ (3 : ℕ) * H ^ (1 / 2 : ℝ) *
            (Real.log H + (E : ℝ))) := by simp
      _ ≤ (E : ℝ) *
          (c * (E : ℝ) ^ (3 : ℕ) * H ^ (1 / 2 : ℝ) *
            (Real.log H + (E : ℝ))) :=
        mul_le_mul_of_nonneg_right hcardCast hcommonNonneg
      _ = c * (E : ℝ) ^ (4 : ℕ) * H ^ (1 / 2 : ℝ) *
          (Real.log H + (E : ℝ)) := by ring
  have hreal : (X.card : ℝ) ≤
      ((finitePointsOnRationalLinearCurveComponents J X).card : ℝ) +
        (nonlinearUnion.card : ℝ) := by
    exact_mod_cast hcardCover
  exact hreal.trans (add_le_add (le_refl _) hnonlinearCard)

/-- A rational affine point on `I` and `G` belongs to the literal rational
first-chart intersection ideal. -/
theorem intPoint_mem_rationalAffineChartIntersectionIdeal
    {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (G : MvPolynomial (Fin (N + 1)) ℚ)
    (z : IntVector N)
    (hI : ∀ f ∈ I,
      MvPolynomial.eval
        (fun i ↦ ((Fin.cases (1 : ℤ) z i : ℤ) : ℚ)) f = 0)
    (hG : MvPolynomial.eval
      (fun i ↦ ((Fin.cases (1 : ℤ) z i : ℤ) : ℚ)) G = 0) :
    (fun i ↦ (z i : ℚ)) ∈ affineIdealZeroLocus
      (rationalAffineChartIntersectionIdeal I G) := by
  rw [mem_affineIdealZeroLocus_iff]
  change rationalAffineChartIntersectionIdeal I G ≤
    RingHom.ker (MvPolynomial.eval (fun i ↦ (z i : ℚ)))
  rw [rationalAffineChartIntersectionIdeal, Ideal.map_le_iff_le_comap]
  apply sup_le
  · intro f hf
    change MvPolynomial.eval (fun i ↦ (z i : ℚ))
      (standardDehomogenizationHom ℚ N f) = 0
    rw [eval_standardDehomogenizationHom]
    have hx :
        (fun i : Fin (N + 1) ↦
          Fin.cases (1 : ℚ) (fun j ↦ (z j : ℚ)) i) =
        (fun i ↦ ((Fin.cases (1 : ℤ) z i : ℤ) : ℚ)) := by
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
    rw [hx]
    exact hI f hf
  · rw [Ideal.span_le]
    intro f hf
    simp only [Set.mem_singleton_iff] at hf
    subst f
    change MvPolynomial.eval (fun i ↦ (z i : ℚ))
      (standardDehomogenizationHom ℚ N G) = 0
    rw [eval_standardDehomogenizationHom]
    have hx :
        (fun i : Fin (N + 1) ↦
          Fin.cases (1 : ℚ) (fun j ↦ (z j : ℚ)) i) =
        (fun i ↦ ((Fin.cases (1 : ℤ) z i : ℤ) : ℚ)) := by
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
    rw [hx]
    exact hG

/-- Degree-effective counting for the actual rational affine chart of a
proper projective surface section.  The cutting degree `a` is quantified
after the constant and may therefore grow with the height. -/
theorem exists_uniform_projectiveSurface_rationalAffineSection_effectiveCount
    (hCurve : CDHNV2025Corollary22)
    {N : ℕ} (hN : 2 ≤ N) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d a : ℕ)
        (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
        (G : MvPolynomial (Fin (N + 1)) ℚ),
        I.IsPrime →
        I.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
        HasProjectiveDimensionDegree I 2 d →
        G.IsHomogeneous a → G ∉ I →
        ∀ (X : Finset (IntVector N)),
          (∀ z ∈ X, ∀ f ∈ I,
            MvPolynomial.eval
              (fun i ↦ ((Fin.cases (1 : ℤ) z i : ℤ) : ℚ)) f = 0) →
          (∀ z ∈ X, MvPolynomial.eval
            (fun i ↦ ((Fin.cases (1 : ℤ) z i : ℤ) : ℚ)) G = 0) →
          ∀ H : ℝ, 1 < H →
            (∀ z ∈ X, ∀ i, |(z i : ℝ)| < H) →
            (X.card : ℝ) ≤
              ((finitePointsOnRationalLinearCurveComponents
                (rationalAffineChartIntersectionIdeal I G) X).card : ℝ) +
                c * (d * a : ℕ) ^ (4 : ℕ) * H ^ (1 / 2 : ℝ) *
                  (Real.log H + (d * a : ℕ)) := by
  classical
  obtain ⟨c, hc, hcount⟩ :=
    exists_uniform_rationalAffineCurveComponents_effectiveCount hCurve hN
  refine ⟨c, hc, ?_⟩
  intro d a I G hIprime hIhom hIprojective hGhom hGnot X hXI hXG H hH hbox
  obtain ⟨degree, hcomponents, hmass⟩ :=
    projectiveSurface_rationalAffineSection_degreeMass
      I G hIprime hIhom hIprojective hGhom hGnot
  have hXchart : ∀ z ∈ X, (fun i ↦ (z i : ℚ)) ∈
      affineIdealZeroLocus (rationalAffineChartIntersectionIdeal I G) := by
    intro z hz
    exact intPoint_mem_rationalAffineChartIntersectionIdeal
      I G z (hXI z hz) (hXG z hz)
  exact hcount (d * a) (rationalAffineChartIntersectionIdeal I G)
    degree hcomponents hmass X hXchart H hH hbox

end

end TranslatedDepthSeven
