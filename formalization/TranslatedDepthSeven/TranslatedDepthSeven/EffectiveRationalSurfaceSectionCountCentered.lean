import TranslatedDepthSeven.EffectiveRationalSurfaceSectionCount
import TranslatedDepthSeven.HilbertAffineChange
import TranslatedDepthSeven.FiniteResiduePacketRescaling

/-!
# Degree-effective curve counting in a translated box

The published effective curve estimate is stated for a box centred at the
origin.  A nonempty finite slice in an arbitrary real-centred box can be
translated by one of its integral points.  The translated points remain
integral and lie in the origin-centred box of side `2 * R + 2`; the literal
affine polynomial automorphism preserves the affine Hilbert dimension and
degree.  Thus no translation-uniform strengthening of the published input is
needed.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 300000

/-- Translation by an integral base point carries rational affine zeros to
zeros of the mapped ideal. -/
theorem integralDifference_mem_affineChange_zeroLocus
    {N : ℕ} (Q : Ideal (MvPolynomial (Fin N) ℚ))
    (base z : IntVector N)
    (hzQ : (fun i ↦ (z i : ℚ)) ∈ affineIdealZeroLocus Q) :
    (fun i ↦ ((z i - base i : ℤ) : ℚ)) ∈
      affineIdealZeroLocus
        (Q.map (affinePolynomialChangeAlgEquiv
          (fun i ↦ (base i : ℚ)) 1 one_ne_zero)) := by
  change Q.map (affinePolynomialChangeAlgEquiv
      (fun i ↦ (base i : ℚ)) 1 one_ne_zero) ≤
    RingHom.ker (MvPolynomial.eval
      (fun i ↦ ((z i - base i : ℤ) : ℚ)))
  rw [Ideal.map_le_iff_le_comap]
  intro f hf
  rw [Ideal.mem_comap, RingHom.mem_ker]
  change MvPolynomial.aeval (fun i ↦ ((z i - base i : ℤ) : ℚ))
      (affinePolynomialChangeAlgEquiv
        (fun i ↦ (base i : ℚ)) 1 one_ne_zero f) = 0
  rw [aeval_affinePolynomialChange]
  have hpoint :
      (fun i ↦ (base i : ℚ) + 1 * ((z i - base i : ℤ) : ℚ)) =
        fun i ↦ (z i : ℚ) := by
    funext i
    push_cast
    ring
  rw [hpoint]
  exact hzQ f hf

/-- Division by a positive common congruence modulus carries rational
affine zeros to zeros of the corresponding affine change of the ideal. -/
theorem congruenceDisplacement_mem_rationalAffineChange_zeroLocus
    {N q : ℕ} (hq : 0 < q)
    (Q : Ideal (MvPolynomial (Fin N) ℚ))
    (base z : IntVector N) (hzcong : IntVectorCongruent q z base)
    (hzQ : (fun i ↦ (z i : ℚ)) ∈ affineIdealZeroLocus Q) :
    (fun i ↦ (congruenceDisplacementOrZero q base z i : ℚ)) ∈
      affineIdealZeroLocus
        (Q.map (affinePolynomialChangeAlgEquiv
          (fun i ↦ (base i : ℚ)) (q : ℚ)
          (by exact_mod_cast hq.ne'))) := by
  change Q.map (affinePolynomialChangeAlgEquiv
      (fun i ↦ (base i : ℚ)) (q : ℚ)
      (by exact_mod_cast hq.ne')) ≤
    RingHom.ker (MvPolynomial.eval
      (fun i ↦ (congruenceDisplacementOrZero q base z i : ℚ)))
  rw [Ideal.map_le_iff_le_comap]
  intro f hf
  rw [Ideal.mem_comap, RingHom.mem_ker]
  change MvPolynomial.aeval
      (fun i ↦ (congruenceDisplacementOrZero q base z i : ℚ))
      (affinePolynomialChangeAlgEquiv
        (fun i ↦ (base i : ℚ)) (q : ℚ)
        (by exact_mod_cast hq.ne') f) = 0
  rw [aeval_affinePolynomialChange]
  have hpoint :
      (fun i ↦ (base i : ℚ) + (q : ℚ) *
        (congruenceDisplacementOrZero q base z i : ℚ)) =
      fun i ↦ (z i : ℚ) := by
    funext i
    exact_mod_cast (congruenceDisplacementOrZero_spec base z hzcong i).symm
  rw [hpoint]
  exact hzQ f hf

/-- Two integral points in the same real-centred box differ by less than
`2 * R + 2` in every coordinate. -/
theorem integralDifference_lt_two_mul_radius_add_two
    {N : ℕ} (center : RealVector N) {R : ℝ} (hR : 0 ≤ R)
    (base z : IntVector N)
    (hbase : ∀ i, |(base i : ℝ) - center i| ≤ R)
    (hz : ∀ i, |(z i : ℝ) - center i| ≤ R) (i : Fin N) :
    |((z i - base i : ℤ) : ℝ)| < 2 * R + 2 := by
  have htriangle : |(z i : ℝ) - (base i : ℝ)| ≤
      |(z i : ℝ) - center i| + |(base i : ℝ) - center i| := by
    have h := abs_sub_le (z i : ℝ) (center i) (base i : ℝ)
    simpa only [abs_sub_comm (center i) (base i : ℝ)] using h
  have htwo : |(z i : ℝ) - (base i : ℝ)| ≤ 2 * R := by
    linarith [hz i, hbase i]
  norm_num only [Int.cast_sub]
  linarith

/-- The effective affine-curve theorem in an arbitrary translated box.
The constant is exactly the one from the origin-centred theorem; translating
by a point of the finite slice changes only the displayed height. -/
theorem exists_uniform_rationalAffineCurveComponents_effectiveCount_centered
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
          ∀ (center : RealVector N) (R : ℝ), 0 ≤ R →
            (∀ z ∈ X, ∀ i, |(z i : ℝ) - center i| ≤ R) →
            (X.card : ℝ) ≤
              ((finitePointsOnRationalLinearCurveComponents J X).card : ℝ) +
                c * (E : ℝ) ^ (4 : ℕ) *
                  (2 * R + 2) ^ (1 / 2 : ℝ) *
                  (Real.log (2 * R + 2) + (E : ℝ)) := by
  classical
  obtain ⟨c, hc, hcurve⟩ := cDHNV2025_curve_halfPower hCurve hN
  refine ⟨c, hc, ?_⟩
  intro E J degree hcomponents hmass X hXzero center R hR hXbox
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
  have hheight : 1 < 2 * R + 2 := by linarith
  have hhalf : 0 ≤ (2 * R + 2) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (by linarith) _
  have hlog : 0 ≤ Real.log (2 * R + 2) :=
    Real.log_nonneg hheight.le
  have hnonlinearCard : (nonlinearUnion.card : ℝ) ≤
      c * (E : ℝ) ^ (4 : ℕ) * (2 * R + 2) ^ (1 / 2 : ℝ) *
        (Real.log (2 * R + 2) + (E : ℝ)) := by
    have hnat : nonlinearUnion.card ≤
        ∑ Q ∈ nonlinearRationalAffineComponents J,
          (finitePointsOnRationalAffineIdeal X Q).card := by
      exact Finset.card_biUnion_le
    have hsum :
        (∑ Q ∈ nonlinearRationalAffineComponents J,
          ((finitePointsOnRationalAffineIdeal X Q).card : ℝ)) ≤
        ∑ _Q ∈ nonlinearRationalAffineComponents J,
          c * (E : ℝ) ^ (3 : ℕ) *
            (2 * R + 2) ^ (1 / 2 : ℝ) *
            (Real.log (2 * R + 2) + (E : ℝ)) := by
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
      let points := finitePointsOnRationalAffineIdeal X Q
      by_cases hpoints : points.Nonempty
      · let base : IntVector N := Classical.choose hpoints
        have hbase : base ∈ points := Classical.choose_spec hpoints
        let shift : IntVector N → IntVector N := fun z i ↦ z i - base i
        let shifted : Finset (IntVector N) := points.image shift
        let Q' := Q.map (affinePolynomialChangeAlgEquiv
          (fun i ↦ (base i : ℚ)) 1 one_ne_zero)
        have hQdata' : HasAffineHilbertDimensionDegree Q' 1 (degree Q) := by
          exact (hasAffineHilbertDimensionDegree_map_affinePolynomialChange_iff
            Q (fun i ↦ (base i : ℚ)) 1 one_ne_zero 1 (degree Q)).2 hQdata
        have hshiftInjective : Function.Injective shift := by
          intro z w hzw
          funext i
          have hi := congrFun hzw i
          dsimp only [shift] at hi
          omega
        have hshiftedCard : shifted.card = points.card := by
          exact Finset.card_image_of_injective points hshiftInjective
        have hbaseX : base ∈ X :=
          (mem_finitePointsOnRationalAffineIdeal_iff X Q base).mp hbase |>.1
        have hsubset : shifted ⊆ rationalPilaIntegralPoints Q' (2 * R + 2) := by
          intro w hw
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
          have hzspec :=
            (mem_finitePointsOnRationalAffineIdeal_iff X Q z).mp hz
          exact intPoint_mem_rationalPilaIntegralPoints_of_mem_zeroLocus
            Q' (2 * R + 2) (shift z)
            (by
              intro i
              exact integralDifference_lt_two_mul_radius_add_two
                center hR base z (hXbox base hbaseX) (hXbox z hzspec.1) i)
            (by
              dsimp only [Q', shift]
              exact integralDifference_mem_affineChange_zeroLocus
                Q base z hzspec.2)
        have hsource := hcurve (degree Q) hd Q' hQdata' (2 * R + 2) hheight
        have hdegreeCast : (degree Q : ℝ) ≤ (E : ℝ) := by
          exact_mod_cast hdE
        have hdegreePow : (degree Q : ℝ) ^ (3 : ℕ) ≤
            (E : ℝ) ^ (3 : ℕ) := by
          exact pow_le_pow_left₀ (by positivity) hdegreeCast 3
        have hlogDegree : Real.log (2 * R + 2) + (degree Q : ℝ) ≤
            Real.log (2 * R + 2) + (E : ℝ) :=
          add_le_add_right hdegreeCast _
        calc
          (points.card : ℝ) = (shifted.card : ℝ) := by rw [hshiftedCard]
          _ ≤ ((rationalPilaIntegralPoints Q' (2 * R + 2)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsubset
          _ ≤ c * (degree Q : ℝ) ^ (3 : ℕ) *
                (2 * R + 2) ^ (1 / 2 : ℝ) *
                (Real.log (2 * R + 2) + (degree Q : ℝ)) := hsource
          _ ≤ c * (E : ℝ) ^ (3 : ℕ) *
                (2 * R + 2) ^ (1 / 2 : ℝ) *
                (Real.log (2 * R + 2) + (E : ℝ)) := by
            exact mul_le_mul
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hdegreePow hc.le) hhalf)
              hlogDegree (by positivity)
              (mul_nonneg (mul_nonneg hc.le (by positivity)) hhalf)
      · have hempty : points = ∅ := Finset.not_nonempty_iff_eq_empty.mp hpoints
        simp only [points, hempty, Finset.card_empty, Nat.cast_zero]
        positivity
    have hcardCast :
        ((nonlinearRationalAffineComponents J).card : ℝ) ≤ (E : ℝ) := by
      exact_mod_cast hcomponentCard
    have hcommonNonneg : 0 ≤
        c * (E : ℝ) ^ (3 : ℕ) * (2 * R + 2) ^ (1 / 2 : ℝ) *
          (Real.log (2 * R + 2) + (E : ℝ)) := by positivity
    calc
      (nonlinearUnion.card : ℝ) ≤
          ∑ Q ∈ nonlinearRationalAffineComponents J,
            ((finitePointsOnRationalAffineIdeal X Q).card : ℝ) := by
        exact_mod_cast hnat
      _ ≤ ∑ _Q ∈ nonlinearRationalAffineComponents J,
          c * (E : ℝ) ^ (3 : ℕ) * (2 * R + 2) ^ (1 / 2 : ℝ) *
            (Real.log (2 * R + 2) + (E : ℝ)) := hsum
      _ = ((nonlinearRationalAffineComponents J).card : ℝ) *
          (c * (E : ℝ) ^ (3 : ℕ) * (2 * R + 2) ^ (1 / 2 : ℝ) *
            (Real.log (2 * R + 2) + (E : ℝ))) := by simp
      _ ≤ (E : ℝ) *
          (c * (E : ℝ) ^ (3 : ℕ) * (2 * R + 2) ^ (1 / 2 : ℝ) *
            (Real.log (2 * R + 2) + (E : ℝ))) :=
        mul_le_mul_of_nonneg_right hcardCast hcommonNonneg
      _ = c * (E : ℝ) ^ (4 : ℕ) * (2 * R + 2) ^ (1 / 2 : ℝ) *
          (Real.log (2 * R + 2) + (E : ℝ)) := by ring
  have hreal : (X.card : ℝ) ≤
      ((finitePointsOnRationalLinearCurveComponents J X).card : ℝ) +
        (nonlinearUnion.card : ℝ) := by
    exact_mod_cast hcardCover
  exact hreal.trans (add_le_add (le_refl _) hnonlinearCard)

/-- The effective affine-curve theorem after dividing a common congruence
class by its positive modulus. The resulting box height is
`2 * R / q + 2`. -/
theorem exists_uniform_rationalAffineCurveComponents_effectiveCount_centered_progression
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
          ∀ (q : ℕ), 0 < q →
            ∀ (residueBase : IntVector N),
              (∀ z ∈ X, IntVectorCongruent q z residueBase) →
          ∀ (center : RealVector N) (R : ℝ), 0 ≤ R →
            (∀ z ∈ X, ∀ i, |(z i : ℝ) - center i| ≤ R) →
            (X.card : ℝ) ≤
              ((finitePointsOnRationalLinearCurveComponents J X).card : ℝ) +
                c * (E : ℝ) ^ (4 : ℕ) *
                  (2 * R / (q : ℝ) + 2) ^ (1 / 2 : ℝ) *
                  (Real.log (2 * R / (q : ℝ) + 2) + (E : ℝ)) := by
  classical
  obtain ⟨c, hc, hcurve⟩ := cDHNV2025_curve_halfPower hCurve hN
  refine ⟨c, hc, ?_⟩
  intro E J degree hcomponents hmass X hXzero q hq residueBase hXcong
    center R hR hXbox
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
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hdiv : 0 ≤ 2 * R / (q : ℝ) :=
    div_nonneg (mul_nonneg (by norm_num) hR) hqR.le
  have hheight : 1 < 2 * R / (q : ℝ) + 2 := by linarith
  have hhalf : 0 ≤ (2 * R / (q : ℝ) + 2) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (by linarith) _
  have hlog : 0 ≤ Real.log (2 * R / (q : ℝ) + 2) :=
    Real.log_nonneg hheight.le
  have hnonlinearCard : (nonlinearUnion.card : ℝ) ≤
      c * (E : ℝ) ^ (4 : ℕ) * (2 * R / (q : ℝ) + 2) ^ (1 / 2 : ℝ) *
        (Real.log (2 * R / (q : ℝ) + 2) + (E : ℝ)) := by
    have hnat : nonlinearUnion.card ≤
        ∑ Q ∈ nonlinearRationalAffineComponents J,
          (finitePointsOnRationalAffineIdeal X Q).card := by
      exact Finset.card_biUnion_le
    have hsum :
        (∑ Q ∈ nonlinearRationalAffineComponents J,
          ((finitePointsOnRationalAffineIdeal X Q).card : ℝ)) ≤
        ∑ _Q ∈ nonlinearRationalAffineComponents J,
          c * (E : ℝ) ^ (3 : ℕ) *
            (2 * R / (q : ℝ) + 2) ^ (1 / 2 : ℝ) *
            (Real.log (2 * R / (q : ℝ) + 2) + (E : ℝ)) := by
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
      let points := finitePointsOnRationalAffineIdeal X Q
      by_cases hpoints : points.Nonempty
      · let base : IntVector N := Classical.choose hpoints
        have hbase : base ∈ points := Classical.choose_spec hpoints
        let shift : IntVector N → IntVector N :=
          congruenceDisplacementOrZero q base
        let shifted : Finset (IntVector N) := points.image shift
        let Q' := Q.map (affinePolynomialChangeAlgEquiv
          (fun i ↦ (base i : ℚ)) (q : ℚ)
          (by exact_mod_cast hq.ne'))
        have hQdata' : HasAffineHilbertDimensionDegree Q' 1 (degree Q) := by
          exact (hasAffineHilbertDimensionDegree_map_affinePolynomialChange_iff
            Q (fun i ↦ (base i : ℚ)) (q : ℚ)
              (by exact_mod_cast hq.ne') 1 (degree Q)).2 hQdata
        have hbaseX : base ∈ X :=
          (mem_finitePointsOnRationalAffineIdeal_iff X Q base).mp hbase |>.1
        have hpointCongruent : ∀ z ∈ points, IntVectorCongruent q z base := by
          intro z hz
          have hzX :=
            (mem_finitePointsOnRationalAffineIdeal_iff X Q z).mp hz |>.1
          intro i
          exact (hXcong z hzX i).trans (hXcong base hbaseX i).symm
        have hshiftInjective : Set.InjOn shift (↑points : Set (IntVector N)) := by
          apply (congruenceDisplacementOrZero_injOn base).mono
          intro z hz
          exact hpointCongruent z hz
        have hshiftedCard : shifted.card = points.card := by
          exact Finset.card_image_iff.mpr hshiftInjective
        have hsubset : shifted ⊆ rationalPilaIntegralPoints Q'
            (2 * R / (q : ℝ) + 2) := by
          intro w hw
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
          have hzspec :=
            (mem_finitePointsOnRationalAffineIdeal_iff X Q z).mp hz
          exact intPoint_mem_rationalPilaIntegralPoints_of_mem_zeroLocus
            Q' (2 * R / (q : ℝ) + 2) (shift z)
            (by
              intro i
              have hbound := congruenceDisplacementOrZero_coordinate_bound
                hq base z (hpointCongruent z hz)
                  (hXbox z hzspec.1) (hXbox base hbaseX) i
              dsimp only [shift]
              linarith)
            (by
              dsimp only [Q', shift]
              exact congruenceDisplacement_mem_rationalAffineChange_zeroLocus
                hq Q base z (hpointCongruent z hz) hzspec.2)
        have hsource := hcurve (degree Q) hd Q' hQdata' (2 * R / (q : ℝ) + 2) hheight
        have hdegreeCast : (degree Q : ℝ) ≤ (E : ℝ) := by
          exact_mod_cast hdE
        have hdegreePow : (degree Q : ℝ) ^ (3 : ℕ) ≤
            (E : ℝ) ^ (3 : ℕ) := by
          exact pow_le_pow_left₀ (by positivity) hdegreeCast 3
        have hlogDegree : Real.log (2 * R / (q : ℝ) + 2) + (degree Q : ℝ) ≤
            Real.log (2 * R / (q : ℝ) + 2) + (E : ℝ) :=
          add_le_add_right hdegreeCast _
        calc
          (points.card : ℝ) = (shifted.card : ℝ) := by rw [hshiftedCard]
          _ ≤ ((rationalPilaIntegralPoints Q' (2 * R / (q : ℝ) + 2)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsubset
          _ ≤ c * (degree Q : ℝ) ^ (3 : ℕ) *
                (2 * R / (q : ℝ) + 2) ^ (1 / 2 : ℝ) *
                (Real.log (2 * R / (q : ℝ) + 2) + (degree Q : ℝ)) := hsource
          _ ≤ c * (E : ℝ) ^ (3 : ℕ) *
                (2 * R / (q : ℝ) + 2) ^ (1 / 2 : ℝ) *
                (Real.log (2 * R / (q : ℝ) + 2) + (E : ℝ)) := by
            exact mul_le_mul
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hdegreePow hc.le) hhalf)
              hlogDegree (by positivity)
              (mul_nonneg (mul_nonneg hc.le (by positivity)) hhalf)
      · have hempty : points = ∅ := Finset.not_nonempty_iff_eq_empty.mp hpoints
        simp only [points, hempty, Finset.card_empty, Nat.cast_zero]
        positivity
    have hcardCast :
        ((nonlinearRationalAffineComponents J).card : ℝ) ≤ (E : ℝ) := by
      exact_mod_cast hcomponentCard
    have hcommonNonneg : 0 ≤
        c * (E : ℝ) ^ (3 : ℕ) * (2 * R / (q : ℝ) + 2) ^ (1 / 2 : ℝ) *
          (Real.log (2 * R / (q : ℝ) + 2) + (E : ℝ)) := by positivity
    calc
      (nonlinearUnion.card : ℝ) ≤
          ∑ Q ∈ nonlinearRationalAffineComponents J,
            ((finitePointsOnRationalAffineIdeal X Q).card : ℝ) := by
        exact_mod_cast hnat
      _ ≤ ∑ _Q ∈ nonlinearRationalAffineComponents J,
          c * (E : ℝ) ^ (3 : ℕ) * (2 * R / (q : ℝ) + 2) ^ (1 / 2 : ℝ) *
            (Real.log (2 * R / (q : ℝ) + 2) + (E : ℝ)) := hsum
      _ = ((nonlinearRationalAffineComponents J).card : ℝ) *
          (c * (E : ℝ) ^ (3 : ℕ) * (2 * R / (q : ℝ) + 2) ^ (1 / 2 : ℝ) *
            (Real.log (2 * R / (q : ℝ) + 2) + (E : ℝ))) := by simp
      _ ≤ (E : ℝ) *
          (c * (E : ℝ) ^ (3 : ℕ) * (2 * R / (q : ℝ) + 2) ^ (1 / 2 : ℝ) *
            (Real.log (2 * R / (q : ℝ) + 2) + (E : ℝ))) :=
        mul_le_mul_of_nonneg_right hcardCast hcommonNonneg
      _ = c * (E : ℝ) ^ (4 : ℕ) * (2 * R / (q : ℝ) + 2) ^ (1 / 2 : ℝ) *
          (Real.log (2 * R / (q : ℝ) + 2) + (E : ℝ)) := by ring
  have hreal : (X.card : ℝ) ≤
      ((finitePointsOnRationalLinearCurveComponents J X).card : ℝ) +
        (nonlinearUnion.card : ℝ) := by
    exact_mod_cast hcardCover
  exact hreal.trans (add_le_add (le_refl _) hnonlinearCard)


/-- Degree-effective counting for a proper rational surface section in an
arbitrary translated box. -/
theorem exists_uniform_projectiveSurface_rationalAffineSection_effectiveCount_centered
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
          ∀ (center : RealVector N) (R : ℝ), 0 ≤ R →
            (∀ z ∈ X, ∀ i, |(z i : ℝ) - center i| ≤ R) →
            (X.card : ℝ) ≤
              ((finitePointsOnRationalLinearCurveComponents
                (rationalAffineChartIntersectionIdeal I G) X).card : ℝ) +
                c * (d * a : ℕ) ^ (4 : ℕ) *
                  (2 * R + 2) ^ (1 / 2 : ℝ) *
                  (Real.log (2 * R + 2) + (d * a : ℕ)) := by
  classical
  obtain ⟨c, hc, hcount⟩ :=
    exists_uniform_rationalAffineCurveComponents_effectiveCount_centered
      hCurve hN
  refine ⟨c, hc, ?_⟩
  intro d a I G hIprime hIhom hIprojective hGhom hGnot X hXI hXG
    center R hR hbox
  obtain ⟨degree, hcomponents, hmass⟩ :=
    projectiveSurface_rationalAffineSection_degreeMass
      I G hIprime hIhom hIprojective hGhom hGnot
  have hXchart : ∀ z ∈ X, (fun i ↦ (z i : ℚ)) ∈
      affineIdealZeroLocus (rationalAffineChartIntersectionIdeal I G) := by
    intro z hz
    exact intPoint_mem_rationalAffineChartIntersectionIdeal
      I G z (hXI z hz) (hXG z hz)
  exact hcount (d * a) (rationalAffineChartIntersectionIdeal I G)
    degree hcomponents hmass X hXchart center R hR hbox

/-- Degree-effective counting for a proper rational surface section after
dividing a common congruence class by its positive modulus. -/
theorem exists_uniform_projectiveSurface_rationalAffineSection_effectiveCount_centered_progression
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
          ∀ (q : ℕ), 0 < q →
            ∀ (residueBase : IntVector N),
              (∀ z ∈ X, IntVectorCongruent q z residueBase) →
          ∀ (center : RealVector N) (R : ℝ), 0 ≤ R →
            (∀ z ∈ X, ∀ i, |(z i : ℝ) - center i| ≤ R) →
            (X.card : ℝ) ≤
              ((finitePointsOnRationalLinearCurveComponents
                (rationalAffineChartIntersectionIdeal I G) X).card : ℝ) +
                c * (d * a : ℕ) ^ (4 : ℕ) *
                  (2 * R / (q : ℝ) + 2) ^ (1 / 2 : ℝ) *
                  (Real.log (2 * R / (q : ℝ) + 2) + (d * a : ℕ)) := by
  classical
  obtain ⟨c, hc, hcount⟩ :=
    exists_uniform_rationalAffineCurveComponents_effectiveCount_centered_progression
      hCurve hN
  refine ⟨c, hc, ?_⟩
  intro d a I G hIprime hIhom hIprojective hGhom hGnot X hXI hXG
    q hq residueBase hXcong center R hR hbox
  obtain ⟨degree, hcomponents, hmass⟩ :=
    projectiveSurface_rationalAffineSection_degreeMass
      I G hIprime hIhom hIprojective hGhom hGnot
  have hXchart : ∀ z ∈ X, (fun i ↦ (z i : ℚ)) ∈
      affineIdealZeroLocus (rationalAffineChartIntersectionIdeal I G) := by
    intro z hz
    exact intPoint_mem_rationalAffineChartIntersectionIdeal
      I G z (hXI z hz) (hXG z hz)
  exact hcount (d * a) (rationalAffineChartIntersectionIdeal I G)
    degree hcomponents hmass X hXchart q hq residueBase hXcong
      center R hR hbox

end

end TranslatedDepthSeven
