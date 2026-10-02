import TranslatedDepthSeven.ResiduePacketPilaComponentCount

/-!
# Pila after residue rescaling for points and curves

The literal intersections arising at node, edge, and auxiliary-form
frontiers can have zero-dimensional minimal components as well as curve
components.  This file gives the componentwise residue-packet estimate in
that exact generality.  Only affine curves of Hilbert dimension and degree
`(1,1)` are retained as linear components.  Every zero-dimensional component
and every nonlinear curve is estimated directly from Pila's theorem after
the affine change `z = base + q w`.

No point-counting estimate is included among the hypotheses.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

set_option maxHeartbeats 2000000

/-- Pila's theorem gives the required half-power estimate for a
zero-dimensional affine scheme of one fixed positive degree. -/
private theorem pila1995_zeroDim_halfPower_oneDegree
    (hPila : Pila1995TheoremA)
    (N d : ℕ) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (I : Ideal (MvPolynomial (Fin N) ℝ)),
        HasAffineHilbertDimensionDegree I 0 d →
        ∀ U : ℝ, 1 < U →
          ((pilaIntegralPoints I U).card : ℝ) ≤
            C * U ^ ((1 / 2 : ℝ) + ε) := by
  obtain ⟨c, hc, hsource⟩ := hPila 0 d N hd
  let C : ℝ := c * pilaConstant d ε
  have hconstant : 0 < pilaConstant d ε := by
    unfold pilaConstant
    positivity
  refine ⟨C, mul_pos hc hconstant, ?_⟩
  intro I hI U hU
  have hprinted := hsource I hI U hU
  have hfactor := pilaFactor_le_const_mul_rpow
    (d := (d : ℝ)) (ε := ε) (H := U) (by positivity) hε hU.le
  have hdReal : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hinv : (d : ℝ)⁻¹ ≤ 1 := by
    exact (inv_le_one₀ (by positivity : (0 : ℝ) < d)).2 hdReal
  have hexponent :
      (0 : ℝ) - 1 + (d : ℝ)⁻¹ ≤ (1 / 2 : ℝ) := by
    linarith
  have hmain :
      U ^ ((0 : ℝ) - 1 + (d : ℝ)⁻¹) ≤ U ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hU.le hexponent
  have hproduct :
      U ^ ((0 : ℝ) - 1 + (d : ℝ)⁻¹) * pilaFactor d U ≤
        U ^ (1 / 2 : ℝ) * (pilaConstant d ε * U ^ ε) := by
    exact mul_le_mul hmain hfactor
      (by unfold pilaFactor; positivity) (by positivity)
  calc
    ((pilaIntegralPoints I U).card : ℝ) ≤
        c * U ^ ((0 : ℝ) - 1 + (d : ℝ)⁻¹) * pilaFactor d U := by
      simpa [pilaFactor] using hprinted
    _ = c *
        (U ^ ((0 : ℝ) - 1 + (d : ℝ)⁻¹) * pilaFactor d U) := by
      ring
    _ ≤ c * (U ^ (1 / 2 : ℝ) *
        (pilaConstant d ε * U ^ ε)) := by
      exact mul_le_mul_of_nonneg_left hproduct hc.le
    _ = C * U ^ ((1 / 2 : ℝ) + ε) := by
      rw [Real.rpow_add (by positivity : 0 < U)]
      simp only [C]
      ring

/-- One coefficient-uniform constant for all zero-dimensional affine
schemes of positive degree at most `D`. -/
private theorem pila1995_zeroDim_halfPower_boundedDegree
    (hPila : Pila1995TheoremA)
    (N D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ), 1 ≤ d → d ≤ D →
        ∀ (I : Ideal (MvPolynomial (Fin N) ℝ)),
          HasAffineHilbertDimensionDegree I 0 d →
          ∀ U : ℝ, 1 < U →
            ((pilaIntegralPoints I U).card : ℝ) ≤
              C * U ^ ((1 / 2 : ℝ) + ε) := by
  let S : Finset ℕ := Finset.Icc 1 D
  let E := {d : ℕ // d ∈ S}
  have heach : ∀ d : E, ∃ C : ℝ, 0 < C ∧
      ∀ (I : Ideal (MvPolynomial (Fin N) ℝ)),
        HasAffineHilbertDimensionDegree I 0 d.1 →
        ∀ U : ℝ, 1 < U →
          ((pilaIntegralPoints I U).card : ℝ) ≤
            C * U ^ ((1 / 2 : ℝ) + ε) := by
    intro d
    exact pila1995_zeroDim_halfPower_oneDegree hPila N d.1
      (Finset.mem_Icc.mp d.2).1 ε hε
  choose c hc hbound using heach
  let C : ℝ := 1 + ∑ d : E, c d
  have hC : 0 < C := by
    dsimp only [C]
    have hsum : 0 ≤ ∑ d : E, c d :=
      Finset.sum_nonneg fun d _ ↦ (hc d).le
    linarith
  refine ⟨C, hC, ?_⟩
  intro d hd hdD I hI U hU
  have hdmem : d ∈ S := Finset.mem_Icc.mpr ⟨hd, hdD⟩
  let e : E := ⟨d, hdmem⟩
  have hsource := hbound e I (by simpa [e] using hI) U hU
  have hterm : c e ≤ ∑ a : E, c a := by
    exact Finset.single_le_sum
      (fun a _ ↦ (hc a).le) (Finset.mem_univ e)
  have hcle : c e ≤ C := by
    dsimp only [C]
    linarith
  exact hsource.trans
    (mul_le_mul_of_nonneg_right hcle (Real.rpow_nonneg (by positivity) _))

/-- One coefficient-uniform constant for the direct componentwise
residue-packet estimate, simultaneously for every modulus, base point,
ideal, and finite packet whose actual affine minimal components have
dimension zero or one and degree at most `D`.  The only untreated part is
the literal union of the `(dimension,degree) = (1,1)` components. -/
theorem exists_uniform_pilaDimZeroOrNonlinearCurveComponents_rescaled_constant
    (hPila : Pila1995TheoremA)
    (N D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {q : ℕ}, 0 < q →
        ∀ (base : IntVector N)
          (J : Ideal (MvPolynomial (Fin N) ℝ)),
        (∀ Q ∈ finiteMinimalPrimes J,
          ∃ n d : ℕ, n ≤ 1 ∧ 1 ≤ d ∧ d ≤ D ∧
            HasAffineHilbertDimensionDegree Q n d) →
        ∀ (X : Finset (IntVector N)),
        (∀ z ∈ X,
          (fun i ↦ (z i : ℝ)) ∈ affineIdealZeroLocus J) →
        (∀ z ∈ X, IntVectorCongruent q z base) →
        ∀ U : ℝ, 1 < U →
        (∀ z ∈ X, ∀ i,
          |(congruenceDisplacementOrZero q base z i : ℝ)| < U) →
        (X.card : ℝ) ≤
          ((finitePointsOnLinearCurveComponents J X).card : ℝ) +
            ((nonlinearAffineComponents J).card : ℝ) * C *
              U ^ ((1 / 2 : ℝ) + ε) := by
  classical
  obtain ⟨Czero, hCzero, hZeroBound⟩ :=
    pila1995_zeroDim_halfPower_boundedDegree hPila N D ε hε
  obtain ⟨Ccurve, hCcurve, hCurveBound⟩ :=
    pila1995_curve_halfPower_boundedDegree hPila N D ε hε
  let C : ℝ := Czero + Ccurve
  have hC : 0 < C := add_pos hCzero hCcurve
  refine ⟨C, hC, ?_⟩
  intro q hq base J hcomponents X hXzero hXcong U hU hXquotientBox
  let nonlinearUnion : Finset (IntVector N) :=
    (nonlinearAffineComponents J).biUnion fun Q ↦
      finitePointsOnAffineIdeal X Q
  have hcover : X ⊆ finitePointsOnLinearCurveComponents J X ∪
      nonlinearUnion := by
    intro z hz
    let T : Ideal (MvPolynomial (Fin N) ℝ) :=
      RingHom.ker (MvPolynomial.eval (fun i ↦ (z i : ℝ)))
    letI : T.IsPrime := RingHom.ker_isPrime _
    have hJT : J ≤ T := by
      intro f hf
      exact RingHom.mem_ker.mpr (hXzero z hz f hf)
    obtain ⟨Q, hQ, hQT⟩ := exists_finiteMinimalPrime_le hJT
    by_cases hlinear : HasAffineHilbertDimensionDegree Q 1 1
    · apply Finset.mem_union_left
      rw [finitePointsOnLinearCurveComponents]
      refine Finset.mem_biUnion.mpr ⟨Q, hQ, ?_⟩
      simp only [if_pos hlinear]
      exact (mem_finitePointsOnAffineIdeal_iff X Q z).mpr
        ⟨hz, fun f hf ↦ RingHom.mem_ker.mp (hQT hf)⟩
    · apply Finset.mem_union_right
      refine Finset.mem_biUnion.mpr ⟨Q, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨hQ, hlinear⟩
      · exact (mem_finitePointsOnAffineIdeal_iff X Q z).mpr
          ⟨hz, fun f hf ↦ RingHom.mem_ker.mp (hQT hf)⟩
  have hcardCover : X.card ≤
      (finitePointsOnLinearCurveComponents J X).card + nonlinearUnion.card :=
    calc
      X.card ≤
          (finitePointsOnLinearCurveComponents J X ∪ nonlinearUnion).card :=
        Finset.card_le_card hcover
      _ ≤ (finitePointsOnLinearCurveComponents J X).card +
          nonlinearUnion.card := Finset.card_union_le _ _
  have hnonlinearCard : (nonlinearUnion.card : ℝ) ≤
      ((nonlinearAffineComponents J).card : ℝ) * C *
        U ^ ((1 / 2 : ℝ) + ε) := by
    have hnat : nonlinearUnion.card ≤
        ∑ Q ∈ nonlinearAffineComponents J,
          (finitePointsOnAffineIdeal X Q).card := Finset.card_biUnion_le
    have hsum :
        (∑ Q ∈ nonlinearAffineComponents J,
          ((finitePointsOnAffineIdeal X Q).card : ℝ)) ≤
        ∑ _Q ∈ nonlinearAffineComponents J,
          C * U ^ ((1 / 2 : ℝ) + ε) := by
      apply Finset.sum_le_sum
      intro Q hQ
      have hQmin : Q ∈ finiteMinimalPrimes J :=
        (Finset.mem_filter.mp hQ).1
      have hQnot : ¬ HasAffineHilbertDimensionDegree Q 1 1 :=
        (Finset.mem_filter.mp hQ).2
      obtain ⟨n, d, hn, hd, hdD, hQdim⟩ := hcomponents Q hQmin
      let Q' := Q.map (affinePolynomialChangeAlgEquiv
        (fun i ↦ (base i : ℝ)) (q : ℝ)
        (by exact_mod_cast hq.ne'))
      have hQdim' : HasAffineHilbertDimensionDegree Q' n d := by
        exact (hasAffineHilbertDimensionDegree_map_affinePolynomialChange_iff
          Q (fun i ↦ (base i : ℝ)) (q : ℝ)
            (by exact_mod_cast hq.ne') n d).2 hQdim
      have hinjective : Set.InjOn
          (congruenceDisplacementOrZero q base)
          (↑(finitePointsOnAffineIdeal X Q) : Set (IntVector N)) := by
        apply (congruenceDisplacementOrZero_injOn base).mono
        intro z hz
        exact hXcong z
          ((mem_finitePointsOnAffineIdeal_iff X Q z).mp hz).1
      have himage : ∀ z ∈ finitePointsOnAffineIdeal X Q,
          congruenceDisplacementOrZero q base z ∈
            pilaIntegralPoints Q' U := by
        intro z hz
        have hzspec := (mem_finitePointsOnAffineIdeal_iff X Q z).mp hz
        apply intPoint_mem_pilaIntegralPoints_of_mem_zeroLocus
        · exact hXquotientBox z hzspec.1
        · exact congruenceDisplacement_mem_affineChange_zeroLocus
            hq Q base z (hXcong z hzspec.1) hzspec.2
      have hcard : (finitePointsOnAffineIdeal X Q).card ≤
          (pilaIntegralPoints Q' U).card :=
        Finset.card_le_card_of_injOn
          (congruenceDisplacementOrZero q base) himage hinjective
      have hcomponentBound :
          ((pilaIntegralPoints Q' U).card : ℝ) ≤
            C * U ^ ((1 / 2 : ℝ) + ε) := by
        interval_cases n
        · have hzero := hZeroBound d hd hdD Q' hQdim' U hU
          exact hzero.trans <| mul_le_mul_of_nonneg_right
            (show Czero ≤ C by simp [C, hCcurve.le])
            (Real.rpow_nonneg (by positivity) _)
        · have hdTwo : 2 ≤ d := by
            by_contra hdNot
            have hdOne : d = 1 := by omega
            apply hQnot
            simpa [hdOne] using hQdim
          have hcurve := hCurveBound d hdTwo hdD Q'
            (by simpa using hQdim') U hU
          exact hcurve.trans <| mul_le_mul_of_nonneg_right
            (show Ccurve ≤ C by simp [C, hCzero.le])
            (Real.rpow_nonneg (by positivity) _)
      calc
        ((finitePointsOnAffineIdeal X Q).card : ℝ) ≤
            ((pilaIntegralPoints Q' U).card : ℝ) := by
          exact_mod_cast hcard
        _ ≤ C * U ^ ((1 / 2 : ℝ) + ε) := hcomponentBound
    calc
      (nonlinearUnion.card : ℝ) ≤
          (∑ Q ∈ nonlinearAffineComponents J,
            ((finitePointsOnAffineIdeal X Q).card : ℝ)) := by
        exact_mod_cast hnat
      _ ≤ ∑ _Q ∈ nonlinearAffineComponents J,
          C * U ^ ((1 / 2 : ℝ) + ε) := hsum
      _ = ((nonlinearAffineComponents J).card : ℝ) * C *
          U ^ ((1 / 2 : ℝ) + ε) := by simp [mul_assoc]
  have hreal : (X.card : ℝ) ≤
      ((finitePointsOnLinearCurveComponents J X).card : ℝ) +
        (nonlinearUnion.card : ℝ) := by
    exact_mod_cast hcardCover
  exact hreal.trans (add_le_add_right hnonlinearCard _)

/-- Direct specialization of the preceding coefficient-uniform estimate to
one displayed packet. -/
theorem finiteSet_card_le_linearCurveComponents_add_pilaDimZeroOrNonlinearCurveComponents_rescaled
    (hPila : Pila1995TheoremA)
    {N D q : ℕ} (hq : 0 < q) (ε : ℝ) (hε : 0 < ε)
    (base : IntVector N)
    (J : Ideal (MvPolynomial (Fin N) ℝ))
    (hcomponents : ∀ Q ∈ finiteMinimalPrimes J,
      ∃ n d : ℕ, n ≤ 1 ∧ 1 ≤ d ∧ d ≤ D ∧
        HasAffineHilbertDimensionDegree Q n d)
    (X : Finset (IntVector N))
    (hXzero : ∀ z ∈ X,
      (fun i ↦ (z i : ℝ)) ∈ affineIdealZeroLocus J)
    (hXcong : ∀ z ∈ X, IntVectorCongruent q z base)
    (U : ℝ) (hU : 1 < U)
    (hXquotientBox : ∀ z ∈ X, ∀ i,
      |(congruenceDisplacementOrZero q base z i : ℝ)| < U) :
    ∃ C : ℝ, 0 < C ∧
      (X.card : ℝ) ≤
        ((finitePointsOnLinearCurveComponents J X).card : ℝ) +
          ((nonlinearAffineComponents J).card : ℝ) * C *
            U ^ ((1 / 2 : ℝ) + ε) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_pilaDimZeroOrNonlinearCurveComponents_rescaled_constant
      hPila N D ε hε
  exact ⟨C, hC,
    hbound hq base J hcomponents X hXzero hXcong U hU hXquotientBox⟩

end

end TranslatedDepthSeven
