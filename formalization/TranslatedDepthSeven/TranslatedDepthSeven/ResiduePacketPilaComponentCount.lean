import TranslatedDepthSeven.AffineChartPilaComponentCount
import TranslatedDepthSeven.FiniteResiduePacketRescaling
import TranslatedDepthSeven.HilbertAffineChange

/-!
# Pila's curve estimate after dividing a residue packet by its modulus

Salberger's auxiliary form is constructed in the original affine
coordinates, whose side is of order `T`.  The points in one square-free
packet are nevertheless all congruent modulo `q`.  Before applying Pila to
the resulting curves one must make the literal substitution
`z = base + q w`; the new side is of order `T/q`.  This file performs that
substitution and preserves the exact affine Hilbert dimension and degree.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

/-- A zero of a real affine ideal, congruent to `base` modulo a positive
integer `q`, becomes a zero of the literal transformed ideal after division
by `q`. -/
theorem congruenceDisplacement_mem_affineChange_zeroLocus
    {N q : ℕ} (hq : 0 < q)
    (Q : Ideal (MvPolynomial (Fin N) ℝ))
    (base z : IntVector N) (hzcong : IntVectorCongruent q z base)
    (hzQ : (fun i ↦ (z i : ℝ)) ∈ affineIdealZeroLocus Q) :
    (fun i ↦ (congruenceDisplacementOrZero q base z i : ℝ)) ∈
      affineIdealZeroLocus
        (Q.map (affinePolynomialChangeAlgEquiv
          (fun i ↦ (base i : ℝ)) (q : ℝ)
          (by exact_mod_cast hq.ne'))) := by
  change Q.map (affinePolynomialChangeAlgEquiv
      (fun i ↦ (base i : ℝ)) (q : ℝ)
      (by exact_mod_cast hq.ne')) ≤
    RingHom.ker (MvPolynomial.eval
      (fun i ↦ (congruenceDisplacementOrZero q base z i : ℝ)))
  rw [Ideal.map_le_iff_le_comap]
  intro f hf
  rw [Ideal.mem_comap, RingHom.mem_ker]
  change MvPolynomial.aeval
      (fun i ↦ (congruenceDisplacementOrZero q base z i : ℝ))
      (affinePolynomialChangeAlgEquiv
        (fun i ↦ (base i : ℝ)) (q : ℝ)
        (by exact_mod_cast hq.ne') f) = 0
  rw [aeval_affinePolynomialChange]
  have hpoint :
      (fun i ↦ (base i : ℝ) + (q : ℝ) *
        (congruenceDisplacementOrZero q base z i : ℝ)) =
      fun i ↦ (z i : ℝ) := by
    funext i
    exact_mod_cast
      (congruenceDisplacementOrZero_spec base z hzcong i).symm
  rw [hpoint]
  exact hzQ f hf

/-- Componentwise Pila estimate in the divided coordinates.  Linear
components remain visible as a literal finite set, while each nonlinear
component is counted in a box of side `U` in the quotient coordinates. -/
theorem finiteSet_card_le_linearComponents_add_pilaCurveComponents_rescaled
    (hPila : Pila1995TheoremA)
    {N D q : ℕ} (hq : 0 < q) (ε : ℝ) (hε : 0 < ε)
    (base : IntVector N)
    (J : Ideal (MvPolynomial (Fin N) ℝ))
    (hcomponents : ∀ Q ∈ finiteMinimalPrimes J,
      HasAffineHilbertDimensionDegree Q 1 1 ∨
        ∃ d : ℕ, 2 ≤ d ∧ d ≤ D ∧
          HasAffineHilbertDimensionDegree Q 1 d)
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
  classical
  obtain ⟨C, hC, hPilaBound⟩ :=
    pila1995_curve_halfPower_boundedDegree hPila N D ε hε
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
      rcases hcomponents Q hQmin with hlinear | ⟨d, hd, hdD, hQdim⟩
      · exact False.elim (hQnot hlinear)
      · let Q' := Q.map (affinePolynomialChangeAlgEquiv
            (fun i ↦ (base i : ℝ)) (q : ℝ)
            (by exact_mod_cast hq.ne'))
        have hQdim' : HasAffineHilbertDimensionDegree Q' 1 d := by
          exact (hasAffineHilbertDimensionDegree_map_affinePolynomialChange_iff
            Q (fun i ↦ (base i : ℝ)) (q : ℝ)
              (by exact_mod_cast hq.ne') 1 d).2 hQdim
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
        calc
          ((finitePointsOnAffineIdeal X Q).card : ℝ) ≤
              ((pilaIntegralPoints Q' U).card : ℝ) := by
            exact_mod_cast hcard
          _ ≤ C * U ^ ((1 / 2 : ℝ) + ε) :=
            hPilaBound d hd hdD Q' hQdim' U hU
    calc
      (nonlinearUnion.card : ℝ) ≤
          (∑ Q ∈ nonlinearAffineComponents J,
            ((finitePointsOnAffineIdeal X Q).card : ℝ)) := by
        exact_mod_cast hnat
      _ ≤ ∑ _Q ∈ nonlinearAffineComponents J,
          C * U ^ ((1 / 2 : ℝ) + ε) := hsum
      _ = ((nonlinearAffineComponents J).card : ℝ) * C *
          U ^ ((1 / 2 : ℝ) + ε) := by simp [mul_assoc]
  refine ⟨C, hC, ?_⟩
  calc
    (X.card : ℝ) ≤
        (finitePointsOnLinearCurveComponents J X).card +
          nonlinearUnion.card := by exact_mod_cast hcardCover
    _ ≤ (finitePointsOnLinearCurveComponents J X).card +
        ((nonlinearAffineComponents J).card : ℝ) * C *
          U ^ ((1 / 2 : ℝ) + ε) := by gcongr

end

end TranslatedDepthSeven
