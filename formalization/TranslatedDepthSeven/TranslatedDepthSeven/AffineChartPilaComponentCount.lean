import TranslatedDepthSeven.FiniteEquationMinimalComponents
import TranslatedDepthSeven.PublishedCountingApplications
import TranslatedDepthSeven.PilaSubpower

/-!
# Pila counting on the actual affine-chart components of an intersection

This file contains the purely algebraic and combinatorial step used after
Salberger's auxiliary form has been constructed.  We set the distinguished
projective coordinate equal to one, take the actual finite list of minimal
prime ideals of the resulting real affine ideal, and cover a literal finite
set of integral points by those components.  Pila's theorem is applied only
to the components whose exact affine dimension and degree have been supplied.

No component-count, degree, or dimension assertion is assumed through a
packaged interface.  The final inequality displays the actual number of
nonlinear minimal components and leaves the points on degree-one components
as a separate literal finite set.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

/-- Setting the zeroth homogeneous coordinate equal to one, over an
arbitrary coefficient ring. -/
def standardDehomogenizationHom (K : Type*) [CommRing K] (N : ℕ) :
    MvPolynomial (Fin (N + 1)) K →+* MvPolynomial (Fin N) K :=
  (MvPolynomial.aeval (Fin.cases 1 fun i ↦ MvPolynomial.X i)).toRingHom

/-- Evaluation after setting `X₀=1` is evaluation at the literal affine
chart vector `(1,z)`. -/
theorem eval_standardDehomogenizationHom
    {K : Type*} [CommRing K] {N : ℕ}
    (z : Fin N → K) (f : MvPolynomial (Fin (N + 1)) K) :
    MvPolynomial.eval z (standardDehomogenizationHom K N f) =
      MvPolynomial.eval (Fin.cases 1 z) f := by
  change (MvPolynomial.eval z).comp (standardDehomogenizationHom K N) f =
    MvPolynomial.eval (Fin.cases 1 z) f
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [standardDehomogenizationHom]
  · intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [standardDehomogenizationHom]
    · simp [standardDehomogenizationHom]

/-- The real affine-chart ideal of the projective intersection `I ∩ V(G)`.
It is defined by the literal operations: extend coefficients to `ℝ`, add
`G`, and set `X₀=1`. -/
def realAffineChartIntersectionIdeal {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (G : MvPolynomial (Fin (N + 1)) ℚ) :
    Ideal (MvPolynomial (Fin N) ℝ) :=
  ((I ⊔ Ideal.span {G}).map
      (MvPolynomial.map (algebraMap ℚ ℝ))).map
    (standardDehomogenizationHom ℝ N)

private theorem eval_map_rat_real {σ : Type*}
    (f : MvPolynomial σ ℚ) (x : σ → ℚ) :
    MvPolynomial.eval (fun i ↦ algebraMap ℚ ℝ (x i))
        (MvPolynomial.map (algebraMap ℚ ℝ) f) =
      algebraMap ℚ ℝ (MvPolynomial.eval x f) := by
  rw [← MvPolynomial.eval₂_eq_eval_map]
  simpa [MvPolynomial.eval₂_id] using
    (MvPolynomial.eval₂_comp_left (algebraMap ℚ ℝ)
      (RingHom.id ℚ) x f).symm

/-- A rational affine point on `I` and on `G` belongs to the real affine
zero locus of the literal chart intersection ideal. -/
theorem intPoint_mem_realAffineChartIntersectionIdeal
    {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (G : MvPolynomial (Fin (N + 1)) ℚ)
    (z : IntVector N)
    (hI : ∀ f ∈ I,
      MvPolynomial.eval
        (fun i ↦ ((Fin.cases (1 : ℤ) z i : ℤ) : ℚ)) f = 0)
    (hG : MvPolynomial.eval
      (fun i ↦ ((Fin.cases (1 : ℤ) z i : ℤ) : ℚ)) G = 0) :
    (fun i ↦ (z i : ℝ)) ∈
      affineIdealZeroLocus (realAffineChartIntersectionIdeal I G) := by
  rw [mem_affineIdealZeroLocus_iff]
  change realAffineChartIntersectionIdeal I G ≤
    RingHom.ker (MvPolynomial.eval (fun i ↦ (z i : ℝ)))
  rw [realAffineChartIntersectionIdeal, Ideal.map_le_iff_le_comap,
    Ideal.map_le_iff_le_comap]
  apply sup_le
  · intro f hf
    change MvPolynomial.eval (fun i ↦ (z i : ℝ))
      (standardDehomogenizationHom ℝ N
        (MvPolynomial.map (algebraMap ℚ ℝ) f)) = 0
    rw [eval_standardDehomogenizationHom]
    let x : Fin (N + 1) → ℚ :=
      fun i ↦ ((Fin.cases (1 : ℤ) z i : ℤ) : ℚ)
    have hx : (fun i : Fin (N + 1) ↦
        Fin.cases (1 : ℝ) (fun j ↦ (z j : ℝ)) i) =
        fun i ↦ algebraMap ℚ ℝ (x i) := by
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [x]
    rw [hx, eval_map_rat_real f x, hI f hf, map_zero]
  · rw [Ideal.span_le]
    intro f hf
    simp only [Set.mem_singleton_iff] at hf
    subst f
    change MvPolynomial.eval (fun i ↦ (z i : ℝ))
      (standardDehomogenizationHom ℝ N
        (MvPolynomial.map (algebraMap ℚ ℝ) G)) = 0
    rw [eval_standardDehomogenizationHom]
    let x : Fin (N + 1) → ℚ :=
      fun i ↦ ((Fin.cases (1 : ℤ) z i : ℤ) : ℚ)
    have hx : (fun i : Fin (N + 1) ↦
        Fin.cases (1 : ℝ) (fun j ↦ (z j : ℝ)) i) =
        fun i ↦ algebraMap ℚ ℝ (x i) := by
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [x]
    rw [hx, eval_map_rat_real G x, hG, map_zero]

/-- The members of a finite integral point set which vanish on an actual
real affine ideal. -/
def finitePointsOnAffineIdeal {N : ℕ}
    (X : Finset (IntVector N))
    (Q : Ideal (MvPolynomial (Fin N) ℝ)) : Finset (IntVector N) := by
  classical
  exact X.filter fun z ↦
    (fun i ↦ (z i : ℝ)) ∈ affineIdealZeroLocus Q

@[simp]
theorem mem_finitePointsOnAffineIdeal_iff {N : ℕ}
    (X : Finset (IntVector N))
    (Q : Ideal (MvPolynomial (Fin N) ℝ)) (z : IntVector N) :
    z ∈ finitePointsOnAffineIdeal X Q ↔
      z ∈ X ∧ (fun i ↦ (z i : ℝ)) ∈ affineIdealZeroLocus Q := by
  classical
  simp [finitePointsOnAffineIdeal]

/-- The literal subset of `X` lying on at least one degree-one affine curve
component of `J`. -/
def finitePointsOnLinearCurveComponents {N : ℕ}
    (J : Ideal (MvPolynomial (Fin N) ℝ))
    (X : Finset (IntVector N)) : Finset (IntVector N) := by
  classical
  exact (finiteMinimalPrimes J).biUnion fun Q ↦
    if Published.HasAffineHilbertDimensionDegree Q 1 1 then
      finitePointsOnAffineIdeal X Q
    else ∅

/-- The actual minimal components not certified to be degree-one curves. -/
def nonlinearAffineComponents {N : ℕ}
    (J : Ideal (MvPolynomial (Fin N) ℝ)) :
    Finset (Ideal (MvPolynomial (Fin N) ℝ)) := by
  classical
  exact (finiteMinimalPrimes J).filter fun Q ↦
    ¬ Published.HasAffineHilbertDimensionDegree Q 1 1

/-- A coefficient-uniform Pila constant valid simultaneously for all affine
curves of degrees `2,…,D` in a fixed ambient affine space. -/
private theorem pila1995_curve_halfPower_oneDegree
    (hPila : Published.Pila1995TheoremA)
    (N d : ℕ) (hd : 2 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (I : Ideal (MvPolynomial (Fin N) ℝ)),
        Published.HasAffineHilbertDimensionDegree I 1 d →
        ∀ U : ℝ, 1 < U →
          ((Published.pilaIntegralPoints I U).card : ℝ) ≤
            C * U ^ ((1 / 2 : ℝ) + ε) := by
  obtain ⟨c, hc, hsource⟩ := hPila 1 d N (by omega)
  let C : ℝ := c * pilaConstant d ε
  have hconstant : 0 < pilaConstant d ε := by
    unfold pilaConstant
    positivity
  refine ⟨C, mul_pos hc hconstant, ?_⟩
  intro I hI U hU
  have hprinted := hsource I hI U hU
  have habsorb := pilaCurvePower_mul_factor_le_const_mul_rpow
    hd hε hU.le
  calc
    ((Published.pilaIntegralPoints I U).card : ℝ) ≤
        c * U ^ ((d : ℝ)⁻¹) * pilaFactor d U := by
      simpa [pilaFactor] using hprinted
    _ = c * (U ^ ((d : ℝ)⁻¹) * pilaFactor d U) := by ring
    _ ≤ c * (pilaConstant d ε * U ^ ((1 / 2 : ℝ) + ε)) := by
      exact mul_le_mul_of_nonneg_left habsorb hc.le
    _ = C * U ^ ((1 / 2 : ℝ) + ε) := by
      simp only [C]
      ring

theorem pila1995_curve_halfPower_boundedDegree
    (hPila : Published.Pila1995TheoremA)
    (N D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ), 2 ≤ d → d ≤ D →
        ∀ (I : Ideal (MvPolynomial (Fin N) ℝ)),
          Published.HasAffineHilbertDimensionDegree I 1 d →
          ∀ U : ℝ, 1 < U →
            ((Published.pilaIntegralPoints I U).card : ℝ) ≤
              C * U ^ ((1 / 2 : ℝ) + ε) := by
  let S : Finset ℕ := Finset.Icc 2 D
  let E := {d : ℕ // d ∈ S}
  have heach : ∀ d : E, ∃ C : ℝ, 0 < C ∧
      ∀ (I : Ideal (MvPolynomial (Fin N) ℝ)),
        Published.HasAffineHilbertDimensionDegree I 1 d.1 →
        ∀ U : ℝ, 1 < U →
          ((Published.pilaIntegralPoints I U).card : ℝ) ≤
            C * U ^ ((1 / 2 : ℝ) + ε) := by
    intro d
    have hd : 2 ≤ d.1 := (Finset.mem_Icc.mp d.2).1
    exact pila1995_curve_halfPower_oneDegree hPila N d.1 hd ε hε
  choose c hc hbound using heach
  let C : ℝ := 1 + ∑ d : E, c d
  have hC : 0 < C := by
    dsimp only [C]
    have : 0 ≤ ∑ d : E, c d :=
      Finset.sum_nonneg fun d _ ↦ (hc d).le
    linarith
  refine ⟨C, hC, ?_⟩
  intro d hd hdD I hI U hU
  have hdmem : d ∈ S := Finset.mem_Icc.mpr ⟨hd, hdD⟩
  let e : E := ⟨d, hdmem⟩
  have hsource := hbound e I (by simpa [e] using hI) U hU
  have hcle : c e ≤ C := by
    dsimp only [C]
    have hterm : c e ≤ ∑ a : E, c a := by
      exact Finset.single_le_sum
        (fun a _ ↦ (hc a).le) (Finset.mem_univ e)
    linarith
  exact hsource.trans (mul_le_mul_of_nonneg_right hcle (by positivity))

/-- An integral vector with strict coordinate bound `U` is a member of
Pila's literal point set as soon as its real point vanishes on the ideal. -/
theorem intPoint_mem_pilaIntegralPoints_of_mem_zeroLocus
    {N : ℕ} (Q : Ideal (MvPolynomial (Fin N) ℝ))
    (U : ℝ) (z : IntVector N)
    (hbox : ∀ i, |(z i : ℝ)| < U)
    (hzero : (fun i ↦ (z i : ℝ)) ∈ affineIdealZeroLocus Q) :
    z ∈ Published.pilaIntegralPoints Q U := by
  classical
  rw [Published.pilaIntegralPoints, Finset.mem_filter]
  refine ⟨?_, hbox, hzero⟩
  rw [mem_integerSupNormBox_iff]
  intro i
  have hceil : U ≤ (⌈U⌉₊ : ℝ) := Nat.le_ceil U
  have habs : ((z i).natAbs : ℝ) ≤ (⌈U⌉₊ : ℝ) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using
      (le_of_lt (hbox i)).trans hceil
  exact_mod_cast habs

/-- Concrete componentwise terminal estimate.  Every actual minimal prime
of `J` is required either to be a degree-one affine curve or to have one
displayed degree in `2,…,D`.  The degree-one contribution remains a literal
finite set; the nonlinear contribution is bounded uniformly by Pila and the
actual number of nonlinear minimal primes. -/
theorem finiteSet_card_le_linearComponents_add_pilaCurveComponents
    (hPila : Published.Pila1995TheoremA)
    {N D : ℕ} (ε : ℝ) (hε : 0 < ε)
    (J : Ideal (MvPolynomial (Fin N) ℝ))
    (hcomponents : ∀ Q ∈ finiteMinimalPrimes J,
      Published.HasAffineHilbertDimensionDegree Q 1 1 ∨
        ∃ d : ℕ, 2 ≤ d ∧ d ≤ D ∧
          Published.HasAffineHilbertDimensionDegree Q 1 d)
    (X : Finset (IntVector N))
    (hXzero : ∀ z ∈ X,
      (fun i ↦ (z i : ℝ)) ∈ affineIdealZeroLocus J)
    (U : ℝ) (hU : 1 < U)
    (hXbox : ∀ z ∈ X, ∀ i, |(z i : ℝ)| < U) :
    ∃ C : ℝ, 0 < C ∧
      (X.card : ℝ) ≤
        ((finitePointsOnLinearCurveComponents J X).card : ℝ) +
          ((nonlinearAffineComponents J).card : ℝ) *
            C * U ^ ((1 / 2 : ℝ) + ε) := by
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
    by_cases hlinear : Published.HasAffineHilbertDimensionDegree Q 1 1
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
      ((nonlinearAffineComponents J).card : ℝ) *
        C * U ^ ((1 / 2 : ℝ) + ε) := by
    have hnat : nonlinearUnion.card ≤
        ∑ Q ∈ nonlinearAffineComponents J,
          (finitePointsOnAffineIdeal X Q).card := by
      exact Finset.card_biUnion_le
    have hsum :
        (∑ Q ∈ nonlinearAffineComponents J,
          ((finitePointsOnAffineIdeal X Q).card : ℝ)) ≤
        ∑ _Q ∈ nonlinearAffineComponents J,
          C * U ^ ((1 / 2 : ℝ) + ε) := by
      apply Finset.sum_le_sum
      intro Q hQ
      have hQmin : Q ∈ finiteMinimalPrimes J := (Finset.mem_filter.mp hQ).1
      have hQnot : ¬ Published.HasAffineHilbertDimensionDegree Q 1 1 :=
        (Finset.mem_filter.mp hQ).2
      rcases hcomponents Q hQmin with hlinear | ⟨d, hd, hdD, hQdim⟩
      · exact False.elim (hQnot hlinear)
      · have hsubset : finitePointsOnAffineIdeal X Q ⊆
            Published.pilaIntegralPoints Q U := by
          intro z hz
          have hzspec := (mem_finitePointsOnAffineIdeal_iff X Q z).mp hz
          exact intPoint_mem_pilaIntegralPoints_of_mem_zeroLocus
            Q U z (hXbox z hzspec.1) hzspec.2
        calc
          ((finitePointsOnAffineIdeal X Q).card : ℝ) ≤
              ((Published.pilaIntegralPoints Q U).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsubset
          _ ≤ C * U ^ ((1 / 2 : ℝ) + ε) :=
            hPilaBound d hd hdD Q hQdim U hU
    calc
      (nonlinearUnion.card : ℝ) ≤
          (∑ Q ∈ nonlinearAffineComponents J,
            ((finitePointsOnAffineIdeal X Q).card : ℝ)) := by
        exact_mod_cast hnat
      _ ≤ ∑ _Q ∈ nonlinearAffineComponents J,
          C * U ^ ((1 / 2 : ℝ) + ε) := hsum
      _ = ((nonlinearAffineComponents J).card : ℝ) *
          C * U ^ ((1 / 2 : ℝ) + ε) := by
        simp [mul_assoc]
  refine ⟨C, hC, ?_⟩
  have hreal : (X.card : ℝ) ≤
      ((finitePointsOnLinearCurveComponents J X).card : ℝ) +
        (nonlinearUnion.card : ℝ) := by exact_mod_cast hcardCover
  exact hreal.trans (add_le_add_right hnonlinearCard _)

end

end TranslatedDepthSeven
