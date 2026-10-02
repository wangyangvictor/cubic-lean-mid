import TranslatedDepthSeven.ProjectiveSurfaceAffineHypersurfaceBezout
import TranslatedDepthSeven.ResiduePacketPilaDimensionZeroOrCurve
import TranslatedDepthSeven.SalbergerAffinePacketMembership

/-!
# Counting a proper surface section, with its lines retained

This is the post-intersection step of the determinant method, without any
determinant hypothesis. A homogeneous form not in the source surface ideal
has total affine component-degree mass at most the product of the two
degrees, by projective Bezout. Pila applies to the zero-dimensional and
nonlinear-curve components. The union of points on degree-one curves is
left as an exact finite set for the separate global line argument.

The constant is chosen before the surface, the cutting form, the modulus,
and the point set. Consequently the same statement handles both the
small-equation proper-cut alternative and the pullback of a nonzero image
partial derivative. No special-fibre hypothesis or coefficient height is
needed in either case.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Uniform proper-cut estimate after dividing one integral residue class.
All component bounds are derived from Bezout, not supplied by the caller. -/
theorem exists_uniform_surfaceProperCut_pila_rescaled
    (hPila : Pila1995TheoremA)
    (hBezout : StandardAG.ProjectiveSurfaceAffineHypersurfaceBezout)
    (N D K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d k : ℕ), d ≤ D → k ≤ K →
      ∀ (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
        (G : MvPolynomial (Fin (N + 1)) ℚ),
        I.IsPrime →
        I.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
        MvPolynomial.X (0 : Fin (N + 1)) ∉ I →
        HasProjectiveDimensionDegree I 2 d →
        G.IsHomogeneous k → G ∉ I →
      ∀ (q : ℕ), 0 < q → ∀ (base : IntVector N)
        (X : Finset (IntVector N)),
        (∀ z ∈ X, ∀ f ∈ I, MvPolynomial.eval
          (fun i ↦ (integralAffineChartVector z i : ℚ)) f = 0) →
        (∀ z ∈ X, MvPolynomial.eval
          (fun i ↦ (integralAffineChartVector z i : ℚ)) G = 0) →
        (∀ z ∈ X, IntVectorCongruent q z base) →
      ∀ U : ℝ, 1 < U →
        (∀ z ∈ X, ∀ i,
          |(congruenceDisplacementOrZero q base z i : ℝ)| < U) →
        (X.card : ℝ) ≤
          ((finitePointsOnLinearCurveComponents
            (realAffineChartIntersectionIdeal I G) X).card : ℝ) +
          C * U ^ ((1 / 2 : ℝ) + ε) := by
  classical
  obtain ⟨C₀, hC₀, hPilaUniform⟩ :=
    exists_uniform_pilaDimZeroOrNonlinearCurveComponents_rescaled_constant
      hPila N (D * K) ε hε
  let C : ℝ := 1 + (D * K : ℕ) * C₀
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro d k hd hk I G hIprime hIhomogeneous hIchart hIdegree
    hGhomogeneous hGnot q hq base X hzero hGzero hcong U hU hbox
  let J := realAffineChartIntersectionIdeal I G
  have hdegreeBound : d * k ≤ D * K := Nat.mul_le_mul hd hk
  have hcomponents : ∀ Q ∈ finiteMinimalPrimes J,
      ∃ n e : ℕ, n ≤ 1 ∧ 1 ≤ e ∧ e ≤ D * K ∧
        HasAffineHilbertDimensionDegree Q n e := by
    intro Q hQ
    obtain ⟨n, e, hn, he, hebound, hHilbert⟩ :=
      projectiveSurfaceAffineHypersurface_component_degree_le
        hBezout I G hIprime hIhomogeneous hIchart hIdegree
          hGhomogeneous hGnot Q hQ
    exact ⟨n, e, hn, he, hebound.trans hdegreeBound, hHilbert⟩
  have hXJ : ∀ z ∈ X,
      (fun i ↦ (z i : ℝ)) ∈ affineIdealZeroLocus J := by
    intro z hz
    apply intPoint_mem_realAffineChartIntersectionIdeal
    · simpa only [integralAffineChartVector] using hzero z hz
    · simpa only [integralAffineChartVector] using hGzero z hz
  have hcomponentCount : (nonlinearAffineComponents J).card ≤ D * K := by
    calc
      (nonlinearAffineComponents J).card ≤ (finiteMinimalPrimes J).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤ d * k := projectiveSurfaceAffineHypersurface_componentCount_le
        hBezout I G hIprime hIhomogeneous hIchart hIdegree
          hGhomogeneous hGnot
      _ ≤ D * K := hdegreeBound
  have hcount := hPilaUniform hq base J hcomponents X hXJ hcong U hU hbox
  have hmass : ((nonlinearAffineComponents J).card : ℝ) * C₀ ≤ C := by
    have hcast : ((nonlinearAffineComponents J).card : ℝ) ≤
        ((D * K : ℕ) : ℝ) := by exact_mod_cast hcomponentCount
    have hmul := mul_le_mul_of_nonneg_right hcast hC₀.le
    dsimp only [C]
    linarith
  have hpow : 0 ≤ U ^ ((1 / 2 : ℝ) + ε) :=
    Real.rpow_nonneg (le_trans zero_le_one hU.le) _
  have hstep :
      ((finitePointsOnLinearCurveComponents J X).card : ℝ) +
          ((nonlinearAffineComponents J).card : ℝ) * C₀ *
            U ^ ((1 / 2 : ℝ) + ε) ≤
        ((finitePointsOnLinearCurveComponents J X).card : ℝ) +
          C * U ^ ((1 / 2 : ℝ) + ε) :=
    add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hmass hpow)
  exact hcount.trans hstep

/-- Unscaled form of the preceding estimate. There is no auxiliary-prime
or Salberger input: only the supplied proper section, Bezout and Pila. -/
theorem exists_uniform_surfaceProperCut_pila
    (hPila : Pila1995TheoremA)
    (hBezout : StandardAG.ProjectiveSurfaceAffineHypersurfaceBezout)
    (N D K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d k : ℕ), d ≤ D → k ≤ K →
      ∀ (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
        (G : MvPolynomial (Fin (N + 1)) ℚ),
        I.IsPrime →
        I.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
        MvPolynomial.X (0 : Fin (N + 1)) ∉ I →
        HasProjectiveDimensionDegree I 2 d →
        G.IsHomogeneous k → G ∉ I →
      ∀ (X : Finset (IntVector N)) (B : ℝ), 1 ≤ B →
        (∀ z ∈ X, ∀ i, |(z i : ℝ)| ≤ B) →
        (∀ z ∈ X, ∀ f ∈ I, MvPolynomial.eval
          (fun i ↦ (integralAffineChartVector z i : ℚ)) f = 0) →
        (∀ z ∈ X, MvPolynomial.eval
          (fun i ↦ (integralAffineChartVector z i : ℚ)) G = 0) →
        (X.card : ℝ) ≤
          ((finitePointsOnLinearCurveComponents
            (realAffineChartIntersectionIdeal I G) X).card : ℝ) +
          C * (B + 1) ^ ((1 / 2 : ℝ) + ε) := by
  obtain ⟨C, hC, hUniform⟩ :=
    exists_uniform_surfaceProperCut_pila_rescaled hPila hBezout N D K ε hε
  refine ⟨C, hC, ?_⟩
  intro d k hd hk I G hIprime hIhomogeneous hIchart hIdegree
    hGhomogeneous hGnot X B hB hbox hzero hGzero
  have hcong : ∀ z ∈ X, IntVectorCongruent 1 z (0 : IntVector N) := by
    intro z _hz i
    exact Subsingleton.elim _ _
  have hquotient : ∀ z ∈ X, ∀ i,
      congruenceDisplacementOrZero 1 (0 : IntVector N) z i = z i := by
    intro z hz i
    simpa using (congruenceDisplacementOrZero_spec
      (0 : IntVector N) z (hcong z hz) i).symm
  apply hUniform d k hd hk I G hIprime hIhomogeneous hIchart hIdegree
    hGhomogeneous hGnot 1 (by norm_num) 0 X hzero hGzero hcong
      (B + 1) (by linarith)
  intro z hz i
  rw [hquotient z hz i]
  linarith only [hbox z hz i]

end

end TranslatedDepthSeven
