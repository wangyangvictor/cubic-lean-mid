import TranslatedDepthSeven.AffineChartPilaComponentCount
import TranslatedDepthSeven.StandardAlgebraicGeometry

/-!
# Projective surface--hypersurface intersections on the standard affine chart

This file isolates the precise textbook algebraic-geometric input needed
after Salberger has produced a homogeneous auxiliary form.  If an integral
projective surface of degree `d` is cut by a homogeneous form `G` of degree
`a` which does not vanish identically on the surface, then the degrees of
the reduced affine-chart components have total at most `d * a`.

This is the hypersurface case of projective Bezout, followed by flat scalar
extension from `Q` to `R` and restriction to the standard affine chart.
It is deliberately stated as a general algebraic-geometric proposition: it
contains neither an integral-point set nor a counting conclusion.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

namespace StandardAG

/-- The affine-chart form of the hypersurface case of projective Bezout.

The function `componentDegree` records the actual Hilbert degree of each
minimal prime of the real affine chart.  The sum, rather than merely each
individual degree, is bounded by `d * a`; this also bounds the number of
components because every displayed degree is positive.

This follows from Hartshorne, Theorem I.7.7, or from
`ProjectiveProperIntersectionBezout` after decomposing the hypersurface,
together with the standard invariance of Hilbert polynomials under field
extension and passage to a nonempty affine chart. -/
def ProjectiveSurfaceAffineHypersurfaceBezout : Prop :=
  ∀ (N d a : ℕ)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (G : MvPolynomial (Fin (N + 1)) ℚ),
    I.IsPrime →
    I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
    MvPolynomial.X (0 : Fin (N + 1)) ∉ I →
    HasProjectiveDimensionDegree I 2 d →
    G.IsHomogeneous a →
    G ∉ I →
      ∃ componentDegree : Ideal (MvPolynomial (Fin N) ℝ) → ℕ,
        (∀ Q ∈ finiteMinimalPrimes
            (realAffineChartIntersectionIdeal I G),
          ∃ n : ℕ,
            n ≤ 1 ∧
            1 ≤ componentDegree Q ∧
            HasAffineHilbertDimensionDegree Q n (componentDegree Q)) ∧
        ∑ Q ∈ finiteMinimalPrimes
            (realAffineChartIntersectionIdeal I G),
          componentDegree Q ≤ d * a

end StandardAG

/-- The total-degree Bezout statement implies the degree bound required for
each individual affine minimal component. -/
theorem projectiveSurfaceAffineHypersurface_component_degree_le
    (hBezout : StandardAG.ProjectiveSurfaceAffineHypersurfaceBezout)
    {N d a : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (G : MvPolynomial (Fin (N + 1)) ℚ)
    (hIprime : I.IsPrime)
    (hIhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hIchart : MvPolynomial.X (0 : Fin (N + 1)) ∉ I)
    (hIdimensionDegree : HasProjectiveDimensionDegree I 2 d)
    (hGhomogeneous : G.IsHomogeneous a)
    (hGnot : G ∉ I)
    (Q : Ideal (MvPolynomial (Fin N) ℝ))
    (hQ : Q ∈ finiteMinimalPrimes
      (realAffineChartIntersectionIdeal I G)) :
    ∃ n e : ℕ,
      n ≤ 1 ∧ 1 ≤ e ∧ e ≤ d * a ∧
        HasAffineHilbertDimensionDegree Q n e := by
  obtain ⟨componentDegree, hcomponents, hmass⟩ :=
    hBezout N d a I G hIprime hIhomogeneous hIchart
      hIdimensionDegree hGhomogeneous hGnot
  obtain ⟨n, hn, he, hHilbert⟩ := hcomponents Q hQ
  refine ⟨n, componentDegree Q, hn, he, ?_, hHilbert⟩
  apply le_trans ?_ hmass
  exact Finset.single_le_sum
    (fun R _hR ↦ Nat.zero_le (componentDegree R)) hQ

/-- Positivity of every component degree turns the same Bezout mass into a
bound for the actual number of affine minimal components. -/
theorem projectiveSurfaceAffineHypersurface_componentCount_le
    (hBezout : StandardAG.ProjectiveSurfaceAffineHypersurfaceBezout)
    {N d a : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (G : MvPolynomial (Fin (N + 1)) ℚ)
    (hIprime : I.IsPrime)
    (hIhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hIchart : MvPolynomial.X (0 : Fin (N + 1)) ∉ I)
    (hIdimensionDegree : HasProjectiveDimensionDegree I 2 d)
    (hGhomogeneous : G.IsHomogeneous a)
    (hGnot : G ∉ I) :
    (finiteMinimalPrimes
      (realAffineChartIntersectionIdeal I G)).card ≤ d * a := by
  obtain ⟨componentDegree, hcomponents, hmass⟩ :=
    hBezout N d a I G hIprime hIhomogeneous hIchart
      hIdimensionDegree hGhomogeneous hGnot
  calc
    (finiteMinimalPrimes
        (realAffineChartIntersectionIdeal I G)).card =
        ∑ _Q ∈ finiteMinimalPrimes
          (realAffineChartIntersectionIdeal I G), 1 := by simp
    _ ≤ ∑ Q ∈ finiteMinimalPrimes
          (realAffineChartIntersectionIdeal I G), componentDegree Q := by
      apply Finset.sum_le_sum
      intro Q hQ
      obtain ⟨_n, _hn, hdegree, _hHilbert⟩ := hcomponents Q hQ
      exact hdegree
    _ ≤ d * a := hmass

end

end TranslatedDepthSeven
