import CubicTenVariables.FixedLeadingSurfacePrimeCountUniform

/-!
# One fixed normalization for the actual prime-count family

The integral coordinate change is chosen once from the leading form.
Its finite-field point map is an explicit bijection, so the good-prime
bound transfers to the same homogeneous equation used by the determinant
construction. The varying excluded coefficient is still a coefficient of
the original equation, not of an independently chosen model.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace CubicTenVariables.FixedLeadingSurfaceNormalizedPrimeCount

open MvPolynomial TranslatedDepthSeven Published
open FixedLeadingSurfaceCoordinateChoice FixedLeadingSurfaceCoordinateTransport
open FixedLeadingSurfacePrimeCountUniform

/-- The actual point substitution, with its integral inverse. -/
def coordinatePointEquiv {R : Type*} [CommRing R] (a b : R) :
    (Fin 3 → R) ≃ (Fin 3 → R) where
  toFun y := ![y 2, y 0 + a * y 2, y 1 + b * y 2]
  invFun x := ![x 1 - a * x 0, x 2 - b * x 0, x 0]
  left_inv y := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp

theorem coordinatePointEquiv_eq_mulVec
    {R : Type*} [CommRing R] (a b : R) (y : Fin 3 → R) :
    coordinatePointEquiv a b y = (coordinateMatrix a b).mulVec y := by
  ext i
  fin_cases i <;> simp [coordinatePointEquiv, coordinateMatrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- Coordinate substitution preserves the literal zero set cardinality,
also over finite coefficient rings. -/
theorem zero_count_coordinateEquiv
    {R : Type*} [CommRing R] (a b : R) (g : MvPolynomial (Fin 3) R) :
    Nat.card {y : Fin 3 → R // eval y (coordinateEquiv a b g) = 0} =
      Nat.card {x : Fin 3 → R // eval x g = 0} := by
  apply Nat.card_congr
  refine (coordinatePointEquiv a b).subtypeEquiv ?_
  intro y
  rw [eval_coordinateEquiv, coordinatePointEquiv_eq_mulVec]

theorem reduction_zero_count_coordinateEquiv
    (p : ℕ) (a b : ℤ) (g : MvPolynomial (Fin 3) ℤ) :
    Nat.card (SurfaceReductionZeroPoint p (coordinateEquiv a b g)) =
      Nat.card (SurfaceReductionZeroPoint p g) := by
  unfold SurfaceReductionZeroPoint
  rw [map_coordinateEquiv]
  exact zero_count_coordinateEquiv (a : ZMod p) (b : ZMod p) _

/-- The degree bound holds integrally, before reduction modulo a prime. -/
theorem totalDegree_integral_coordinateEquiv_le
    (a b : ℤ) (g : MvPolynomial (Fin 3) ℤ) :
    (coordinateEquiv a b g).totalDegree ≤ g.totalDegree := by
  nth_rw 1 [← g.sum_homogeneousComponent]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro j hj
  exact (coordinateEquiv_isHomogeneous a b
    (homogeneousComponent_isHomogeneous j g)).totalDegree_le.trans
      (Nat.le_of_lt_succ (Finset.mem_range.mp hj))

theorem firstChart_homogenize
    {d : ℕ} (g : MvPolynomial (Fin 3) ℤ) (hdegree : g.totalDegree ≤ d) :
    surfaceHypersurfaceFirstChartDehomogenize (homogenize d g) = g := by
  exact standardDehomogenizationHom_homogenize d g hdegree

theorem firstChart_transformed_homogenize
    (a b : ℤ) {d : ℕ} (g : MvPolynomial (Fin 3) ℤ)
    (hdegree : g.totalDegree ≤ d) :
    surfaceHypersurfaceFirstChartDehomogenize
      (projectiveEquiv a b (homogenize d g)) = coordinateEquiv a b g := by
  rw [integral_projectiveEquiv_homogenize]
  exact firstChart_homogenize _
    ((totalDegree_integral_coordinateEquiv_le a b g).trans hdegree)

/-- One integral normalization and one fixed excluded integer work before
all lower coefficients and all nonzero rational leading scalars. -/
theorem exists_normalized_prime_count
    (integralityOpen : Literature.HomogeneousHypersurfaceIntegralityOpen)
    (curveWeil : Literature.AffinePlaneCurveWeil)
    {d : ℕ} (hd : 2 ≤ d)
    (k : MvPolynomial (Fin 3) ℤ) (hk : k.IsHomogeneous d)
    (hirr : IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) k))
    (K₀ : ℝ) (hK₀ : 1 < K₀) :
    ∃ (a b : ℤ) (μ : Fin 3 →₀ ℕ) (D : ℕ),
      (coordinateMatrix a b).det = 1 ∧ 0 < D ∧ k.coeff μ ≠ 0 ∧
      ∀ (g : MvPolynomial (Fin 3) ℤ) (c : ℚ), c ≠ 0 →
        g.totalDegree ≤ d →
        map (Int.castRingHom ℚ) (homogeneousComponent d g) =
          C c * map (Int.castRingHom ℚ) k →
        let F := projectiveEquiv a b (homogenize d g)
        F.IsHomogeneous d ∧
        (map (Int.castRingHom ℚ) F).degreeOf 3 = d ∧
        (surfaceHypersurfaceFirstChartDehomogenize F).totalDegree ≤ d ∧
        (homogeneousComponent d g).coeff μ ≠ 0 ∧
        ((homogeneousComponent d g).coeff μ).natAbs ≤ mvPolynomialCoefficientNatAbsMax g ∧
        ∀ p : ℕ, p.Prime →
          ¬ p ∣ D * ((homogeneousComponent d g).coeff μ).natAbs →
          (Nat.card (SurfaceReductionZeroPoint p
            (surfaceHypersurfaceFirstChartDehomogenize F)) : ℝ) ≤ K₀ * (p : ℝ) ^ 2 := by
  have hk0 : k ≠ 0 := by
    intro hz
    exact hirr.ne_zero (by rw [hz, map_zero])
  obtain ⟨a, b, hdet, hvariable⟩ :=
    exists_fixed_coordinates_for_all_scalar_leading_equations k hk hk0
  obtain ⟨μ, D, hD, hμ, hcount⟩ := exists_fixed_leading_prime_count
    integralityOpen curveWeil hd k hk hirr K₀ hK₀
  refine ⟨a, b, μ, D, hdet, hD, hμ, ?_⟩
  intro g c hc hdegree htop
  have hdegreeQ : (map (Int.castRingHom ℚ) g).totalDegree ≤ d :=
    (Finset.sup_mono (support_map_subset _ _)).trans hdegree
  have htopQ : homogeneousComponent d (map (Int.castRingHom ℚ) g) =
      C c * map (Int.castRingHom ℚ) k := by
    convert htop using 1
    ext ν
    simp [coeff_homogeneousComponent, coeff_map]
  obtain ⟨hb, hheight, hprimes⟩ := hcount g c hc hdegree htop
  refine ⟨projectiveEquiv_isHomogeneous a b (homogenize_isHomogeneous d g),
    hvariable g c hc hdegreeQ htopQ, ?_, hb, hheight, ?_⟩
  · rw [firstChart_transformed_homogenize a b g hdegree]
    exact (totalDegree_integral_coordinateEquiv_le a b g).trans hdegree
  · intro p hp hpD
    rw [firstChart_transformed_homogenize a b g hdegree,
      reduction_zero_count_coordinateEquiv]
    exact hprimes p hp hpD

end CubicTenVariables.FixedLeadingSurfaceNormalizedPrimeCount
