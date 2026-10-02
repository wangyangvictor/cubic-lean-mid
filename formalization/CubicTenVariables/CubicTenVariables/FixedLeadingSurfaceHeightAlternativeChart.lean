import CubicTenVariables.FixedLeadingSurfaceCoordinateTransport
import TranslatedDepthSeven.ProjectiveAffineChartBridge
import TranslatedDepthSeven.CharacteristicPolynomialHeight
import TranslatedDepthSeven.IsolatedVertexQuotientPersistentPila

/-! Fixed-degree dehomogenization preserves the coefficient bound exactly. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace CubicTenVariables.FixedLeadingSurfaceHeightAlternativeChart
open MvPolynomial TranslatedDepthSeven
open scoped BigOperators

private theorem integral_dehom_monomial {n : ℕ}
    (m : Option (Fin n) →₀ ℕ) (a : ℤ) :
    multivariateDehomogenization (monomial m a) = monomial m.some a := by
  rw [multivariateDehomogenization, MvPolynomial.aeval_monomial]
  rw [Finsupp.prod_option_index]
  · simp [monomial_eq]
  · simp
  · intro i x y
    simp [pow_add]

private theorem integral_dehom_coeff_of_homogeneous {n d : ℕ}
    (P : MvPolynomial (Option (Fin n)) ℤ) (hP : P.IsHomogeneous d)
    (m : Option (Fin n) →₀ ℕ) (hm : m.degree = d) :
    (multivariateDehomogenization P).coeff m.some = P.coeff m := by
  classical
  nth_rw 1 [P.as_sum]
  simp only [map_sum, integral_dehom_monomial, coeff_sum, coeff_monomial]
  rw [Finset.sum_eq_single m]
  · simp
  · intro z hz hzm
    have hzdeg : z.degree = d := by
      rw [Finsupp.degree_eq_weight_one]
      exact hP (mem_support_iff.mp hz)
    have hne : z.some ≠ m.some := fun h =>
      hzm (finsupp_eq_of_some_eq_of_degree_eq z m (hzdeg.trans hm.symm) h)
    simp [hne]
  · intro hmnot
    simpa using notMem_support_iff.mp hmnot

/-- No two monomials of one homogeneous degree collide on the standard
chart. Hence dehomogenization does not increase the coefficient maximum. -/
theorem integral_dehom_coefficient_bound {n d C : ℕ}
    (P : MvPolynomial (Option (Fin n)) ℤ) (hP : P.IsHomogeneous d)
    (hcoeff : ∀ μ, (P.coeff μ).natAbs ≤ C) :
    ∀ μ, ((multivariateDehomogenization P).coeff μ).natAbs ≤ C := by
  classical
  intro μ
  by_cases hex : ∃ m ∈ P.support, m.some = μ
  · obtain ⟨m, hm, he⟩ := hex
    have hmdeg : m.degree = d := by
      rw [Finsupp.degree_eq_weight_one]
      exact hP (mem_support_iff.mp hm)
    rw [← he, integral_dehom_coeff_of_homogeneous P hP m hmdeg]
    exact hcoeff m
  · have hz : (multivariateDehomogenization P).coeff μ = 0 := by
      nth_rw 1 [P.as_sum]
      simp only [map_sum, integral_dehom_monomial, coeff_sum, coeff_monomial]
      apply Finset.sum_eq_zero
      intro m hm
      have hne : m.some ≠ μ := fun he => hex ⟨m, hm, he⟩
      simp [hne]
    simp [hz]

/-- The two concrete descriptions of the standard chart agree, over any ring. -/
theorem dehom_rename_finSucc {R : Type*} [CommRing R] (n : ℕ)
    (P : MvPolynomial (Fin (n + 1)) R) :
    multivariateDehomogenization (rename (_root_.finSuccEquiv n) P) =
      standardDehomogenizationHom R n P := by
  have he : (multivariateDehomogenization (R := R) (σ := Fin n)).toRingHom.comp
      (rename (_root_.finSuccEquiv n)).toRingHom = standardDehomogenizationHom R n := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [multivariateDehomogenization, standardDehomogenizationHom]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp [multivariateDehomogenization, standardDehomogenizationHom]
  exact RingHom.congr_fun he P

theorem standardChart_coefficient_bound {n d C : ℕ}
    (P : MvPolynomial (Fin (n + 1)) ℤ) (hP : P.IsHomogeneous d)
    (hcoeff : ∀ μ, (P.coeff μ).natAbs ≤ C) :
    ∀ μ, ((standardDehomogenizationHom ℤ n P).coeff μ).natAbs ≤ C := by
  rw [← dehom_rename_finSucc]
  apply integral_dehom_coefficient_bound _ hP.rename_isHomogeneous
  intro μ
  obtain ⟨ν, rfl⟩ := Finsupp.mapDomain_surjective (_root_.finSuccEquiv n).surjective μ
  rw [coeff_rename_mapDomain _ (_root_.finSuccEquiv n).injective]
  exact hcoeff ν

theorem standardChart_coefficientMax_bound {n d C : ℕ}
    (P : MvPolynomial (Fin (n + 1)) ℤ) (hP : P.IsHomogeneous d)
    (hcoeff : ∀ μ, (P.coeff μ).natAbs ≤ C) :
    mvPolynomialCoefficientNatAbsMax (standardDehomogenizationHom ℤ n P) ≤ C := by
  apply Finset.sup_le
  intro μ _hμ
  exact standardChart_coefficient_bound P hP hcoeff μ

/-- The standard chart has total degree at most the fixed homogeneous degree. -/
theorem standardChart_totalDegree_le {n d : ℕ}
    (P : MvPolynomial (Fin (n + 1)) ℤ) (hP : P.IsHomogeneous d) :
    (standardDehomogenizationHom ℤ n P).totalDegree ≤ d := by
  have hd := (multivariateHomogenization_dehomogenization_of_isHomogeneous
    (rename (_root_.finSuccEquiv n) (map (Int.castRingHom ℚ) P))
    (hP.map (Int.castRingHom ℚ)).rename_isHomogeneous).1
  rw [dehom_rename_finSucc] at hd
  have he := RingHom.congr_fun
    (standardDehomogenizationHom_comp_map n (Int.castRingHom ℚ)) P
  change standardDehomogenizationHom ℚ n (map (Int.castRingHom ℚ) P) =
    map (Int.castRingHom ℚ) (standardDehomogenizationHom ℤ n P) at he
  rw [he] at hd
  simpa only [totalDegree, support_map_of_injective _
    (f := Int.castRingHom ℚ) Int.cast_injective] using hd

/-- Degree-only threshold and exponent for the four homogeneous variables. -/
def heightThreshold (d : ℕ) : ℕ := (d + 1) ^ 4 * ((d + 1) ^ 4).factorial

def heightExponent (d : ℕ) : ℕ := d * (d + 1) ^ 4 + 1

theorem interpolation_bound_le_power {d H : ℕ}
    (hH : max 1 (heightThreshold d) ≤ H) :
    (d + 1) ^ 4 * ((d + 1) ^ 4).factorial * max 1 H ^ (d * (d + 1) ^ 4) ≤
      H ^ heightExponent d := by
  have hH1 : 1 ≤ H := le_trans (le_max_left _ _) hH
  have hHC : heightThreshold d ≤ H := le_trans (le_max_right _ _) hH
  rw [max_eq_right hH1, heightExponent, pow_succ]
  exact (Nat.mul_le_mul_right _ hHC).trans_eq (Nat.mul_comm _ _)

end CubicTenVariables.FixedLeadingSurfaceHeightAlternativeChart
