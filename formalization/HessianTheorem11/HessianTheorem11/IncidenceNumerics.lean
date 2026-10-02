import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Numerical and monomial checks in the incidence proof

These are unconditional arithmetic theorems.  The integer variables named
`D`, `n`, and so on are not definitions of geometric invariants.  Application
to a cubic still requires proofs of the corresponding geometric inequalities
and of the stated vanishing of cubic block types.
-/

namespace HessianTheorem11.IncidenceNumerics

theorem incidence11_of_radial {D : ℤ}
    (h : D ≤ 11 ∨ 3 * (D - 11) ≤ 11 - 3) : D ≤ 13 := by omega

theorem incidence12_preliminary_of_radial {D : ℤ}
    (h : D ≤ 12 ∨ 3 * (D - 12) ≤ 12 - 3) : D ≤ 15 := by omega

theorem incidence12_of_radial_and_no_equality {D : ℤ}
    (h : D ≤ 12 ∨ 3 * (D - 12) ≤ 12 - 3)
    (hne : D ≠ 15) : D ≤ 14 := by omega

theorem incidence13_preliminary_of_radial {D : ℤ}
    (h : D ≤ 13 ∨ 3 * (D - 13) ≤ 13 - 3) : D ≤ 16 := by omega

theorem incidence13_of_radial_and_no_equality {D : ℤ}
    (h : D ≤ 13 ∨ 3 * (D - 13) ≤ 13 - 3)
    (hne : D ≠ 16) : D ≤ 15 := by omega

theorem four_not_dvd_six : ¬ (4 : ℕ) ∣ 6 := by norm_num

theorem four_not_dvd_seven : ¬ (4 : ℕ) ∣ 7 := by norm_num

theorem twelve_equality_clifford_contradiction
    (h : 2 ^ (4 / 2) ∣ (12 - 4 - 2 : ℕ)) : False := by norm_num at h

/-- The common radial weight sum before changing the radial coordinate. -/
theorem radial_weight_sum {n e a b c d : ℤ}
    (hn : n = a + b + c + d) (he : e = a - d) :
    -2 * a + b + 4 * d = n - 3 * e - c := by omega

theorem smooth_radial_weight_sum {n e a b c d : ℤ}
    (hn : n = a + b + c + d) (he : e = a - d) :
    -2 * a + b + 4 * d - 3 = n - 3 * e - c - 3 := by omega

theorem singular_radial_weight_sum {n e a c d : ℤ}
    (hn : n = a + c + d) (he : e = a - d) :
    -2 * a + 4 * d - 6 = n - 3 * e - c - 6 := by omega

/-- Check all smooth radial cubic block types at once. The exponents are
ordered `A, kx, B₀, C, D₀`. The hypotheses are exactly the vanishing types
used in the smooth branch of Proposition 6.2. -/
theorem smooth_radial_monomial_nonnegative
    {a x b c d : ℤ}
    (ha : 0 ≤ a) (hx : 0 ≤ x) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hdegree : a + x + b + c + d = 3)
    (hA3 : a ≠ 3)
    (hA2B : ¬ (a = 2 ∧ b = 1))
    (hA2C : ¬ (a = 2 ∧ c = 1))
    (hABC : ¬ (a = 1 ∧ b = 1 ∧ c = 1))
    (hAC2 : ¬ (a = 1 ∧ c = 2))
    (hxL : 0 < x → a + c = 0)
    (hxxT : 2 ≤ x → x + a + b ≤ 2) :
    0 ≤ -2 * a - 2 * x + b + 4 * d := by omega

/-- Singular radial exponents are `kx, A₀, C, D₀`. A term containing `x`
must be `x D₀²`; without a normal coordinate a term containing `A₀` is
forbidden by the differentiated rank condition. -/
theorem singular_radial_monomial_nonnegative
    {x a c d : ℤ}
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hdegree : x + a + c + d = 3)
    (hxterms : 0 < x → x = 1 ∧ a = 0 ∧ c = 0 ∧ d = 2)
    (htangent : 0 < a → 0 < d) :
    0 ≤ -8 * x - 2 * a + 4 * d := by omega

theorem thirteen_singular_projection_impossible {c : ℤ}
    (hc : 0 ≤ c) (hradial : 13 - 3 * 3 ≥ 6 + c) : False := by omega

theorem thirteen_smooth_projection_c_le_one {c : ℤ}
    (hradial : 13 - 3 * 3 ≥ 3 + c) : c ≤ 1 := by omega

/-- Numerical candidates after excluding `c=1` and the hypersurface case.
This does not itself exclude the resulting three geometric configurations. -/
theorem thirteen_candidate_triples {d a b t r : ℤ}
    (hd : 1 ≤ d) (ha : a = d + 3) (hb : b = 10 - 2 * d)
    (hbpos : 1 ≤ b) (ht : t = 13 - d) (hr : r = 13 - a)
    (hdne : d ≠ 1) :
    (d = 2 ∧ t = 11 ∧ r = 8 ∧ a = 5) ∨
    (d = 3 ∧ t = 10 ∧ r = 7 ∧ a = 6) ∨
    (d = 4 ∧ t = 9 ∧ r = 6 ∧ a = 7) := by omega

theorem thirteen_candidate_incidence {d a t : ℤ}
    (ha : a = d + 3) (ht : t = 13 - d) : t + a = 16 := by omega

/-- Twice the modified normal-span weight total of Lemma 33.2. -/
theorem deficient_normal_span_weight_negative {d r : ℤ}
    (h : r < d) : 2 + 3 - 6 * (d - r) < 0 := by omega

theorem binary_normal_quadric_weight_negative :
    (2 * 13 - 6 * 4 - 3 : ℤ) < 0 := by norm_num

theorem codimension_three_weight_negative : (1 - (3 - 1) : ℤ) < 0 := by norm_num

theorem invariant_isotropic_weight_sum (r : ℤ) :
    -2 * (5 + 1) + (4 - 2 * r) + 2 * r + 8 = 0 := by ring

theorem scalar_kernel_weight_negative {dimA0 : ℤ}
    (h : 2 ≤ dimA0) : 1 - 3 * dimA0 ≤ -5 := by omega

theorem scalar_kernel_surviving_weights :
    (-5 + 1 + 4 : ℤ) = 0 ∧ (-5 + 4 + 4 : ℤ) = 3 := by norm_num

end HessianTheorem11.IncidenceNumerics
