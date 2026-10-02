import Mathlib.Tactic

/-!+# Arithmetic reductions for the singular-dimension entries

These are reductions of geometric statements to precise exceptional cases.
No theorem here asserts that an actual cubic satisfies the geometric premises.
In particular `t + 3 ≤ 2 * r` is the source's bespoke radial inequality, not
a textbook AG theorem that may silently be assumed in the final target.

Dimensions and ranks are natural numbers: the singular cone contains the origin,
and the component applications concern nonempty components.
-/

namespace HessianTheorem11.SingularNumerics

/-- Combining tangent containment with the singular radial bound. -/
theorem component_envelope {n t r : ℕ}
    (tangent : t + r ≤ n) (radial : t + 3 ≤ 2 * r) :
    3 * t + 3 ≤ 2 * n := by
  omega

/-- The thirteen-variable component estimate needs no exceptional-rank saving
once the tangent and radial inequalities have been proved geometrically. -/
theorem component_le_seven_in_thirteen {t r : ℕ}
    (tangent : t + r ≤ 13) (radial : t + 3 ≤ 2 * r) :
    t ≤ 7 := by
  omega

/-- The only twelve-variable component not already of dimension at most six. -/
theorem twelve_exception {t r : ℕ}
    (tangent : t + r ≤ 12) (radial : t + 3 ≤ 2 * r) (large : 6 < t) :
    t = 7 ∧ r = 5 := by
  omega

/-- The only eleven-variable component not already of dimension at most five. -/
theorem eleven_exception {t r : ℕ}
    (tangent : t + r ≤ 11) (radial : t + 3 ≤ 2 * r) (large : 5 < t) :
    t = 6 ∧ r = 5 := by
  omega

/-- Numerical assembly after the separate geometric rank-five saving has
actually been established (Theorem 31.1 in the source). -/
theorem component_le_six_in_twelve {t r : ℕ}
    (tangent : t + r ≤ 12) (radial : t + 3 ≤ 2 * r)
    (rank_five_saving : r = 5 → t ≤ 6) : t ≤ 6 := by
  by_contra h
  obtain ⟨_, hr⟩ := twelve_exception tangent radial (by omega)
  exact h (rank_five_saving hr)

/-- Numerical assembly after the eleven-variable tangent-dominance
contradiction has excluded its exceptional component. -/
theorem component_le_five_in_eleven {t r : ℕ}
    (tangent : t + r ≤ 11) (radial : t + 3 ≤ 2 * r)
    (exception_excluded : ¬ (t = 6 ∧ r = 5)) : t ≤ 5 := by
  by_contra h
  exact exception_excluded (eleven_exception tangent radial (by omega))

/-- In eleven variables the surviving numerical candidate saturates the
tangent-containment bound; equal finite dimensions can therefore be used to
identify its tangent space with the Hessian kernel. -/
theorem eleven_exception_saturates {t r : ℕ}
    (tangent : t + r ≤ 11) (radial : t + 3 ≤ 2 * r) (large : 5 < t) :
    t + r = 11 := by
  obtain ⟨ht, hr⟩ := eleven_exception tangent radial large
  omega

/-- The generic tangent-image computation in the eleven-variable branch
contradicts the separately proved generic Hessian rank at least ten. -/
theorem eleven_tangent_rank_contradiction {genericRank kernelDimension : ℕ}
    (rank_nullity : genericRank + kernelDimension = 11)
    (kernel_lower : 2 ≤ kernelDimension) (generic_lower : 10 ≤ genericRank) :
    False := by
  omega

/-- The singular equality model with rank five occupies twelve variables. -/
theorem rank_five_model_dimensions :
    2 * (5 : ℕ) - 4 = 6 ∧ 1 + 6 + 5 = 12 ∧ 2 * (5 : ℕ) - 2 = 8 := by
  norm_num

/-- For a nonzero degree-twelve determinant divisible by a fourth power of
a cubic, the multiplicity has to equal four. -/
theorem twelve_cubic_multiplicity {multiplicity : ℕ}
    (corank_lower : 4 ≤ multiplicity) (degree_bound : 3 * multiplicity ≤ 12) :
    multiplicity = 4 := by
  omega

/-- Four anticommuting involutions would force a divisibility contradicted
by the six-dimensional normal block.  The production of those involutions
is a distinct polynomial and linear-algebra proof obligation. -/
theorem no_four_divides_six : ¬ (4 : ℕ) ∣ 6 := by
  norm_num

/-- The dimension formulas in the source's simple-divisor obstruction. -/
theorem rank_five_model_obstruction_dimensions :
    12 - (8 : ℕ) = 4 ∧ 12 - 4 - (2 : ℕ) = 6 ∧
      2 ^ ((4 : ℕ) / 2) = 4 := by
  norm_num

section SignedWeights

/-- Total weight of the four singular radial blocks.  The block sizes are
`1`, `t - 1`, `n - t - r`, and `r`; the zero-weight block drops out. -/
theorem singular_weight_sum (n t r : ℤ) :
    (-8) * 1 + (-2) * (t - 1) + 0 * (n - t - r) + 4 * r =
      4 * r - 2 * t - 6 := by
  ring

/-- The arithmetic conclusion from nonnegativity of that weight sum. -/
theorem radial_of_weight_nonnegative {t r : ℤ}
    (weight_nonnegative : 0 ≤ 4 * r - 2 * t - 6) :
    t + 3 ≤ 2 * r := by
  omega

/-- Lemma 29.4: a nondegenerate proper normal span depending on at most four
linear forms leaves a coordinate whose weight can be decreased by six. -/
theorem deficient_span_common_radical_weight {s : ℤ}
    (source_size : s = 5 ∨ s = 6) : 12 - 2 * s - 6 < 0 := by
  omega

/-- Lemma 29.4: a three-dimensional nondegenerate span plus one-dimensional
radical has negative total weight in either required source dimension. -/
theorem deficient_span_mixed_weight {s : ℤ}
    (source_size : s = 5 ∨ s = 6) : 14 - 3 * s < 0 := by
  omega

/-- Lemma 29.4: a totally isotropic normal span has negative total weight. -/
theorem deficient_span_isotropic_weight {s : ℤ}
    (source_size : s = 5 ∨ s = 6) : 12 - 3 * s < 0 := by
  omega

end SignedWeights

end HessianTheorem11.SingularNumerics
