import CubicTenVariables.FixedEquationDimensionReduction
import CubicTenVariables.DegreeSpanReduction

/-!
# Good-characteristic dimension bounds including empty generic models

If the rational equation ideal is the unit ideal, clear the denominator of
its actual certificate for 1. The same integer equations then generate the
unit ideal in every field outside one fixed finite set of characteristics.
Combining this with the existing proper-ideal theorem removes its
nonemptiness restriction. The exceptional integer precedes every prime and
every field, and the zero set is always that of the original equations.
-/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.FixedEquationDimensionAll

open MvPolynomial FixedEquationNormalization FixedEquationDimensionReduction

/-- Empty generic models stay empty away from the primes dividing one
cleared integral certificate. The actual equation ideal remains the unit
ideal, not merely an ideal with no rational solutions. -/
theorem exists_good_characteristic_top {N t : ℕ}
    (f : Fin t → MvPolynomial (Fin N) ℤ) (htop : equationIdeal f ℚ = ⊤) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ p : ℕ, ¬ p ∣ D →
      ∀ (K : Type*) [Field K] [CharP K p],
        equationIdeal f K = ⊤ ∧ zeroSet f K = ∅ := by
  have hone : map (Int.castRingHom ℚ) (1 : MvPolynomial (Fin N) ℤ) ∈
      Ideal.span (Set.range (fun i => map (Int.castRingHom ℚ) (f i))) := by
    change map (Int.castRingHom ℚ) 1 ∈ equationIdeal f ℚ
    rw [htop]
    trivial
  obtain ⟨d,hd,hcert⟩ := DegreeSpanReduction.exists_integral_certificate f 1 hone
  have hcert' : C d ∈ Ideal.span (Set.range f) := by simpa only [mul_one] using hcert
  refine ⟨d.natAbs,Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hd),?_⟩
  intro p hp K _ _
  have hdK : (d : K) ≠ 0 := by
    intro hz
    have hdiv := (CharP.intCast_eq_zero_iff K p d).mp hz
    exact hp (by simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hdiv)
  have hmem : C (d : K) ∈ equationIdeal f K := by
    have hm := Ideal.mem_map_of_mem (map (Int.castRingHom K)) hcert'
    simpa only [Ideal.map_span, ← Set.range_comp', equationIdeal, equationsOver,
      map_C, Int.coe_castRingHom] using hm
  have htopK : equationIdeal f K = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    have hm := (equationIdeal f K).mul_mem_left (C (d : K)⁻¹) hmem
    simpa only [← C_mul, inv_mul_cancel₀ hdK, C_1] using hm
  refine ⟨htopK,?_⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have h1 : (1 : MvPolynomial (Fin N) K) ∈ equationIdeal f K := by
    rw [htopK]
    trivial
  have hz := equationIdeal_le_vanishingIdeal f K h1 x hx
  simpa using hz

/-- The original quotient and the actual common-zero coordinate ring have
the stated dimension for every good-characteristic field, with no
properness or nonemptiness hypothesis on the rational equation model. -/
theorem exists_good_characteristic_dimension_bound {N t r : ℕ}
    (f : Fin t → MvPolynomial (Fin N) ℤ)
    (hdim : ringKrullDim (MvPolynomial (Fin N) ℚ ⧸ equationIdeal f ℚ) ≤
      (r : WithBot ℕ∞)) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ (p : ℕ), p.Prime → ¬ p ∣ D →
      ∀ (K : Type) [Field K] [CharP K p],
        ringKrullDim (MvPolynomial (Fin N) K ⧸ equationIdeal f K) ≤
          (r : WithBot ℕ∞) ∧
        ringKrullDim (MvPolynomial (Fin N) K ⧸ vanishingIdeal K (zeroSet f K)) ≤
          (r : WithBot ℕ∞) := by
  by_cases htop : equationIdeal f ℚ = ⊤
  · obtain ⟨D,hD,hgood⟩ := exists_good_characteristic_top f htop
    refine ⟨D,hD,?_⟩
    intro p _ hp K _ _
    obtain ⟨heq,_⟩ := hgood p hp K
    have hdK : ringKrullDim (MvPolynomial (Fin N) K ⧸ equationIdeal f K) ≤
        (r : WithBot ℕ∞) := by
      rw [heq, ringKrullDim_eq_bot_of_subsingleton]
      exact bot_le
    exact ⟨hdK,(zeroSet_dimension_le_quotient f K).trans hdK⟩
  · exact FixedEquationDimensionReduction.exists_good_characteristic_dimension_bound f htop hdim

end CubicTenVariables.FixedEquationDimensionAll
