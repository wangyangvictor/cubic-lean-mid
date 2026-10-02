import CubicTenVariables.MicrolocalPromotionTable
import CubicTenVariables.HomogeneousOpenIntegerCertificate

/-! Integer certificates on the actual promotion open of a constructed
microlocal table. Rational open membership supplies the exact integer zero
equations and a nonzero integer principal-open value. The resulting bound
has exponent (10+j)/2 and is uniform before the integer frequency. No new
literature input or partition-exhaustion assertion occurs. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.MicrolocalTableCertificate

open MvPolynomial HessianTheorem11 TranslatedDepthSeven
open PolynomialExponentialFamily MicrolocalPromotionTable

private theorem cast_eval (P : ParameterPolynomial 10) (v : Fin 10 → ℤ) :
    (eval v P : ℚ) = eval (fun a => (v a : ℚ)) (map (Int.castRingHom ℚ) P) := by
  simpa only [Function.comp_def,Int.coe_castRingHom] using map_eval (Int.castRingHom ℚ) v P

/-- Literal rational open membership gives a specific component of the
table with all its original integer equations zero and its open value
nonzero. No denominator or good-prime assumption is needed for this step. -/
theorem integer_open_member {t j : ℕ} {F : ParameterPolynomial 10}
    {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
    (T : Table F f j) (v : Fin 10 → ℤ)
    (hv : (fun a => (v a : ℚ)) ∈ T.open) :
    ∃ i : Fin T.c, (∀ a, eval v (T.G i a) = 0) ∧ eval v (T.h i) ≠ 0 := by
  obtain ⟨i,hG,hh⟩ := hv
  refine ⟨i,?_,?_⟩
  · intro a
    have hz : eval (fun a => (v a : ℚ)) (map (Int.castRingHom ℚ) (T.G i a)) = 0 :=
      hG _ (Ideal.subset_span ⟨a,rfl⟩)
    rw [← cast_eval] at hz
    exact_mod_cast hz
  · intro hz
    apply hh
    rw [← cast_eval,hz,Int.cast_zero]

/-- One constant and degree work for every integer point in the actual
table open. The same positive integer controls all remaining primes, and
the output is the original complete sum with its precise promoted exponent. -/
theorem exists_certificate {t j : ℕ} {F : ParameterPolynomial 10}
    {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
    (T : Table F f j) :
    ∃ (C : ℝ) (D : ℕ), 1 ≤ C ∧ ∀ v : Fin 10 → ℤ,
      (fun a => (v a : ℚ)) ∈ T.open →
      ∃ Δ : ℕ, 1 ≤ Δ ∧
        (∀ H : ℝ, 1 ≤ H → (∀ a, |(v a : ℝ)| ≤ H) → (Δ : ℝ) ≤ C * H^D) ∧
        ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ Δ →
          ‖completeCubicSum F p v‖ ≤ C * (p : ℝ)^((10+(j : ℝ))/2) := by
  have hbound : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ T.N →
      ∀ (i : Fin T.c) (v : Fin 10 → ℤ),
        (fun a => (v a : ZMod p)) ∈ parameterPoints (T.G i) (T.h i) (ZMod p) →
        ‖completeCubicSum F p v‖ ≤ (T.C : ℝ) * (p : ℝ)^((10+(j : ℝ))/2) := by
    intro p _ hp i v hv
    have he : (((8+j : ℕ) : ℝ)/2+1) = (10+(j : ℝ))/2 := by push_cast; ring
    simpa only [he] using (T.choice i).complete_sum_bound p hp v hv
  obtain ⟨C₀,D,hC₀,hcert⟩ := HomogeneousOpenIntegerCertificate.exists_certificates
    F T.s T.G T.h T.N T.modulus_pos (T.C : ℝ) (fun _ => (10+(j : ℝ))/2) hbound
  let C : ℝ := max C₀ (T.C : ℝ)
  refine ⟨C,D,hC₀.trans (le_max_left _ _),?_⟩
  intro v hv
  obtain ⟨i,hG,hh⟩ := integer_open_member T v hv
  obtain ⟨Δ,hΔ,hpos,hheight,hprime⟩ := hcert i v hG hh
  refine ⟨Δ,hpos,?_,?_⟩
  · intro H hH hvH
    exact (hheight H hH hvH).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (by linarith) D))
  · intro p _ hp
    exact (hprime p hp).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))

end CubicTenVariables.MicrolocalTableCertificate
