import TranslatedDepthSeven.PrimitiveProjectiveCurvePrimeCover
import TranslatedDepthSeven.IntegerBoxCount

/-! A fixed irreducible plane curve has O_P(B) primitive integer zeros in
its first rational chart. The prime pool has constant cardinality because
the equation, and hence the degree of its derivative certificate, is fixed. -/
namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published Filter
open scoped BigOperators Topology
set_option maxHeartbeats 3000000

private theorem fixed_polynomial_eval_natAbs_le_pow {N B : ℕ}
    (Q : MvPolynomial (Fin N) ℤ)
    (hB : 1 ≤ B) (hcoeff : Q.support.card * mvPolynomialCoefficientNatAbsMax Q ≤ B)
    (x : Fin N → ℤ) (hx : ∀ i, (x i).natAbs ≤ B) :
    (eval x Q).natAbs ≤ B ^ (Q.totalDegree + 1) := by
  have h := eval_natAbs_le_support_mul_coeff_mul_pow_generic Q x
    (fun _ hm ↦ coeff_natAbs_le_mvPolynomialCoefficientNatAbsMax Q hm) le_rfl hx
  rw [max_eq_right hB] at h
  apply h.trans
  calc
    Q.support.card * mvPolynomialCoefficientNatAbsMax Q * B ^ Q.totalDegree ≤
        B * B ^ Q.totalDegree := Nat.mul_le_mul_right _ hcoeff
    _ = B ^ (Q.totalDegree + 1) := by rw [pow_succ]; ac_rfl

/-- Fixed-form primitive projective count in the first rational chart.
The constant is chosen before the height and the finite set of points. -/
theorem exists_primitivePlaneCurve_firstChart_linear_count
    {d : ℕ} (hd : 2 ≤ d)
    (P : MvPolynomial (Fin 3) ℤ) (hPhom : P.IsHomogeneous d)
    (hPirred : Irreducible (P.map (Int.castRingHom ℚ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℕ, 1 ≤ B → ∀ S : Finset (Fin 3 → ℤ),
      (∀ x ∈ S, IsPrimitiveIntVector x) →
      (∀ x ∈ S, x 0 ≠ 0) →
      (∀ x ∈ S, eval x P = 0) →
      (∀ x ∈ S, ∀ i, (x i).natAbs ≤ B) →
      (S.card : ℝ) ≤ C * B := by
  classical
  obtain ⟨j, _hj, hproper⟩ := exists_proper_partial_of_positive_homogeneous
    (P.map (Int.castRingHom ℚ)) hPirred.ne_zero (hPhom.map _) (by omega)
  let Q : MvPolynomial (Fin 3) ℤ := X 0 * pderiv j P
  let A : ℝ := ((Q.totalDegree + 1 : ℕ) : ℝ)
  have hA : 0 ≤ A := Nat.cast_nonneg _
  have hpools := eventually_exists_curveCertificatePrimePool (A := A) (β := 1) 0 hA (by norm_num)
  have hpoolsNat := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop).eventually hpools
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.mp hpoolsNat
  let T := max 1 (max B₀ (Q.support.card * mvPolynomialCoefficientNatAbsMax Q))
  let K : ℝ := (2 * (d * (d - 1)) : ℕ) + (A + 2) * (16 * (d : ℝ) ^ 3)
  let C : ℝ := K + ((2 * T + 1) ^ 3 : ℕ) + 1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro B hB S hprimitive hchart hzero hbox
  by_cases hBT : T ≤ B
  · obtain ⟨primes, hcard, hprimes, havoid⟩ := hB₀ B ((Nat.le_max_left B₀ _).trans ((Nat.le_max_right 1 _).trans hBT))
    have hcard' : (primes.card : ℝ) ≤ A + 2 := by
      have hh : (primes.card : ℝ) ≤ A + 1 + 1 := by simpa using hcard
      linarith
    have hprimes' : ∀ p ∈ primes, p.Prime ∧ 4 * B < p := by
      intro p hp
      obtain ⟨hprime, hlo, _⟩ := hprimes p hp
      refine ⟨hprime, ?_⟩
      have hlo' : (4 : ℝ) * B < p := by simpa only [Real.rpow_one] using hlo
      exact_mod_cast hlo'
    have havoid' : ∀ x ∈ S, primitiveFirstChartCertificate P j x ≠ 0 →
        ∃ p ∈ primes, ¬ (p : ℤ) ∣ primitiveFirstChartCertificate P j x := by
      intro x hx hD
      apply havoid _ hD
      have hcoeff : Q.support.card * mvPolynomialCoefficientNatAbsMax Q ≤ B :=
        (Nat.le_max_right B₀ _).trans ((Nat.le_max_right 1 _).trans hBT)
      have hbound := fixed_polynomial_eval_natAbs_le_pow Q hB hcoeff x (hbox x hx)
      have heval : eval x Q = primitiveFirstChartCertificate P j x := by
        simp [Q, primitiveFirstChartCertificate]
      rw [heval] at hbound
      simpa only [pow_zero, mul_one, A, Real.rpow_natCast, Nat.cast_pow] using (Nat.cast_le (α := ℝ)).mpr hbound
    have hcount := card_primitiveFirstChart_le_prime_cover hd hB P hPhom hPirred j hproper S
      hprimitive hchart hzero hbox primes hprimes' havoid'
    have hcountR : (S.card : ℝ) ≤ (2 * (d * (d - 1)) : ℕ) +
        ∑ p ∈ primes, ((d : ℝ) * p) * (2 * (d : ℝ) ^ 2) := by exact_mod_cast hcount
    have hsum : (∑ p ∈ primes, ((d : ℝ) * p) * (2 * (d : ℝ) ^ 2)) ≤
        (A + 2) * (16 * (d : ℝ) ^ 3 * B) := by
      calc
        _ ≤ ∑ _p ∈ primes, 16 * (d : ℝ) ^ 3 * B := by
          apply Finset.sum_le_sum
          intro p hp
          have hhigh : (p : ℝ) ≤ 8 * B := by simpa using (hprimes p hp).2.2
          calc
            ((d : ℝ) * p) * (2 * (d : ℝ) ^ 2) ≤
                ((d : ℝ) * (8 * B)) * (2 * (d : ℝ) ^ 2) := by gcongr
            _ = 16 * (d : ℝ) ^ 3 * B := by ring
        _ = (primes.card : ℝ) * (16 * (d : ℝ) ^ 3 * B) := by simp
        _ ≤ (A + 2) * (16 * (d : ℝ) ^ 3 * B) := mul_le_mul_of_nonneg_right hcard' (by positivity)
    have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB
    have hmain : (S.card : ℝ) ≤ K * B := by
      have hconst := mul_le_mul_of_nonneg_left hBR (show (0 : ℝ) ≤ (2 * (d * (d - 1)) : ℕ) by positivity)
      dsimp only [K]
      nlinarith
    apply hmain.trans
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg B)
    dsimp [C]
    have hnonneg : (0 : ℝ) ≤ (((2 * T + 1) ^ 3 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  · have hboxT : ∀ x ∈ S, ∀ i, (x i).natAbs ≤ T := fun x hx i ↦ (hbox x hx i).trans (by omega)
    have hsmall : (S.card : ℝ) ≤ ((2 * T + 1) ^ 3 : ℕ) := by
      exact_mod_cast card_intVector_finset_le_box S hboxT
    have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB
    apply hsmall.trans
    calc
      (((2 * T + 1) ^ 3 : ℕ) : ℝ) ≤ C := by dsimp [C]; linarith
      _ ≤ C * B := by nlinarith [hC]

end
end TranslatedDepthSeven
