import CubicTenVariables.CubicCompositeResidueBound
import CubicTenVariables.PrimeFrogZeroMass

/-!
# Uniform bounds for actual prime-power root fibers

Specializing the proved composite constrained-root estimate at c=p^a,
d=p gives one constant before the prime, level and residue center.
The underlying unrestricted root estimate is proved by finite differencing.
-/

noncomputable section
namespace CubicTenVariables.PrimePowerRootFiberBound
open MvPolynomial SquarefreeResidueFactors PrimeFrogZeroMass
open PolynomialRootPrimeFactorization SmoothResidueIteration

/-- The literal natural quotient at every positive level. -/
theorem prime_pow_div (p a : ℕ) (hp : 0 < p) (ha : 1 ≤ a) :
    p^a/p = p^(a-1) := by
  calc
    p^a/p = (p^(a-1)*p)/p := by
      congr 1
      rw [← pow_succ]
      congr 1
      omega
    _ = p^(a-1) := by simp [hp.ne']

/-- At level at least two, the source's squarefull residue factor is p. -/
theorem d2_prime_pow (p : ℕ) (hp : p.Prime) (a : ℕ) (ha : 2 ≤ a) :
    d2 (p^a) p = p := by
  rw [d2_eq_gcd (p^a) p (pow_pos hp.pos _) hp.squarefree
    (dvd_pow_self p (by omega)), prime_pow_div p a hp.pos (by omega)]
  exact Nat.gcd_eq_left_iff_dvd.mpr (dvd_pow_self p (by omega))

/-- The existing constrained count is exactly the actual fiber above
canonical representatives, with no geometric or degree hypothesis. -/
theorem count_integerLift_eq_zeroLifts {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (p : ℕ) [Fact p.Prime]
    (a : ℕ) (ha : 1 ≤ a) (y : Fin n → ZMod p) :
    count F (integerLift p y) (p^a) p (dvd_pow_self p (by omega)) =
      (zeroLifts p a ha F y).card := by
  rw [count_prime_class F (integerLift p y) p a ha]
  simp only [integerLift, Int.cast_natCast, ZMod.natCast_zmod_val, zeroLifts]

/-- One constant before all primes, levels and residue centers bounds the
literal root fiber by its two actual prime gcd weights. No local estimate or supplied unrestricted root-count bound is left over. -/
theorem exists_uniform_bound
    
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : HessianTheorem11.Anisotropic (map (Int.castRingHom ℚ) F))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (p : ℕ) [Fact p.Prime] (a : ℕ) (ha : 1 ≤ a),
      2 ≤ a → ∀ (y : Fin 10 → ZMod p),
      eval₂ (Int.castRingHom (ZMod p)) y F = 0 →
      ((zeroLifts p a ha F y).card : ℝ) ≤
        A * (p : ℝ)^((a-1 : ℕ) * (9+ε)) * (rootWeight F p y : ℝ) := by
  obtain ⟨A,hA1,hbound⟩ :=
    CubicCompositeResidueBound.exists_composite_root_bound  F hF hA ε hε
  refine ⟨A,hA1,?_⟩
  intro p hp a ha ha2 y hy
  have hp' : p.Prime := hp.out
  have hy' : (p : ℤ) ∣ eval (integerLift p y) F := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, cast_eval_integerLift]
    exact hy
  have hb := hbound (p^a) p (pow_pos hp'.pos _) hp'.squarefree
    (dvd_pow_self p (by omega)) (integerLift p y) hy'
  rw [count_integerLift_eq_zeroLifts F p a ha y,
    prime_pow_div p a hp'.pos ha, d2_prime_pow p hp' a ha2] at hb
  simpa only [rootWeight, Nat.cast_mul, Nat.cast_pow,
    Real.rpow_natCast_mul (Nat.cast_nonneg p), mul_assoc] using hb

end CubicTenVariables.PrimePowerRootFiberBound
