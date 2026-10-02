import CubicTenVariables.BinaryRootDecomposition
import CubicTenVariables.BinarySingularLifts
import CubicTenVariables.BinaryPolynomialCoefficients

/-!
# The complete binary quadratic lifting bound

An integral binary polynomial of degree at most three, with cubic part
divisible by p and nondegenerate reduced quadratic part, has at most
(s+1)*p^s roots modulo p^s. All sets counted below are literal finite filters.
The singular-class recurrence and its rescaled polynomial are constructed
internally. No Hensel theorem or assumed root-count recurrence is used.
-/

noncomputable section
namespace CubicTenVariables.BinaryCubicPerturbation

/-- The binary lifting estimate, including modulus one and characteristic two.
The nonzero discriminant is the determinant of the reduced quadratic Hessian. -/
theorem rootCount_le_succ_mul_pow (G : Coefficients) (p : ℕ) [Fact p.Prime]
    (hD : (discriminant G : ZMod p) ≠ 0) (s : ℕ) :
    rootCount G p s ≤ (s+1)*p^s := by
  induction s using Nat.strong_induction_on generalizing G with
  | h s ih =>
    by_cases hs0 : s = 0
    · subst s
      simp only [rootCount_zero, zero_add, pow_zero, mul_one, le_refl]
    by_cases hs1 : s = 1
    · subst s
      simpa only [Nat.reduceAdd, pow_one] using rootCount_one_le G p hD
    have hs : 2 ≤ s := by omega
    have hbound := rootCount_le_smooth_add_singular G p hD s (by omega)
      (p^2*((s-2+1)*p^(s-2))) (by
        intro v _ hvx hvy
        let a : ℤ := (v 0).val
        let b : ℤ := (v 1).val
        obtain ⟨hx,hy⟩ := canonical_center_critical G p v hvx hvy
        have hv (i : Fin 2) : ((![a,b] i : ℤ) : ZMod p) = v i := by
          fin_cases i <;> simp [a,b]
        by_cases h0 : (p : ℤ)^2 ∣ value G (p : ℤ) a b
        · have hc := BinarySingularLifts.card_singular_binary_lifts_of_sq_dvd
            G p s hs a b hx hy h0
          have heq : liftCount G p s (by omega) v =
              p^2 * rootCount (rescale G (p : ℤ) a b) p (s-2) := by
            simpa only [liftCount, rootCount, hv] using hc
          rw [heq]
          exact Nat.mul_le_mul_left _
            (ih (s-2) (by omega) (rescale G (p : ℤ) a b)
              (rescale_nondegenerate G p a b hD))
        · have hc := BinarySingularLifts.card_singular_binary_lifts_of_not_sq_dvd
            G p s hs a b hx hy h0
          have heq : liftCount G p s (by omega) v = 0 := by
            simpa only [liftCount, hv] using hc
          rw [heq]
          exact Nat.zero_le _)
    refine hbound.trans_eq ?_
    have hpow : p^2*p^(s-2) = p^s := by
      rw [← pow_add]
      congr 1
      omega
    calc
      2*p^s + p^2*((s-2+1)*p^(s-2)) = (2+(s-2+1))*p^s := by
        rw [← hpow]
        ring
      _ = (s+1)*p^s := by congr 1; omega

/-- Literal finite-filter version of the completed binary estimate. -/
theorem card_binary_zeros_le_succ_mul_pow (G : Coefficients) (p : ℕ) [Fact p.Prime]
    (hD : (discriminant G : ZMod p) ≠ 0) (s : ℕ) :
    (Finset.univ.filter fun z : Fin 2 → ZMod (p^s) =>
      value G (p : ZMod (p^s)) (z 0) (z 1) = 0).card ≤ (s+1)*p^s :=
  rootCount_le_succ_mul_pow G p hD s

/-- The estimate for an arbitrary actual integral binary polynomial.
The reduced-degree assumption says exactly that all cubic coefficients
vanish modulo p; nondegeneracy uses the actual evaluated second derivatives. -/
theorem card_polynomial_zeros_le_succ_mul_pow
    (F : MvPolynomial (Fin 2) ℤ) (p : ℕ) [Fact p.Prime]
    (hF : F.totalDegree ≤ 3)
    (hred : (MvPolynomial.map (Int.castRingHom (ZMod p)) F).totalDegree ≤ 2)
    (hD : (HessianTheorem11.hessian
      (MvPolynomial.map (Int.castRingHom (ZMod p)) F)
      (0 : Fin 2 → ZMod p)).det ≠ 0) (s : ℕ) :
    (Finset.univ.filter fun z : Fin 2 → ZMod (p^s) =>
      MvPolynomial.eval₂ (Int.castRingHom (ZMod (p^s))) z F = 0).card ≤
        (s+1)*p^s := by
  obtain ⟨G,rfl,hG⟩ := exists_nondegenerate_polynomial_representation F p hF hred hD
  simpa only [eval₂_polynomial, Int.cast_natCast] using
    card_binary_zeros_le_succ_mul_pow G p hG s

end CubicTenVariables.BinaryCubicPerturbation
