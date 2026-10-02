import CubicTenVariables.NumericalConductor

/-! A coarse pointwise bound at every integer frequency. The proved gcd
majorant is specialized at exceptional integers zero, whose divisibility
conditions are automatic. The actual gcds then restore one power of the
squarefree part and two powers of the square part. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ConductorCoarsePointwise
open MvPolynomial

variable {F : MvPolynomial (Fin 10) ℤ} {C : ℝ}

/-- Uniform in the frequency and its numerical depths. Only the actual
coarse bounds and homogeneity are required before using the exact CRT. -/
theorem norm_div_K_bound (h : NumericalPrimeDepth.CoarseBounds F C)
    (hF : F.IsHomogeneous 3) (a b : ℕ) (ha : Squarefree a) (hb : Squarefree b)
    (hab : a.Coprime b) (v : Fin 10 → ℤ) :
    ‖completeCubicSum F (a*b^2) v‖ / NumericalConductor.K h a b v ≤
      C^(a.primeFactors.card+b.primeFactors.card)*
        ((a*b^2 : ℕ) : ℝ)^((13 : ℝ)/2) := by
  have hbase := NumericalConductor.norm_div_K_le_gcd h hF a b ha hb hab v 0 0
    (fun _ _ _ => dvd_zero _) (fun _ _ _ => dvd_zero _)
  simp only [Nat.gcd_zero_right] at hbase
  have ha0 : 0 < (a : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero ha.ne_zero
  have hb0 : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
  have hbpow : ((b : ℝ)^2)^((13 : ℝ)/2) = (b : ℝ)^13 := by
    rw [← Real.rpow_natCast_mul hb0]
    norm_num
  have hscale : ((a*b^2 : ℕ) : ℝ)^((13 : ℝ)/2) =
      (a : ℝ)^((11 : ℝ)/2)*(b : ℝ)^11*(a : ℝ)*(b : ℝ)^2 := by
    rw [Nat.cast_mul,Nat.cast_pow,Real.mul_rpow ha0.le (by positivity),hbpow,
      show (13 : ℝ)/2 = 11/2+1 by norm_num,Real.rpow_add ha0,Real.rpow_one]
    ring
  apply hbase.trans_eq
  rw [hscale]
  ring

/-- The literal complete sum at the squarefree-times-square modulus.
No lower bound on the local numerical depths is imposed. -/
theorem complete_sum_bound (h : NumericalPrimeDepth.CoarseBounds F C)
    (hF : F.IsHomogeneous 3) (a b : ℕ) (ha : Squarefree a) (hb : Squarefree b)
    (hab : a.Coprime b) (v : Fin 10 → ℤ) :
    ‖completeCubicSum F (a*b^2) v‖ ≤
      C^(a.primeFactors.card+b.primeFactors.card)*
        ((a*b^2 : ℕ) : ℝ)^((13 : ℝ)/2)*NumericalConductor.K h a b v :=
  (div_le_iff₀ (NumericalConductor.K_pos h a b v)).mp
    (norm_div_K_bound h hF a b ha hb hab v)

end CubicTenVariables.ConductorCoarsePointwise
