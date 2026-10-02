import CubicTenVariables.SquarefreeResidueFactors

/-! Exact arithmetic of the manuscript's coprime onion moduli.
The factor d1 is the prescribed product of primes of valuation one in c;
no exceptional-prime integer is involved. -/

namespace CubicTenVariables.OnionModuli
open SquarefreeResidueFactors

/-- The complementary character modulus after removing d1. -/
def c2 (c d : ℕ) : ℕ := c / d1 c d

theorem d1_dvd_d (c d : ℕ) (hc : 0 < c) (hd : Squarefree d) (hdc : d ∣ c) :
    d1 c d ∣ d := by
  rw [d1_eq_div_gcd c d hc hd hdc]
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left d (c/d))

theorem d1_squarefree (c d : ℕ) (hc : 0 < c) (hd : Squarefree d) (hdc : d ∣ c) :
    Squarefree (d1 c d) := hd.squarefree_of_dvd (d1_dvd_d c d hc hd hdc)

theorem d1_pos (c d : ℕ) (hc : 0 < c) (hd : Squarefree d) (hdc : d ∣ c) :
    0 < d1 c d := Nat.pos_of_ne_zero (d1_squarefree c d hc hd hdc).ne_zero

theorem d1_dvd_c (c d : ℕ) (hc : 0 < c) (hd : Squarefree d) (hdc : d ∣ c) :
    d1 c d ∣ c := (d1_dvd_d c d hc hd hdc).trans hdc

theorem c2_pos (c d : ℕ) (hc : 0 < c) (hd : Squarefree d) (hdc : d ∣ c) :
    0 < c2 c d := Nat.div_pos (Nat.le_of_dvd hc (d1_dvd_c c d hc hd hdc))
      (d1_pos c d hc hd hdc)

theorem c_eq_d1_mul_c2 (c d : ℕ) (hc : 0 < c) (hd : Squarefree d) (hdc : d ∣ c) :
    c = d1 c d * c2 c d := (Nat.mul_div_cancel' (d1_dvd_c c d hc hd hdc)).symm

theorem d_eq_d1_mul_d2 (c d : ℕ) (hc : 0 < c) (hd : Squarefree d) (hdc : d ∣ c) :
    d = d1 c d * d2 c d := (Nat.mul_div_cancel' (d1_dvd_d c d hc hd hdc)).symm

theorem c2_eq_d2_mul_quotient (c d : ℕ) (hc : 0 < c) (hd : Squarefree d)
    (hdc : d ∣ c) : c2 c d = d2 c d * (c/d) := by
  calc
    c2 c d = (d*(c/d))/(d1 c d) := by rw [Nat.mul_div_cancel' hdc]; rfl
    _ = (d1 c d * (d2 c d*(c/d)))/(d1 c d) := by
      congr 1
      rw [← mul_assoc, ← d_eq_d1_mul_d2 c d hc hd hdc]
    _ = _ := Nat.mul_div_cancel_left _ (d1_pos c d hc hd hdc)

theorem d2_dvd_c2 (c d : ℕ) (hc : 0 < c) (hd : Squarefree d) (hdc : d ∣ c) :
    d2 c d ∣ c2 c d := by
  rw [c2_eq_d2_mul_quotient c d hc hd hdc]
  exact dvd_mul_right _ _

theorem coprime_d1_d2 (c d : ℕ) (hc : 0 < c) (hd : Squarefree d) (hdc : d ∣ c) :
    (d1 c d).Coprime (d2 c d) :=
  Nat.coprime_of_squarefree_mul (by rwa [← d_eq_d1_mul_d2 c d hc hd hdc])

theorem coprime_d1_quotient (c d : ℕ) (hc : 0 < c) (hd : Squarefree d)
    (hdc : d ∣ c) : (d1 c d).Coprime (c/d) := by
  rw [d1_eq_div_gcd c d hc hd hdc]
  exact Nat.coprime_div_gcd_of_squarefree hd (quotient_pos c d hc hd hdc).ne'

/-- The character moduli are genuinely coprime, even when either equals one. -/
theorem coprime_d1_c2 (c d : ℕ) (hc : 0 < c) (hd : Squarefree d) (hdc : d ∣ c) :
    (d1 c d).Coprime (c2 c d) := by
  rw [c2_eq_d2_mul_quotient c d hc hd hdc]
  exact (coprime_d1_d2 c d hc hd hdc).mul_right (coprime_d1_quotient c d hc hd hdc)

/-- The remaining kernel modulus is exactly the original quotient c/d. -/
theorem c2_div_d2 (c d : ℕ) (hc : 0 < c) (hd : Squarefree d) (hdc : d ∣ c) :
    c2 c d / d2 c d = c/d := by
  rw [c2, Nat.div_div_eq_div_mul, ← d_eq_d1_mul_d2 c d hc hd hdc]

end CubicTenVariables.OnionModuli
