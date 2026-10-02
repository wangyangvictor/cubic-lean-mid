import CubicTenVariables.OnionModuli

/-! Literal positive parameters for averaging the squarefull onion bound.
The source factors give c=d1*d2²*e and c²*d=d1³*d2⁵*e². -/

namespace CubicTenVariables.OnionModulusParameters
open SquarefreeResidueFactors OnionModuli

/-- The remaining unrestricted positive factor after removing d2 squared. -/
def e (c d : ℕ) : ℕ := c2 c d / (d2 c d)^2

/-- The actual source-defined parameter triple. -/
def parameters (c d : ℕ) : ℕ × ℕ × ℕ := (d1 c d, d2 c d, e c d)

/-- Each prime in d2 occurs twice in c2, as witnessed by the exact quotient. -/
theorem d2_sq_dvd_c2 (c d : ℕ) (hc : 0 < c) (hd : Squarefree d) (hdc : d ∣ c) :
    (d2 c d)^2 ∣ c2 c d := by
  rw [c2_eq_d2_mul_quotient c d hc hd hdc, pow_two]
  exact Nat.mul_dvd_mul_left _ (d2_dvd_quotient c d hc hd hdc)

theorem e_pos (c d : ℕ) (hc : 0 < c) (hd : Squarefree d) (hdc : d ∣ c) :
    0 < e c d :=
  Nat.div_pos (Nat.le_of_dvd (c2_pos c d hc hd hdc) (d2_sq_dvd_c2 c d hc hd hdc))
    (pow_pos (d2_pos c d hc hd hdc) _)

theorem c2_eq_d2_sq_mul_e (c d : ℕ) (hc : 0 < c) (hd : Squarefree d) (hdc : d ∣ c) :
    c2 c d = (d2 c d)^2 * e c d :=
  (Nat.mul_div_cancel' (d2_sq_dvd_c2 c d hc hd hdc)).symm

/-- The parameter e is also the remaining quotient of c/d by d2. -/
theorem e_eq_quotient_div_d2 (c d : ℕ) (hc : 0 < c) (hd : Squarefree d) (hdc : d ∣ c) :
    e c d = (c/d)/d2 c d := by
  rw [e, pow_two, ← Nat.div_div_eq_div_mul, c2_div_d2 c d hc hd hdc]

theorem quotient_eq_d2_mul_e (c d : ℕ) (hc : 0 < c) (hd : Squarefree d) (hdc : d ∣ c) :
    c/d = d2 c d * e c d := by
  rw [e_eq_quotient_div_d2 c d hc hd hdc]
  exact (Nat.mul_div_cancel' (d2_dvd_quotient c d hc hd hdc)).symm

/-- Exact reconstruction of the original character modulus. -/
theorem c_eq (c d : ℕ) (hc : 0 < c) (hd : Squarefree d) (hdc : d ∣ c) :
    c = d1 c d * (d2 c d)^2 * e c d := by
  calc
    c = d1 c d * c2 c d := c_eq_d1_mul_c2 c d hc hd hdc
    _ = _ := by rw [c2_eq_d2_sq_mul_e c d hc hd hdc, mul_assoc]

/-- Exact reconstruction of the original squarefree factor. -/
theorem d_eq (c d : ℕ) (hc : 0 < c) (hd : Squarefree d) (hdc : d ∣ c) :
    d = d1 c d * d2 c d := d_eq_d1_mul_d2 c d hc hd hdc

/-- Exact reconstruction of the complete squarefull modulus. -/
theorem modulus_eq (c d : ℕ) (hc : 0 < c) (hd : Squarefree d) (hdc : d ∣ c) :
    c^2*d = (d1 c d)^3 * (d2 c d)^5 * (e c d)^2 := by
  calc
    c^2*d = (d1 c d*(d2 c d)^2*e c d)^2 * (d1 c d*d2 c d) :=
      congrArg₂ (fun a b : ℕ => a*b) (congrArg (fun a : ℕ => a^2) (c_eq c d hc hd hdc))
        (d_eq c d hc hd hdc)
    _ = _ := by ring

/-- All three parameters are positive, including the unit-modulus case. -/
theorem parameters_pos (c d : ℕ) (hc : 0 < c) (hd : Squarefree d) (hdc : d ∣ c) :
    0 < (parameters c d).1 ∧ 0 < (parameters c d).2.1 ∧ 0 < (parameters c d).2.2 :=
  ⟨d1_pos c d hc hd hdc, d2_pos c d hc hd hdc, e_pos c d hc hd hdc⟩

/-- Equality of the actual parameter triples determines both original moduli. -/
theorem parameters_inj (c d c' d' : ℕ)
    (hc : 0 < c) (hd : Squarefree d) (hdc : d ∣ c)
    (hc' : 0 < c') (hd' : Squarefree d') (hdc' : d' ∣ c')
    (he : parameters c d = parameters c' d') : c = c' ∧ d = d' := by
  have h₁ := congrArg Prod.fst he
  have h₂ := congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) he
  have h₃ := congrArg (fun t : ℕ × ℕ × ℕ => t.2.2) he
  change d1 c d = d1 c' d' at h₁
  change d2 c d = d2 c' d' at h₂
  change e c d = e c' d' at h₃
  constructor
  · calc
      c = d1 c d*(d2 c d)^2*e c d := c_eq c d hc hd hdc
      _ = d1 c' d'*(d2 c' d')^2*e c' d' := by rw [h₁,h₂,h₃]
      _ = c' := (c_eq c' d' hc' hd' hdc').symm
  · calc
      d = d1 c d*d2 c d := d_eq c d hc hd hdc
      _ = d1 c' d'*d2 c' d' := by rw [h₁,h₂]
      _ = d' := (d_eq c' d' hc' hd' hdc').symm

/-- Injectivity on the literal set of eligible positive modulus pairs. -/
theorem parameters_injOn :
    Set.InjOn (fun cd : ℕ × ℕ => parameters cd.1 cd.2)
      {cd | 0 < cd.1 ∧ Squarefree cd.2 ∧ cd.2 ∣ cd.1} := by
  intro x hx y hy hxy
  obtain ⟨hc,hd⟩ := parameters_inj x.1 x.2 y.1 y.2 hx.1 hx.2.1 hx.2.2
    hy.1 hy.2.1 hy.2.2 hxy
  exact Prod.ext hc hd

@[simp] theorem e_one : e 1 1 = 1 := by
  simp [e, c2, d2, d1]

@[simp] theorem parameters_one : parameters 1 1 = (1,1,1) := by
  simp [parameters, d1, d2]

end CubicTenVariables.OnionModulusParameters
