import TranslatedDepthSeven.IsolatedVertexQuotientCertificate

/-!
# Polynomial height of the isolated-vertex quotient certificate

This file absorbs the completely explicit certificate bound from
`IsolatedVertexQuotientCertificate` into one fixed power of
`H = 2+B+L+m`.  The exponent depends only on the fixed unimodular matrix and
the fixed lower equation family, never on the translated box, residue class,
or quotient point.
-/

namespace TranslatedDepthSeven

noncomputable section

set_option maxHeartbeats 2000000

private theorem natural_le_five_pow (n : ℕ) : n ≤ 5 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hone : 1 ≤ 5 ^ n := one_le_pow₀ (by omega)
      calc
        n + 1 ≤ 5 ^ n + 5 ^ n := Nat.add_le_add ih hone
        _ ≤ 5 * 5 ^ n := by omega
        _ = 5 ^ (n + 1) := by ring

private theorem four_factor_le_power_sum
    {H x₁ x₂ x₃ x₄ : ℝ} {a₁ a₂ a₃ a₄ : ℕ}
    (hH : 0 ≤ H) (hx₂ : 0 ≤ x₂)
    (hx₃ : 0 ≤ x₃) (hx₄ : 0 ≤ x₄)
    (h₁ : x₁ ≤ H ^ a₁) (h₂ : x₂ ≤ H ^ a₂)
    (h₃ : x₃ ≤ H ^ a₃) (h₄ : x₄ ≤ H ^ a₄) :
    x₁ * x₂ * x₃ * x₄ ≤ H ^ (a₁ + a₂ + a₃ + a₄) := by
  calc
    x₁ * x₂ * x₃ * x₄ ≤
        H ^ a₁ * H ^ a₂ * H ^ a₃ * H ^ a₄ := by gcongr
    _ = H ^ (a₁ + a₂ + a₃ + a₄) := by
      rw [show a₁ + a₂ + a₃ + a₄ = ((a₁ + a₂) + a₃) + a₄ by omega]
      rw [pow_add, pow_add, pow_add]

private theorem seventh_power_le_power
    {H x : ℝ} {a : ℕ} (hx : 0 ≤ x)
    (h : x ≤ H ^ a) :
    x ^ 7 ≤ H ^ (7 * a) := by
  calc
    x ^ 7 ≤ (H ^ a) ^ 7 := pow_le_pow_left₀ hx h 7
    _ = H ^ (a * 7) := (pow_mul H a 7).symm
    _ = H ^ (7 * a) := by rw [Nat.mul_comm a 7]

private theorem two_factor_le_power_sum
    {H x₁ x₂ : ℝ} {a₁ a₂ : ℕ}
    (hH : 0 ≤ H) (hx₂ : 0 ≤ x₂)
    (h₁ : x₁ ≤ H ^ a₁) (h₂ : x₂ ≤ H ^ a₂) :
    x₁ * x₂ ≤ H ^ (a₁ + a₂) := by
  calc
    x₁ * x₂ ≤ H ^ a₁ * H ^ a₂ := by gcongr
    _ = H ^ (a₁ + a₂) := by rw [pow_add]

/-- Every fixed natural number is absorbed by the same natural power of the
strict height, since that height is at least five. -/
theorem natCast_le_strictHeight_pow_self (p : Parameters) (n : ℕ) :
    (n : ℝ) ≤ p.H ^ n := by
  calc
    (n : ℝ) ≤ (5 ^ n : ℕ) := by exact_mod_cast natural_le_five_pow n
    _ = (5 : ℝ) ^ n := by norm_num
    _ ≤ p.H ^ n := pow_le_pow_left₀ (by norm_num) p.five_le_H n

/-- One deliberately generous but explicit exponent for the quotient
Jacobian certificate. -/
def isolatedVertexQuotientCertificateExponent
    (U : IntegralUnimodularChange 13)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ)) : ℕ :=
  let R := integralMatrixL1Norm U.forward
  let d := equationFamilyDegreeBound lowerEquations
  let S₀ := equationFamilySupportBound lowerEquations
  let E₀ := equationFamilyCoefficientBound lowerEquations
  let S := (d + 1) * (S₀ * 2 ^ d)
  let CE := (d + 1) + S₀ + E₀ + (R + 2) * d + d
  Nat.factorial 7 + 7 * (S + d + CE + (6 * R + 1) * d)

/-- The transformed lower-coordinate translation base is polynomially
bounded in the strict height. -/
theorem quotientTranslationBaseHeight_cast_le
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF) :
    ((integralMatrixL1Norm U.forward *
      depthSevenProjectionBaseHeight x₀ : ℕ) : ℝ) ≤
        p.H ^ (integralMatrixL1Norm U.forward + 1) := by
  let R := integralMatrixL1Norm U.forward
  let P := depthSevenProjectionBaseHeight x₀
  have hR : (R : ℝ) ≤ p.H ^ R := natCast_le_strictHeight_pow_self p R
  have hP : (P : ℝ) ≤ p.H :=
    depthSevenProjectionBaseHeight_cast_le p sourceEquations CF hx₀
  calc
    ((R * P : ℕ) : ℝ) = (R : ℝ) * P := by norm_num
    _ ≤ p.H ^ R * p.H :=
      mul_le_mul hR hP (Nat.cast_nonneg _) (pow_nonneg p.H_pos.le _)
    _ = p.H ^ (R + 1) := by rw [pow_succ]

/-- The coefficient bound for every translated quotient equation is one
fixed power of the strict height. -/
theorem quotientAffineCoefficientBound_cast_le
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ)) :
    let R := integralMatrixL1Norm U.forward
    let d := equationFamilyDegreeBound lowerEquations
    let S₀ := equationFamilySupportBound lowerEquations
    let E₀ := equationFamilyCoefficientBound lowerEquations
    (((d + 1) *
      (S₀ * E₀ *
        (2 * max 1 (R * depthSevenProjectionBaseHeight x₀)) ^ d) *
      max 1 p.m ^ d : ℕ) : ℝ) ≤
        p.H ^ ((d + 1) + S₀ + E₀ + (R + 2) * d + d) := by
  dsimp only
  let R := integralMatrixL1Norm U.forward
  let d := equationFamilyDegreeBound lowerEquations
  let S₀ := equationFamilySupportBound lowerEquations
  let E₀ := equationFamilyCoefficientBound lowerEquations
  have hH : (1 : ℝ) ≤ p.H := p.one_le_strictHeight
  have hRbase : ((R * depthSevenProjectionBaseHeight x₀ : ℕ) : ℝ) ≤
      p.H ^ (R + 1) :=
    quotientTranslationBaseHeight_cast_le U p sourceEquations CF hx₀
  have hmaxBase : ((max 1
      (R * depthSevenProjectionBaseHeight x₀) : ℕ) : ℝ) ≤
      p.H ^ (R + 1) := by
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (one_le_pow₀ hH) hRbase
  have htwo : (2 : ℝ) ≤ p.H := by linarith [p.five_le_H]
  have htwiceBase : ((2 * max 1
      (R * depthSevenProjectionBaseHeight x₀) : ℕ) : ℝ) ≤
      p.H ^ (R + 2) := by
    calc
      ((2 * max 1
          (R * depthSevenProjectionBaseHeight x₀) : ℕ) : ℝ) =
          (2 : ℝ) * ((max 1
            (R * depthSevenProjectionBaseHeight x₀) : ℕ) : ℝ) := by
            norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      _ ≤
          p.H * p.H ^ (R + 1) :=
        mul_le_mul htwo hmaxBase (by positivity) p.H_pos.le
      _ = p.H ^ (R + 2) := by
        rw [show R + 2 = (R + 1) + 1 by omega, pow_succ]
        ring
  have htwicePow : ((2 * max 1
      (R * depthSevenProjectionBaseHeight x₀)) ^ d : ℕ) ≤
      (p.H ^ ((R + 2) * d) : ℝ) := by
    norm_num only [Nat.cast_pow]
    calc
      ((2 * max 1
        (R * depthSevenProjectionBaseHeight x₀) : ℕ) : ℝ) ^ d ≤
          (p.H ^ (R + 2)) ^ d :=
        pow_le_pow_left₀ (by positivity) htwiceBase d
      _ = p.H ^ ((R + 2) * d) := by rw [← pow_mul]
  have hm : (p.m : ℝ) ≤ p.H := by
    unfold Parameters.H
    nlinarith [p.hB, p.hL]
  have hmaxm : ((max 1 p.m : ℕ) : ℝ) ≤ p.H := by
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le hH hm
  have hmpow : (((max 1 p.m) ^ d : ℕ) : ℝ) ≤ p.H ^ d := by
    calc
      (((max 1 p.m) ^ d : ℕ) : ℝ) =
          ((max 1 p.m : ℕ) : ℝ) ^ d := by norm_num
      _ ≤ p.H ^ d := pow_le_pow_left₀ (by positivity) hmaxm d
  have hd1 : ((d + 1 : ℕ) : ℝ) ≤ p.H ^ (d + 1) :=
    natCast_le_strictHeight_pow_self p (d + 1)
  have hS₀ : (S₀ : ℝ) ≤ p.H ^ S₀ :=
    natCast_le_strictHeight_pow_self p S₀
  have hE₀ : (E₀ : ℝ) ≤ p.H ^ E₀ :=
    natCast_le_strictHeight_pow_self p E₀
  have hinner : ((S₀ * E₀ *
      (2 * max 1 (R * depthSevenProjectionBaseHeight x₀)) ^ d : ℕ) : ℝ) ≤
      p.H ^ S₀ * p.H ^ E₀ * p.H ^ ((R + 2) * d) := by
    calc
      ((S₀ * E₀ *
          (2 * max 1 (R * depthSevenProjectionBaseHeight x₀)) ^ d : ℕ) : ℝ) =
        (S₀ : ℝ) * (E₀ : ℝ) *
          (((2 * max 1
            (R * depthSevenProjectionBaseHeight x₀)) ^ d : ℕ) : ℝ) := by
              norm_num only [Nat.cast_mul]
      _ ≤ p.H ^ S₀ * p.H ^ E₀ * p.H ^ ((R + 2) * d) := by
        gcongr
  calc
    (((d + 1) *
        (S₀ * E₀ *
          (2 * max 1 (R * depthSevenProjectionBaseHeight x₀)) ^ d) *
        (max 1 p.m) ^ d : ℕ) : ℝ) =
      ((d + 1 : ℕ) : ℝ) *
        (((S₀ * E₀ *
          (2 * max 1 (R * depthSevenProjectionBaseHeight x₀)) ^ d) : ℕ) : ℝ) *
        ((((max 1 p.m) ^ d : ℕ) : ℝ)) := by
          norm_num only [Nat.cast_mul]
    _ ≤
      p.H ^ (d + 1) *
        (p.H ^ S₀ * p.H ^ E₀ * p.H ^ ((R + 2) * d)) *
        p.H ^ d := by
      gcongr
    _ = p.H ^ ((d + 1) + S₀ + E₀ + (R + 2) * d + d) := by
      simp only [pow_add]
      ring

/-- The complete raw determinant expression is bounded by the fixed
certificate exponent. -/
theorem quotientJacobianCertificateRawBound_cast_le
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ)) :
    let R := integralMatrixL1Norm U.forward
    let d := equationFamilyDegreeBound lowerEquations
    let S₀ := equationFamilySupportBound lowerEquations
    let E₀ := equationFamilyCoefficientBound lowerEquations
    let S := (d + 1) * (S₀ * 2 ^ d)
    let C := (d + 1) *
      (S₀ * E₀ *
        (2 * max 1 (R * depthSevenProjectionBaseHeight x₀)) ^ d) *
      max 1 p.m ^ d
    ((Nat.factorial 7 *
      (S * d * C *
        max 1 (isolatedVertexTransformedNaturalSide U p) ^ d) ^ 7 : ℕ) : ℝ) ≤
      p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations := by
  dsimp only
  let R := integralMatrixL1Norm U.forward
  let d := equationFamilyDegreeBound lowerEquations
  let S₀ := equationFamilySupportBound lowerEquations
  let E₀ := equationFamilyCoefficientBound lowerEquations
  let S := (d + 1) * (S₀ * 2 ^ d)
  let CE := (d + 1) + S₀ + E₀ + (R + 2) * d + d
  let C := (d + 1) *
    (S₀ * E₀ *
      (2 * max 1 (R * depthSevenProjectionBaseHeight x₀)) ^ d) *
    max 1 p.m ^ d
  have hfac : ((Nat.factorial 7 : ℕ) : ℝ) ≤
      p.H ^ Nat.factorial 7 :=
    natCast_le_strictHeight_pow_self p (Nat.factorial 7)
  have hS : (S : ℝ) ≤ p.H ^ S :=
    natCast_le_strictHeight_pow_self p S
  have hd : (d : ℝ) ≤ p.H ^ d :=
    natCast_le_strictHeight_pow_self p d
  have hC : (C : ℝ) ≤ p.H ^ CE := by
    simpa only [C, CE, R, d, S₀, E₀] using
      quotientAffineCoefficientBound_cast_le
        U p sourceEquations CF hx₀ lowerEquations
  have hsideRaw := isolatedVertexTransformedNaturalSide_cast_le U p
  have hside : (isolatedVertexTransformedNaturalSide U p : ℝ) ≤
      (6 * R : ℕ) * p.H := by
    change (isolatedVertexTransformedNaturalSide U p : ℝ) ≤
      (6 * R : ℕ) * p.T at hsideRaw
    exact hsideRaw.trans (mul_le_mul_of_nonneg_left p.T_le_H (by positivity))
  have hfixed : ((6 * R : ℕ) : ℝ) ≤ p.H ^ (6 * R) :=
    natCast_le_strictHeight_pow_self p (6 * R)
  have hsidePower : (isolatedVertexTransformedNaturalSide U p : ℝ) ≤
      p.H ^ (6 * R + 1) := by
    calc
      (isolatedVertexTransformedNaturalSide U p : ℝ) ≤
          (6 * R : ℕ) * p.H := hside
      _ ≤ p.H ^ (6 * R) * p.H :=
        mul_le_mul_of_nonneg_right hfixed p.H_pos.le
      _ = p.H ^ (6 * R + 1) := by rw [pow_succ]
  have hmaxSide : ((max 1
      (isolatedVertexTransformedNaturalSide U p) : ℕ) : ℝ) ≤
      p.H ^ (6 * R + 1) := by
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (one_le_pow₀ p.one_le_strictHeight) hsidePower
  have hsidePow : (((max 1
      (isolatedVertexTransformedNaturalSide U p)) ^ d : ℕ) : ℝ) ≤
      p.H ^ ((6 * R + 1) * d) := by
    calc
      (((max 1
        (isolatedVertexTransformedNaturalSide U p)) ^ d : ℕ) : ℝ) =
          ((max 1
            (isolatedVertexTransformedNaturalSide U p) : ℕ) : ℝ) ^ d := by
              norm_num only [Nat.cast_pow]
      _ ≤
          (p.H ^ (6 * R + 1)) ^ d :=
        pow_le_pow_left₀ (by positivity) hmaxSide d
      _ = p.H ^ ((6 * R + 1) * d) := by rw [← pow_mul]
  have hinside : ((S * d * C *
      max 1 (isolatedVertexTransformedNaturalSide U p) ^ d : ℕ) : ℝ) ≤
      p.H ^ (S + d + CE + (6 * R + 1) * d) := by
    calc
      ((S * d * C *
          max 1 (isolatedVertexTransformedNaturalSide U p) ^ d : ℕ) : ℝ) =
        (S : ℝ) * (d : ℝ) * (C : ℝ) *
          ((((max 1
            (isolatedVertexTransformedNaturalSide U p)) ^ d : ℕ) : ℝ)) := by
              norm_num only [Nat.cast_mul]
      _ ≤ p.H ^ (S + d + CE + (6 * R + 1) * d) :=
        four_factor_le_power_sum p.H_pos.le
          (Nat.cast_nonneg d) (Nat.cast_nonneg C)
          (Nat.cast_nonneg ((max 1
            (isolatedVertexTransformedNaturalSide U p)) ^ d))
          hS hd hC hsidePow
  have hinsidePow : (((S * d * C *
      max 1 (isolatedVertexTransformedNaturalSide U p) ^ d) ^ 7 : ℕ) : ℝ) ≤
      p.H ^ (7 * (S + d + CE + (6 * R + 1) * d)) := by
    calc
      (((S * d * C *
        max 1 (isolatedVertexTransformedNaturalSide U p) ^ d) ^ 7 : ℕ) : ℝ) =
          (((S * d * C *
            max 1 (isolatedVertexTransformedNaturalSide U p) ^ d : ℕ) : ℝ) ^ 7) := by
              norm_num only [Nat.cast_pow]
      _ ≤ p.H ^ (7 * (S + d + CE + (6 * R + 1) * d)) :=
        seventh_power_le_power (Nat.cast_nonneg (S * d * C *
            max 1 (isolatedVertexTransformedNaturalSide U p) ^ d)) hinside
  calc
    ((Nat.factorial 7 *
        (S * d * C *
          max 1 (isolatedVertexTransformedNaturalSide U p) ^ d) ^ 7 : ℕ) : ℝ) =
      ((Nat.factorial 7 : ℕ) : ℝ) *
        (((S * d * C *
          max 1 (isolatedVertexTransformedNaturalSide U p) ^ d) ^ 7 : ℕ) : ℝ) := by
            norm_num only [Nat.cast_mul]
    _ ≤ p.H ^ (Nat.factorial 7 +
        7 * (S + d + CE + (6 * R + 1) * d)) :=
      two_factor_le_power_sum p.H_pos.le
        (Nat.cast_nonneg ((S * d * C *
          max 1 (isolatedVertexTransformedNaturalSide U p) ^ d) ^ 7))
        hfac hinsidePow
    _ = p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations := by
      rfl

/-- Pointwise certificate with the final height bound required for deletion
from the second reservoir. -/
theorem exists_quotientAffineEquation_jacobianCertificate_le_heightPower
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    {w : IntVector 12}
    (hw : w ∈ isolatedVertexQuotientPointFinset
      U p x₀ sourceEquations CF)
    (hregular : IsQuotientJacobianRegularAt
      (isolatedVertexQuotientAffineEquationFinset U p x₀ lowerEquations) w) :
    ∃ rows : Fin 7 → Fin
        (isolatedVertexQuotientAffineEquationFinset U p x₀ lowerEquations).card,
      ∃ cols : Fin 7 → Fin 12,
        Function.Injective rows ∧ Function.Injective cols ∧
        integralJacobianMinor
          (indexedFinsetFamily
            (isolatedVertexQuotientAffineEquationFinset
              U p x₀ lowerEquations)) w rows cols ≠ 0 ∧
        ((integralJacobianMinor
          (indexedFinsetFamily
            (isolatedVertexQuotientAffineEquationFinset
              U p x₀ lowerEquations)) w rows cols).natAbs : ℝ) ≤
          p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations := by
  obtain ⟨rows, cols, hrows, hcols, hminor, hbound⟩ :=
    exists_quotientAffineEquation_bounded_nonzero_jacobianMinor
      U p x₀ lowerEquations w hregular
      (isolatedVertexQuotientPoint_coordinate_le
        U p x₀ sourceEquations CF hw)
  refine ⟨rows, cols, hrows, hcols, hminor, ?_⟩
  have hboundReal :
      ((integralJacobianMinor
        (indexedFinsetFamily
          (isolatedVertexQuotientAffineEquationFinset
            U p x₀ lowerEquations)) w rows cols).natAbs : ℝ) ≤
        ((Nat.factorial 7 *
          (((equationFamilyDegreeBound lowerEquations + 1) *
              (equationFamilySupportBound lowerEquations *
                2 ^ equationFamilyDegreeBound lowerEquations)) *
            equationFamilyDegreeBound lowerEquations *
            ((equationFamilyDegreeBound lowerEquations + 1) *
              (equationFamilySupportBound lowerEquations *
                equationFamilyCoefficientBound lowerEquations *
                (2 * max 1
                  (integralMatrixL1Norm U.forward *
                    depthSevenProjectionBaseHeight x₀)) ^
                      equationFamilyDegreeBound lowerEquations) *
              max 1 p.m ^ equationFamilyDegreeBound lowerEquations) *
            max 1 (isolatedVertexTransformedNaturalSide U p) ^
              equationFamilyDegreeBound lowerEquations) ^ 7 : ℕ) : ℝ) := by
    exact_mod_cast hbound
  exact hboundReal.trans
    (quotientJacobianCertificateRawBound_cast_le
      U p sourceEquations CF hx₀ lowerEquations)

end

end TranslatedDepthSeven
