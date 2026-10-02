import TranslatedDepthSeven.StrictRootTheorem
import TranslatedDepthSeven.StaticChartReservoirCover

namespace TranslatedDepthSeven

noncomputable section

open Filter
open scoped Topology

/-- A deliberately generous fixed exponent which absorbs both certificates
attached to a chart of the displayed equation family. -/
def strictChartCertificateExponent
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (denominator : ℤ) : ℕ :=
  let K := Nat.factorial 7 *
    (equationFamilySupportBound equations *
      equationFamilyDegreeBound equations *
      equationFamilyCoefficientBound equations) ^ 7
  denominator.natAbs + 1 + K + 7 * equationFamilyDegreeBound equations

private theorem nat_le_five_pow (n : ℕ) : n ≤ 5 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hone : 1 ≤ 5 ^ n := one_le_pow₀ (by omega)
      calc
        n + 1 ≤ 5 ^ n + 5 ^ n := Nat.add_le_add ih hone
        _ ≤ 5 * 5 ^ n := by omega
        _ = 5 ^ (n + 1) := by ring

private theorem natCast_le_height_pow_self (p : Parameters) (n : ℕ) :
    (n : ℝ) ≤ p.H ^ n := by
  calc
    (n : ℝ) ≤ (5 ^ n : ℕ) := by exact_mod_cast nat_le_five_pow n
    _ = (5 : ℝ) ^ n := by norm_num
    _ ≤ p.H ^ n := pow_le_pow_left₀ (by norm_num) p.five_le_H n

/-- Every selected chart determinant has a uniform, completely explicit
height bound on the normalized point set. -/
theorem chartDeterminant_natAbs_le_heightPower
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ)
    {z : IntVector 13}
    (hz : z ∈ depthSevenNormalizedJacobianChartCell p x₀ equations CF C) :
    ((MvPolynomial.eval (integralAffineMap x₀ z p.m)
      C.determinant).natAbs : ℝ) ≤
      p.H ^ strictChartCertificateExponent equations denominator := by
  let S := equationFamilySupportBound equations
  let d := equationFamilyDegreeBound equations
  let E := equationFamilyCoefficientBound equations
  let K := Nat.factorial 7 * (S * d * E) ^ 7
  let y := integralAffineMap x₀ z p.m
  have hz' : z ∈ depthSevenNormalizedDisplacementFinset p x₀ equations CF :=
    ((mem_depthSevenNormalizedJacobianChartCell_iff
      p x₀ equations CF C z).mp hz).1
  have hy : ∀ j, (y j).natAbs ≤ ⌈p.B + p.L⌉₊ :=
    fun j => depthSevenNormalized_affineImage_coordinate_le
      p x₀ equations CF hz' j
  have hY : (max 1 ⌈p.B + p.L⌉₊ : ℝ) ≤ p.H := by
    have hBL : 0 ≤ p.B + p.L := by nlinarith [p.hB, p.hL]
    have hceil : (⌈p.B + p.L⌉₊ : ℝ) < p.B + p.L + 1 :=
      Nat.ceil_lt_add_one hBL
    have hceilH : (⌈p.B + p.L⌉₊ : ℝ) ≤ p.H := by
      unfold Parameters.H
      nlinarith [p.one_le_natCast_m]
    exact max_le p.one_le_strictHeight hceilH
  have hminor :
      (integralJacobianMinor (indexedFinsetFamily equations) y
        C.rows C.cols).natAbs ≤
        Nat.factorial 7 *
          (S * d * E * max 1 ⌈p.B + p.L⌉₊ ^ d) ^ 7 := by
    apply integralJacobianMinor_natAbs_le_factorial_mul_pow
    intro i j
    change (MvPolynomial.eval y
      (MvPolynomial.pderiv j
        (indexedFinsetFamily equations i))).natAbs ≤ _
    refine (eval_pderiv_natAbs_le_support_mul_degree_mul_coeff_mul_pow
      (e := d) (C := E) (indexedFinsetFamily equations i) y j
      ?_ ?_ hy).trans ?_
    · intro μ hμ
      apply coeff_natAbs_le_equationFamilyCoefficientBound
      · exact (equations.equivFin.symm i).2
      · exact hμ
    · apply totalDegree_le_equationFamilyDegreeBound
      exact (equations.equivFin.symm i).2
    · gcongr
      exact support_card_le_equationFamilySupportBound
        (equations.equivFin.symm i).2
  rw [IntegralDepthSevenJacobianChartIndex.determinant,
    eval_integralJacobianMinorPolynomial]
  have hK : (K : ℝ) ≤ p.H ^ K := natCast_le_height_pow_self p K
  have hY' : ((max 1 ⌈p.B + p.L⌉₊ : ℕ) : ℝ) ≤ p.H := by
    simpa only [Nat.cast_max, Nat.cast_one] using hY
  have hpow : ((max 1 ⌈p.B + p.L⌉₊ : ℕ) : ℝ) ^ (d * 7) ≤
      p.H ^ (d * 7) := pow_le_pow_left₀ (by positivity) hY' _
  have hraw :
      ((Nat.factorial 7 *
        (S * d * E * max 1 ⌈p.B + p.L⌉₊ ^ d) ^ 7 : ℕ) : ℝ) ≤
        p.H ^ (K + d * 7) := by
    norm_num only [Nat.cast_mul, Nat.cast_pow]
    calc
      _ = (K : ℝ) * ((max 1 ⌈p.B + p.L⌉₊ : ℕ) : ℝ) ^ (d * 7) := by
        dsimp [K]
        push_cast
        ring
      _ ≤ p.H ^ K * p.H ^ (d * 7) := by
        exact mul_le_mul hK hpow (pow_nonneg (Nat.cast_nonneg _) _)
          (pow_nonneg p.H_pos.le _)
      _ = p.H ^ (K + d * 7) := by rw [← pow_add]
  have hmain := (show
      ((integralJacobianMinor (indexedFinsetFamily equations) y
        C.rows C.cols).natAbs : ℝ) ≤
        ((Nat.factorial 7 *
          (S * d * E * max 1 ⌈p.B + p.L⌉₊ ^ d) ^ 7 : ℕ) : ℝ) by
      exact_mod_cast hminor).trans hraw
  apply hmain.trans
  apply pow_le_pow_right₀ (by linarith [p.five_le_H])
  dsimp [strictChartCertificateExponent, K, S, d, E]
  omega

/-- The fixed affine scale and model denominator are absorbed by the same
certificate exponent. -/
theorem scale_mul_denominator_natAbs_le_heightPower
    (p : Parameters) (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (denominator : ℤ) :
    ((((p.m : ℤ) * denominator).natAbs : ℕ) : ℝ) ≤
      p.H ^ strictChartCertificateExponent equations denominator := by
  let n := denominator.natAbs
  have hm : (p.m : ℝ) ≤ p.H := by
    unfold Parameters.H
    nlinarith [p.hB, p.hL]
  have hn : (n : ℝ) ≤ p.H ^ n := natCast_le_height_pow_self p n
  have hproduct : (p.m : ℝ) * n ≤ p.H ^ (n + 1) := by
    calc
      (p.m : ℝ) * n ≤ p.H * p.H ^ n :=
        mul_le_mul hm hn (Nat.cast_nonneg _) p.H_pos.le
      _ = p.H ^ (n + 1) := by rw [pow_succ]; ring
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  norm_num only [Nat.cast_mul]
  apply hproduct.trans
  apply pow_le_pow_right₀ (by linarith [p.five_le_H])
  dsimp [strictChartCertificateExponent, n]
  omega

/-- Eventual strict-input form of the static chart reservoir cover.  The
pool and crossing number are the literal canonical choices of the manuscript
reservoir theorem.  The only remaining inputs are the displayed nonzero and
height bounds for the two actual integer certificates. -/
theorem eventually_exists_strict_rankSevenChart_reservoirCover
    {A a Cres ε : ℝ}
    (hA : 0 ≤ A) (ha : 0 < a) (haOne : a < 1)
    (hCres : 1 < Cres) (hε : 0 < ε) :
    ∀ᶠ H : ℝ in atTop,
      ∀ (p : Parameters), p.H = H →
      ∀ (x₀ : IntVector 13)
        (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
        (C : IntegralDepthSevenJacobianChartIndex equations)
        (denominator : ℤ),
      denominator ≠ 0 →
      ((((p.m : ℤ) * denominator).natAbs : ℕ) : ℝ) ≤ H ^ A →
      (∀ z ∈ depthSevenNormalizedJacobianChartCell
        p x₀ equations CF C,
        (((MvPolynomial.eval (integralAffineMap x₀ z p.m)
          C.determinant).natAbs : ℕ) : ℝ) ≤ H ^ A) →
      ∃ (P : Finset ℕ) (k : ℕ),
        (∀ s ∈ P, s.Prime) ∧
        P = manuscriptPrimePoolAt A a H ∧
        k = manuscriptCrossingAt A a Cres H p.T ∧
        (depthSevenNormalizedJacobianChartCell
          p x₀ equations CF C).card ≤
          ∑ q ∈ modulusReservoir P k,
            (rankSevenChartReservoirCell
              p x₀ equations CF C denominator q).card := by
  filter_upwards [eventually_exists_manuscriptModulusReservoir
    hA ha haOne hCres hε] with H hreservoir
  intro p hpH x₀ equations CF C denominator hdenominatorNe hfixedSize hdetSize
  have hmNe : (p.m : ℤ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (p.one_le_m.trans_lt' Nat.zero_lt_one))
  have hfixedNe : (p.m : ℤ) * denominator ≠ 0 :=
    mul_ne_zero hmNe hdenominatorNe
  have hTH : p.T ≤ H := by simpa [← hpH] using p.T_le_H
  obtain ⟨P, k, hPprime, hPcanonical, hkcanonical, _hPcard,
    _hPinterval, _hkP, _hmoduli, _hconnected, _hfamily, _hlcm,
    _hcertOne, hcertTwo⟩ :=
    hreservoir p.T p.one_le_T hTH
  have hsurvival : ∀ D₁ D₂ : ℤ, D₁ ≠ 0 → D₂ ≠ 0 →
      (D₁.natAbs : ℝ) ≤ H ^ A → (D₂.natAbs : ℝ) ≤ H ^ A →
      Nonempty (ReservoirModulus
        (certificateAllowedPrimesTwo P D₁ D₂) k) := by
    intro D₁ D₂ hD₁ hD₂ hD₁size hD₂size
    exact (hcertTwo D₁ D₂ hD₁ hD₂ hD₁size hD₂size).2.1
  refine ⟨P, k, hPprime, hPcanonical, hkcanonical, ?_⟩
  exact card_rankSevenChartCell_le_sum_reservoirCells_of_twoCertificateSurvival
    p x₀ equations CF C denominator P k hPprime H A hsurvival
    hfixedNe hfixedSize
    (fun _z hz =>
      eval_chart_determinant_ne_zero_of_mem_normalizedChartCell
        p x₀ equations CF C hz)
    hdetSize

/-- Strict chart cover with every certificate-height premise discharged
from the fixed equation family and the literal normalization model. -/
theorem eventually_exists_model_rankSevenChart_reservoirCover
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    {a Cres ε : ℝ} (ha : 0 < a) (haOne : a < 1)
    (hCres : 1 < Cres) (hε : 0 < ε) :
    ∀ᶠ H : ℝ in atTop,
      ∀ (p : Parameters), p.H = H →
      ∀ (x₀ : IntVector 13) (CF : ℕ)
        (C : IntegralDepthSevenJacobianChartIndex equations),
      ∃ (P : Finset ℕ) (k : ℕ),
        (∀ s ∈ P, s.Prime) ∧
        P = manuscriptPrimePoolAt
          (strictChartCertificateExponent equations model.denominator : ℝ)
          a H ∧
        k = manuscriptCrossingAt
          (strictChartCertificateExponent equations model.denominator : ℝ)
          a Cres H p.T ∧
        (depthSevenNormalizedJacobianChartCell
          p x₀ equations CF C).card ≤
          ∑ q ∈ modulusReservoir P k,
            (rankSevenChartReservoirCell
              p x₀ equations CF C model.denominator q).card := by
  let A : ℝ := strictChartCertificateExponent equations model.denominator
  filter_upwards [eventually_exists_strict_rankSevenChart_reservoirCover
    (A := A) (a := a) (Cres := Cres) (ε := ε)
    (by positivity) ha haOne hCres hε] with H hcover
  intro p hpH x₀ CF C
  apply hcover p hpH x₀ equations CF C model.denominator
  · exact model.denominator_ne_zero
  · simpa only [A, hpH, Real.rpow_natCast] using
      scale_mul_denominator_natAbs_le_heightPower
        p equations model.denominator
  · intro z hz
    simpa only [A, hpH, Real.rpow_natCast] using
      chartDeterminant_natAbs_le_heightPower
        p x₀ equations CF C model.denominator hz

end

end TranslatedDepthSeven
