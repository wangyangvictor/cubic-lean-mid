import TranslatedDepthSeven.PowerBound

/-!
# Primitive power-law calculus

This file sits below the terminal ledger.  Its hypotheses are explicit
pointwise inequalities at the natural geometric scale `T^s`, rather than
already-packaged `UniformPowerBound` statements.  The conversion theorem
checks the only epsilon bookkeeping involved: if `0 ≤ s ≤ 1`, the surplus
power `(T^s)^ε` is at most `T^ε`.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- The canonical modulus scale `q = T^(5/7)`. -/
def qScale (T : NNReal) : NNReal := T ^ (5 / 7 : ℝ)

/-- The residual box scale `U = T^(2/7) = T/q`. -/
def uScale (T : NNReal) : NNReal := T ^ (2 / 7 : ℝ)

/-- The line-height split `X = T^(2/21) = U^(1/3)`. -/
def xScale (T : NNReal) : NNReal := T ^ (2 / 21 : ℝ)

/-- The quotient modulus scale in the isolated-vertex argument. -/
def quotientQScale (T : NNReal) : NNReal := T ^ (9 / 13 : ℝ)

/-- The low-height cutoff in the isolated-vertex argument. -/
def quotientXScale (T : NNReal) : NNReal := T ^ (4 / 13 : ℝ)

theorem uScale_eq_div_qScale {T : NNReal} (hT : 1 ≤ T) :
    uScale T = T / qScale T := by
  have hT0 : T ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hT)
  unfold uScale qScale
  calc
    T ^ (2 / 7 : ℝ) = T ^ ((1 : ℝ) - 5 / 7) := by
      congr 1
      norm_num
    _ = T ^ (1 : ℝ) / T ^ (5 / 7 : ℝ) := NNReal.rpow_sub hT0 _ _
    _ = T / T ^ (5 / 7 : ℝ) := by rw [NNReal.rpow_one]

theorem xScale_eq_uScale_rpow_third (T : NNReal) :
    xScale T = (uScale T) ^ (1 / 3 : ℝ) := by
  rw [xScale, uScale, ← NNReal.rpow_mul]
  congr 1
  norm_num

theorem uScale_div_xScale {T : NNReal} (hT : 1 ≤ T) :
    uScale T / xScale T = T ^ (4 / 21 : ℝ) := by
  have hT0 : T ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hT)
  rw [uScale, xScale, ← NNReal.rpow_sub hT0]
  congr 1
  norm_num

theorem qScale_rpow_six (T : NNReal) :
    (qScale T) ^ (6 : ℝ) = T ^ (30 / 7 : ℝ) := by
  rw [qScale, ← NNReal.rpow_mul]
  congr 1
  norm_num

/-- Exact surface-packet tangent balance: `(T^(5/7))^14 = T^10`. -/
theorem qScale_rpow_fourteen (T : NNReal) :
    (qScale T) ^ (14 : ℝ) = T ^ (10 : ℝ) := by
  rw [qScale, ← NNReal.rpow_mul]
  congr 1
  norm_num

theorem xScale_rpow_five (T : NNReal) :
    (xScale T) ^ (5 : ℝ) = T ^ (10 / 21 : ℝ) := by
  rw [xScale, ← NNReal.rpow_mul]
  congr 1
  norm_num

theorem quotientQScale_rpow_five (T : NNReal) :
    (quotientQScale T) ^ (5 : ℝ) = T ^ (45 / 13 : ℝ) := by
  rw [quotientQScale, ← NNReal.rpow_mul]
  congr 1
  norm_num

/-- Exact isolated-vertex quotient balance: `(T^(9/13))^13 = T^9`. -/
theorem quotientQScale_rpow_thirteen (T : NNReal) :
    (quotientQScale T) ^ (13 : ℝ) = T ^ (9 : ℝ) := by
  rw [quotientQScale, ← NNReal.rpow_mul]
  congr 1
  norm_num

/--
A primitive pointwise estimate at scale `T^s`.  It means

`f(H,T) ≤ C_ε H^ε (T^s)^(r+ε)`

for every positive epsilon and all `H,T ≥ 1`.
-/
def ScalePowerLaw (f : CountFunction) (s r : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : NNReal, ∀ H T : NNReal, 1 ≤ H → 1 ≤ T → T ≤ H →
      f H T ≤ C * H ^ ε * (T ^ s) ^ (r + ε)

/-- A primitive scale law with `s ≤ 1` gives the usual uniform power bound
with exponent `s*r`. -/
theorem ScalePowerLaw.toUniformPowerBound {f : CountFunction} {s r : ℝ}
    (hs1 : s ≤ 1) (hf : ScalePowerLaw f s r) :
    UniformPowerBound f (s * r) := by
  intro ε hε
  obtain ⟨C, hC⟩ := hf ε hε
  refine ⟨C, ?_⟩
  intro H T hH hT hTH
  refine (hC H T hH hT hTH).trans ?_
  have hsurplus : s * ε ≤ ε := by
    nlinarith [mul_le_mul_of_nonneg_right hs1 hε.le]
  have hexponent : s * (r + ε) ≤ s * r + ε := by
    nlinarith
  unfold powerEnvelope
  rw [← NNReal.rpow_mul]
  apply mul_le_mul_right
  exact NNReal.rpow_le_rpow_of_exponent_le hT hexponent

/-- The exact function `(T^s)^r` satisfies its primitive scale law. -/
theorem scaleFunction_scalePowerLaw (s r : ℝ) (hs0 : 0 ≤ s) :
    ScalePowerLaw (fun _ T ↦ (T ^ s) ^ r) s r := by
  intro ε hε
  refine ⟨1, ?_⟩
  intro H T hH hT hTH
  have hHpow : 1 ≤ H ^ ε := NNReal.one_le_rpow hH hε.le
  have hbase : 1 ≤ T ^ s := NNReal.one_le_rpow hT hs0
  have hscale : (T ^ s) ^ r ≤ (T ^ s) ^ (r + ε) :=
    NNReal.rpow_le_rpow_of_exponent_le hbase (by linarith)
  calc
    (T ^ s) ^ r ≤ H ^ ε * (T ^ s) ^ (r + ε) := by
      exact le_trans hscale (le_mul_of_one_le_left' hHpow)
    _ = 1 * H ^ ε * (T ^ s) ^ (r + ε) := by simp

/-- The named canonical factor `(T^s)^r`. -/
def scaleFactor (s r : ℝ) : CountFunction := fun _ T ↦ (T ^ s) ^ r

theorem scaleFactor_bound {s r : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    UniformPowerBound (scaleFactor s r) (s * r) := by
  change UniformPowerBound (fun _ T ↦ (T ^ s) ^ r) (s * r)
  exact (scaleFunction_scalePowerLaw s r hs0).toUniformPowerBound hs1

theorem scaleFactor_bound_of_mul_eq {s r a : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ha : s * r = a) : UniformPowerBound (scaleFactor s r) a := by
  rw [← ha]
  exact scaleFactor_bound hs0 hs1

theorem UniformPowerBound.mul_of_add_eq {f g : CountFunction} {a b c : ℝ}
    (hc : a + b = c) (hf : UniformPowerBound f a)
    (hg : UniformPowerBound g b) :
    UniformPowerBound (fun H T ↦ f H T * g H T) c := by
  rw [← hc]
  exact hf.mul hg

end

end TranslatedDepthSeven
