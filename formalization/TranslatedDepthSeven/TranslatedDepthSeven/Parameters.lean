import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Parameters for the translated depth-seven estimate

This file records the elementary parameter normalization from the first
section of `translated_depth_seven_short.tex`.  It deliberately contains no
algebraic-geometric input.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- An integer vector in `n` coordinates. -/
abbrev IntVector (n : ℕ) := Fin n → ℤ

/-- A real vector in `n` coordinates. -/
abbrev RealVector (n : ℕ) := Fin n → ℝ

/--
The parameters which vary in the translated depth-seven estimate.

The residue is stored in `ZMod m`; the field `hm` rules out the degenerate
ring `ZMod 0`.  The fixed geometric datum is intentionally not part of this
structure.
-/
structure Parameters where
  B : ℝ
  L : ℝ
  m : ℕ
  hm : 0 < m
  center : RealVector 13
  residue : Fin 13 → ZMod m
  hB : 1 ≤ B
  hL : 1 ≤ L
  hcenter : ∀ i, |center i| ≤ B

namespace Parameters

/-- The height parameter `\mathcal H = 2 + B + L + m`. -/
def H (p : Parameters) : ℝ := 2 + p.B + p.L + p.m

/-- The normalized side length `T = 1 + L / m`. -/
def T (p : Parameters) : ℝ := 1 + p.L / p.m

theorem one_le_m (p : Parameters) : 1 ≤ p.m := p.hm

theorem natCast_m_pos (p : Parameters) : (0 : ℝ) < p.m := by
  exact_mod_cast p.hm

theorem one_le_natCast_m (p : Parameters) : (1 : ℝ) ≤ p.m := by
  exact_mod_cast p.one_le_m

theorem five_le_H (p : Parameters) : 5 ≤ p.H := by
  unfold H
  have hm := p.one_le_natCast_m
  linarith [p.hB, p.hL]

theorem H_pos (p : Parameters) : 0 < p.H := lt_of_lt_of_le (by norm_num) p.five_le_H

theorem L_nonneg (p : Parameters) : 0 ≤ p.L := le_trans (by norm_num) p.hL

theorem L_div_m_nonneg (p : Parameters) : 0 ≤ p.L / p.m :=
  div_nonneg p.L_nonneg p.natCast_m_pos.le

theorem one_le_T (p : Parameters) : 1 ≤ p.T := by
  unfold T
  linarith [p.L_div_m_nonneg]

theorem T_pos (p : Parameters) : 0 < p.T := lt_of_lt_of_le (by norm_num) p.one_le_T

theorem L_div_m_le_T (p : Parameters) : p.L / p.m ≤ p.T := by
  unfold T
  linarith

theorem L_div_m_le_L (p : Parameters) : p.L / p.m ≤ p.L := by
  rw [div_le_iff₀ p.natCast_m_pos]
  nlinarith [p.L_nonneg, p.one_le_natCast_m]

theorem T_le_H (p : Parameters) : p.T ≤ p.H := by
  have hdiv := p.L_div_m_le_L
  unfold T H
  have hm := p.one_le_natCast_m
  linarith [p.hB]

/-- Membership in the translated box of side length `L`. -/
def InTranslatedBox (p : Parameters) (x : RealVector 13) : Prop :=
  ∀ i, |x i - p.center i| ≤ p.L

/-- Coordinatewise membership in the prescribed residue class modulo `m`. -/
def InResidueClass (p : Parameters) (x : IntVector 13) : Prop :=
  ∀ i, (x i : ZMod p.m) = p.residue i

/-- Two integral vectors in the same prescribed residue class differ by
`m` times an integral vector, coordinate by coordinate.  This is the exact
existence assertion in the normalization `x = x₀ + m y`. -/
theorem exists_integral_displacement (p : Parameters)
    {x x₀ : IntVector 13} (hx : p.InResidueClass x)
    (hx₀ : p.InResidueClass x₀) :
    ∃ y : IntVector 13, ∀ i, x i = x₀ i + p.m * y i := by
  classical
  have hdvd : ∀ i, (p.m : ℤ) ∣ x₀ i - x i := by
    intro i
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub (x i) (x₀ i) p.m).mp
    exact (hx i).trans (hx₀ i).symm
  let c : IntVector 13 := fun i ↦ Classical.choose (hdvd i)
  have hc : ∀ i, x₀ i - x i = (p.m : ℤ) * c i := by
    intro i
    exact Classical.choose_spec (hdvd i)
  refine ⟨fun i ↦ -c i, ?_⟩
  intro i
  have hxi : x i = x₀ i - (p.m : ℤ) * c i := by
    linarith [hc i]
  simpa [mul_neg, sub_eq_add_neg] using hxi

/-- The integral displacement in `x = x₀ + m y` is unique. -/
theorem integral_displacement_unique (p : Parameters)
    {x x₀ y y' : IntVector 13}
    (hy : ∀ i, x i = x₀ i + p.m * y i)
    (hy' : ∀ i, x i = x₀ i + p.m * y' i) : y = y' := by
  funext i
  have hm : (p.m : ℤ) ≠ 0 := by exact_mod_cast p.hm.ne'
  apply mul_left_cancel₀ hm
  linarith [hy i, hy' i]

/-- Exact existence and uniqueness in the congruence-class normalization. -/
theorem existsUnique_integral_displacement (p : Parameters)
    {x x₀ : IntVector 13} (hx : p.InResidueClass x)
    (hx₀ : p.InResidueClass x₀) :
    ∃! y : IntVector 13, ∀ i, x i = x₀ i + p.m * y i := by
  obtain ⟨y, hy⟩ := p.exists_integral_displacement hx hx₀
  refine ⟨y, hy, ?_⟩
  intro y' hy'
  exact p.integral_displacement_unique hy' hy

/-- Two points in the translated box differ coordinatewise by at most `2L`. -/
theorem dist_le_two_L (p : Parameters) {x x' : RealVector 13}
    (hx : p.InTranslatedBox x) (hx' : p.InTranslatedBox x') (i : Fin 13) :
    |x i - x' i| ≤ 2 * p.L := by
  calc
    |x i - x' i| = |(x i - p.center i) - (x' i - p.center i)| := by ring_nf
    _ ≤ |x i - p.center i| + |x' i - p.center i| := abs_sub _ _
    _ ≤ p.L + p.L := add_le_add (hx i) (hx' i)
    _ = 2 * p.L := by ring

/--
The elementary box estimate behind `x = x_* + m y`: if two points of the
translated box differ by `m y`, then `|y_i| ≤ 2T` in every coordinate.
-/
theorem normalized_displacement_le_two_T (p : Parameters)
    {x x' y : RealVector 13} (hx : p.InTranslatedBox x)
    (hx' : p.InTranslatedBox x')
    (hxy : ∀ i, x i = x' i + p.m * y i) (i : Fin 13) :
    |y i| ≤ 2 * p.T := by
  have hdist : |x i - x' i| ≤ 2 * p.L := p.dist_le_two_L hx hx' i
  have heq : |x i - x' i| = (p.m : ℝ) * |y i| := by
    rw [hxy i]
    have hm_nonneg : (0 : ℝ) ≤ p.m := p.natCast_m_pos.le
    rw [add_sub_cancel_left, abs_mul, abs_of_nonneg hm_nonneg]
  have hy : |y i| ≤ 2 * (p.L / p.m) := by
    rw [heq] at hdist
    have hy' : |y i| ≤ (2 * p.L) / (p.m : ℝ) := by
      rw [le_div_iff₀ p.natCast_m_pos]
      simpa [mul_comm] using hdist
    simpa [div_eq_mul_inv, mul_assoc] using hy'
  calc
    |y i| ≤ 2 * (p.L / p.m) := hy
    _ ≤ 2 * p.T := mul_le_mul_of_nonneg_left p.L_div_m_le_T (by norm_num)

/-- Integral form of the normalized box estimate. -/
theorem integral_displacement_le_two_T (p : Parameters)
    {x x₀ y : IntVector 13}
    (hx : p.InTranslatedBox (fun i ↦ (x i : ℝ)))
    (hx₀ : p.InTranslatedBox (fun i ↦ (x₀ i : ℝ)))
    (hxy : ∀ i, x i = x₀ i + p.m * y i) (i : Fin 13) :
    |(y i : ℝ)| ≤ 2 * p.T := by
  exact p.normalized_displacement_le_two_T
    (y := fun j ↦ (y j : ℝ)) hx hx₀ (fun j ↦ by
      have hj := congrArg (fun z : ℤ ↦ (z : ℝ)) (hxy j)
      norm_num at hj ⊢
      exact hj) i

/-- The complete elementary normalization used in the manuscript: two box
points in the same residue class have a unique integral displacement and that
displacement lies in the box of side `2T`. -/
theorem existsUnique_normalized_displacement (p : Parameters)
    {x x₀ : IntVector 13}
    (hxres : p.InResidueClass x) (hx₀res : p.InResidueClass x₀)
    (hxbox : p.InTranslatedBox (fun i ↦ (x i : ℝ)))
    (hx₀box : p.InTranslatedBox (fun i ↦ (x₀ i : ℝ))) :
    ∃! y : IntVector 13,
      (∀ i, x i = x₀ i + p.m * y i) ∧
      (∀ i, |(y i : ℝ)| ≤ 2 * p.T) := by
  obtain ⟨y, hy, hyuniq⟩ := p.existsUnique_integral_displacement hxres hx₀res
  refine ⟨y, ⟨hy, fun i ↦ p.integral_displacement_le_two_T hxbox hx₀box hy i⟩, ?_⟩
  intro y' hy'
  exact hyuniq y' hy'.1

end Parameters

end

end TranslatedDepthSeven
