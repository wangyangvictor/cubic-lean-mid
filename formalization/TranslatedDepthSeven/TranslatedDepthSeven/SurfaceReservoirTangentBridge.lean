import TranslatedDepthSeven.ConcreteTangentPacketCover
import TranslatedDepthSeven.ConcreteExceptionalRescaling
import TranslatedDepthSeven.ManuscriptReservoirTarget

/-!
# Matching the real normalized side to the integral tangent threshold

The exact normalized displacement set is contained in the integral box of
radius `ceil (2*T)`.  For the tangent-packet theorem we deliberately use
that integer as the parameter called `T`; this only changes the reservoir
constant.  The lemmas below make the rounding and that fixed constant
explicit.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- The integer side used in the normalized tangent calculation. -/
def surfaceTangentNaturalSide (p : Parameters) : ℕ :=
  ⌈2 * p.T⌉₊

/-- The manuscript's real normalized side as a nonnegative real. -/
def surfaceTangentRealSide (p : Parameters) : NNReal :=
  ⟨p.T, p.T_pos.le⟩

@[simp]
theorem coe_surfaceTangentRealSide (p : Parameters) :
    (surfaceTangentRealSide p : ℝ) = p.T := rfl

/-- A reservoir constant which absorbs the factor introduced by replacing
the real `T` by `ceil (2*T)`. -/
def normalizedSurfaceReservoirConstant : ℝ :=
  3 * tangentReservoirConstant

theorem one_le_surfaceTangentNaturalSide (p : Parameters) :
    1 ≤ surfaceTangentNaturalSide p := by
  have hreal : (1 : ℝ) ≤ 2 * p.T := by
    nlinarith [p.one_le_T]
  exact_mod_cast hreal.trans (Nat.le_ceil (2 * p.T))

/-- The literal normalized point set has the coordinate bound required by
the tangent-packet theorem with `surfaceTangentNaturalSide`. -/
theorem depthSevenNormalized_coordinate_le_two_surfaceTangentNaturalSide
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {z : IntVector 13}
    (hz : z ∈ depthSevenNormalizedDisplacementFinset p x₀ equations CF) :
    ∀ j, (z j).natAbs ≤ 2 * surfaceTangentNaturalSide p := by
  classical
  intro j
  have hzbox : z ∈ integerSupNormBox 13 ⌈2 * p.T⌉₊ :=
    (Finset.mem_filter.mp hz).1
  have hcoord := (mem_integerSupNormBox_iff z).mp hzbox j
  exact hcoord.trans (Nat.le_mul_of_pos_left _ (by omega))

theorem surfaceTangentNaturalSide_cast_le_three_mul (p : Parameters) :
    (surfaceTangentNaturalSide p : NNReal) ≤ 3 * surfaceTangentRealSide p := by
  change (surfaceTangentNaturalSide p : ℝ) ≤ 3 * p.T
  have hceil : (surfaceTangentNaturalSide p : ℝ) < 2 * p.T + 1 := by
    exact Nat.ceil_lt_add_one (mul_nonneg (by norm_num) p.T_pos.le)
  linarith [p.one_le_T]

theorem qScale_surfaceTangentNaturalSide_le_three_mul (p : Parameters) :
    qScale (surfaceTangentNaturalSide p : NNReal) ≤
      3 * qScale (surfaceTangentRealSide p) := by
  have hbase := NNReal.rpow_le_rpow
    (surfaceTangentNaturalSide_cast_le_three_mul p)
    (by norm_num : (0 : ℝ) ≤ 5 / 7)
  have hthree : (3 : NNReal) ^ (5 / 7 : ℝ) ≤ 3 := by
    calc
      (3 : NNReal) ^ (5 / 7 : ℝ) ≤ (3 : NNReal) ^ (1 : ℝ) :=
        NNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 3 := NNReal.rpow_one 3
  calc
    qScale (surfaceTangentNaturalSide p : NNReal) ≤
        qScale (3 * surfaceTangentRealSide p) := hbase
    _ = (3 : NNReal) ^ (5 / 7 : ℝ) *
        qScale (surfaceTangentRealSide p) := by
      rw [qScale, qScale, NNReal.mul_rpow]
    _ ≤ 3 * qScale (surfaceTangentRealSide p) := by
      exact mul_le_mul_of_nonneg_right hthree (by positivity)

/-- The lower endpoint of the manuscript reservoir, with the enlarged fixed
constant, dominates the exact integral tangent threshold. -/
theorem surfaceTangentQThreshold_le_normalized_manuscriptReservoirTarget
    (p : Parameters) :
    surfaceTangentQThreshold (surfaceTangentNaturalSide p) ≤
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) := by
  apply Nat.ceil_mono
  change (tangentReservoirConstant : ℝ) *
      (qScale (surfaceTangentNaturalSide p : NNReal) : ℝ) ≤
    normalizedSurfaceReservoirConstant * p.T ^ (5 / 7 : ℝ)
  have hscale :
      (qScale (surfaceTangentNaturalSide p : NNReal) : ℝ) ≤
        3 * (qScale (surfaceTangentRealSide p) : ℝ) := by
    exact_mod_cast qScale_surfaceTangentNaturalSide_le_three_mul p
  have hconstant : 0 ≤ (tangentReservoirConstant : ℝ) := by positivity
  calc
    (tangentReservoirConstant : ℝ) *
        (qScale (surfaceTangentNaturalSide p : NNReal) : ℝ) ≤
      (tangentReservoirConstant : ℝ) *
        (3 * (qScale (surfaceTangentRealSide p) : ℝ)) :=
      mul_le_mul_of_nonneg_left hscale hconstant
    _ = normalizedSurfaceReservoirConstant * p.T ^ (5 / 7 : ℝ) := by
      simp [normalizedSurfaceReservoirConstant, qScale]
      ring

/-- Hence every modulus above the reservoir target satisfies the exact
integer threshold used by the concrete occupied-packet theorem. -/
theorem surfaceTangentQThreshold_le_of_normalized_reservoir_lower
    (p : Parameters) {q : ℕ}
    (hq : manuscriptReservoirTarget normalizedSurfaceReservoirConstant
      p.T (5 / 7) ≤ q) :
    surfaceTangentQThreshold (surfaceTangentNaturalSide p) ≤ q :=
  (surfaceTangentQThreshold_le_normalized_manuscriptReservoirTarget p).trans hq

end

end TranslatedDepthSeven
