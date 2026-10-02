import CubicTenVariables.FiniteFrequencyRemainder
import CubicTenVariables.ShiftedCompleteSumWindow
import CubicTenVariables.NonzeroFrequencyNumerics

/-! Specialization of the explicit clean shifted-average antecedent to the
integer cube-root window used in the nonzero-frequency reduction. This is
an application of an arithmetic hypothesis, not a literature assertion. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.CleanShiftedSpecialization
open MvPolynomial LocalSupremumWindow LocalSupremumNumerics NonzeroFrequencyNumerics

/-- The integer window radius has the required uniform polynomial size. -/
theorem width_le (P R : ℝ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hRP : R ≤ P^((3 : ℝ)/2)) :
    (cubeRootWidth R : ℝ) ≤ 2*P^((1 : ℝ)/2) := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  calc
    _ ≤ 2*R^((1 : ℝ)/3) := (cubeRootWidth_bounds R hR).2
    _ ≤ 2*(P^((3 : ℝ)/2))^((1 : ℝ)/3) := by
      gcongr
    _ = _ := by
      rw [← Real.rpow_mul hP0.le]
      norm_num

/-- Every center of an actual nonempty truncated lattice window lies in a
single box of radius 3P^5. The frequency exponent may be any width≤1. -/
theorem center_norm_le (P R φ width : ℝ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hRP : R ≤ P^((3 : ℝ)/2)) (hφ : φ ≤ 1) (hwidth : width ≤ 1)
    (v : Fin 10 → ℤ)
    (hv : v ∈ centers (frequencies 10 (P^width*V P R φ)) (cubeRootWidth R)) :
    ‖(fun i => (v i : ℝ))‖ ≤ 3*P^5 := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hRP2 : R ≤ P^2 := hRP.trans (by
    rw [← Real.rpow_natCast P 2]
    exact Real.rpow_le_rpow_of_exponent_le hP (by norm_num))
  have hB0 : 0 ≤ P^width*V P R φ := by unfold V; positivity
  have hB := FiniteFrequencyRemainder.cutoff_le_fifth_power P R φ width hP hR0 hRP2 hφ hwidth
  have hL := width_le P R hP hR hRP
  have hhalf : P^((1 : ℝ)/2) ≤ P^5 := by
    rw [← Real.rpow_natCast P 5]
    exact Real.rpow_le_rpow_of_exponent_le hP (by norm_num)
  exact (ShiftedCompleteSumWindow.center_norm_le _ hB0 _ v hv).trans (by linarith)

/-- The height-window-modulus product in the arithmetic epsilon loss is
bounded before applying the clean shifted-average hypothesis. -/
theorem height_product_le (P R : ℝ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hRP : R ≤ P^((3 : ℝ)/2)) :
    (3*P^5)*(cubeRootWidth R : ℝ)*R ≤ 6*P^7 := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  calc
    _ ≤ (3*P^5)*(2*P^((1 : ℝ)/2))*(P^((3 : ℝ)/2)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (width_le P R hP hR hRP) (by positivity)
      · exact hRP
      · exact zero_le_one.trans hR
      · positivity
    _ = _ := by
      rw [← Real.rpow_natCast P 5,← Real.rpow_natCast P 7]
      calc
        _ = 6*((P^(5 : ℝ)*P^((1 : ℝ)/2))*P^((3 : ℝ)/2)) := by ring
        _ = _ := by
          rw [← Real.rpow_add hP0,← Real.rpow_add hP0]
          norm_num

/-- One constant precedes all physical and dyadic parameters. The clean
shifted average is supplied explicitly, with the same arithmetic exponent b. -/
theorem exists_bound (F : MvPolynomial (Fin 10) ℤ) (b : ℝ)
    (hshift : ShiftedCompleteSumWindow.CleanShiftedAverage F b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P R φ width : ℝ,
      1 ≤ P → 1 ≤ R → R ≤ P^((3 : ℝ)/2) → φ ≤ 1 → width ≤ 1 →
      ∀ v : Fin 10 → ℤ,
      v ∈ centers (frequencies 10 (P^width*V P R φ)) (cubeRootWidth R) →
      ShiftedCompleteSumWindow.shiftedSum F R (cubeRootWidth R) v ≤
        C*P^(7*ε)*((cubeRootWidth R : ℝ)+R^((1 : ℝ)/3))^10*R^b := by
  obtain ⟨C,hC,hbound⟩ := hshift ε hε
  refine ⟨C*6^ε,?_,?_⟩
  · exact one_le_mul_of_one_le_of_one_le hC (Real.one_le_rpow (by norm_num) hε.le)
  intro P R φ width hP hR hRP hφ hwidth v hv
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hB : 1 ≤ 3*P^5 := by nlinarith [one_le_pow₀ hP (n := 5)]
  have hcenter := center_norm_le P R φ width hP hR hRP hφ hwidth v hv
  have hb := hbound (3*P^5) R hB hR (cubeRootWidth R)
    (cubeRootWidth_pos R hR) v hcenter
  have hpow : ((3*P^5)*(cubeRootWidth R : ℝ)*R)^ε ≤ 6^ε*P^(7*ε) := by
    calc
      _ ≤ (6*P^7)^ε := Real.rpow_le_rpow (by positivity)
        (height_product_le P R hP hR hRP) hε.le
      _ = _ := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6) (by positivity),
          ← Real.rpow_natCast P 7,← Real.rpow_mul hP0.le]
        norm_num
  apply hb.trans
  calc
    _ ≤ C*(6^ε*P^(7*ε))*((cubeRootWidth R : ℝ)+R^((1 : ℝ)/3))^10*R^b := by
      gcongr
    _ = _ := by ring

end CubicTenVariables.CleanShiftedSpecialization
