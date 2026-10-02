import CubicTenVariables.CleanShiftedSpecialization
import CubicTenVariables.LocalizedShiftedWindow

/-! Specialization of the literal localized shifted-average antecedent.
The arithmetic proposition remains explicit and is not asserted here. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.LocalizedCleanShiftedSpecialization
open MvPolynomial LocalSupremumWindow LocalSupremumNumerics NonzeroFrequencyNumerics
open CleanShiftedSpecialization

/-- One constant precedes all physical and dyadic parameters. The clean
shifted average is supplied explicitly, with the same arithmetic exponent b. -/
theorem exists_bound (F : MvPolynomial (Fin 10) ℤ) (W : ℕ)
    (Ω : Set (Fin 10 → ZMod W)) (b : ℝ)
    (hshift : LocalizedShiftedWindow.CleanShiftedAverage F W Ω b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P R φ width : ℝ,
      1 ≤ P → 1 ≤ R → R ≤ P^((3 : ℝ)/2) → φ ≤ 1 → width ≤ 1 →
      ∀ v : Fin 10 → ℤ,
      v ∈ centers (frequencies 10 (P^width*V P R φ)) (cubeRootWidth R) →
      LocalizedShiftedWindow.shiftedSum F W Ω R (cubeRootWidth R) v ≤
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


end CubicTenVariables.LocalizedCleanShiftedSpecialization
