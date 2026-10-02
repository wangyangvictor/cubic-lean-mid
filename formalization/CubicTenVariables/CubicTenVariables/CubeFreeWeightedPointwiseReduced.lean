import CubicTenVariables.CubeFreeNonzeroAverageReduced
import CubicTenVariables.CubeFreeConductorMoments
import CubicTenVariables.ConductorPositiveMeanNumerics

/-! Finite nonnegative weights in a translated box preserve the proved
coarse and inverse-conductor fixed-frequency bounds. The constant is
chosen before every spatial parameter, finite set and weight. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CubeFreeWeightedPointwiseReduced
open MvPolynomial HessianTheorem11 NumericalPrimeDepth
open ConductorFixedFrequency CubeFreeConductorMoments
open scoped BigOperators

variable {t N Betti : ℕ} {F : MvPolynomial (Fin 10) ℤ}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
  {tables : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)}
  {C : ℝ} {d₀ : ℕ} {h : CoarseBounds F C}

private theorem height_factor_le (D ε : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (u : Fin 10 → ℝ) (L : ℝ) (hL : 0 ≤ L) (m : ℕ)
    (v : Fin 10 → ℤ) (hv : ∀ k, |(v k : ℝ)-u k| ≤ L) :
    (D*frequencyHeight v)^ε ≤ (D*(2+‖u‖+L+(m : ℝ)))^ε := by
  have hf : 0 ≤ frequencyHeight v := by dsimp [frequencyHeight]; positivity
  exact Real.rpow_le_rpow (mul_nonneg (zero_le_one.trans hD) hf)
    (mul_le_mul_of_nonneg_left (ConductorPositiveMeanNumerics.height_le u L hL m v hv)
      (zero_le_one.trans hD)) hε

/-- The coarse cube-free mean with any nonnegative finite weight on
nonzero frequencies. No coprimality or progression restriction is needed. -/
theorem exists_coarse_bound
    (integrality : CubicPrincipalOpenUniform.Uniform)
    (cubicWeil : Literature.SmoothCubicWeil)
    (isolated : CubicSurfacePointCountReduced.IsolatedConjugateCubicSurfacePointCount)
    (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    (hP : MicrolocalRationalPartition.Conclusion F f N Betti tables)
    (hhom : F.IsHomogeneous 3) (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ D : ℝ, 1 ≤ D →
      ∀ (u : Fin 10 → ℝ) (L : ℝ), 0 ≤ L → ∀ m : ℕ,
      ∀ (V : Finset (Fin 10 → ℤ)) (w : (Fin 10 → ℤ) → ℝ),
      (∀ v ∈ V, 0 ≤ w v) →
      (∀ v ∈ V, ∀ k, |(v k : ℝ)-u k| ≤ L) →
      (∀ v ∈ V, v ≠ 0) →
      (∑ v ∈ V, ∑ q ∈ CubeFreeNonzeroAverageReduced.window D,
        w v*‖completeCubicSum F q v‖) ≤
        M*(D*(2+‖u‖+L+(m : ℝ)))^ε*D^9*(∑ v ∈ V, w v) := by
  classical
  obtain ⟨M,hM,hbound⟩ := CubeFreeNonzeroAverageReduced.of_data integrality cubicWeil isolated pointcount
    F hhom hAn f N Betti hP.modulus_pos hP.geometry hP.incidence ε hε
  refine ⟨M,hM,?_⟩
  intro D hD u L hL m V w hw hbox hnonzero
  have hpoint (v : Fin 10 → ℤ) (hv : v ∈ V) :
      (∑ q ∈ CubeFreeNonzeroAverageReduced.window D, w v*‖completeCubicSum F q v‖) ≤
        w v*(M*(D*(2+‖u‖+L+(m : ℝ)))^ε*D^9) := by
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (hw v hv)
    apply (hbound v (hnonzero v hv) D hD).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (height_factor_le D ε hD hε.le u L hL m v (hbox v hv))
        (zero_le_one.trans hM)) (by positivity)
  calc
    _ ≤ ∑ v ∈ V, w v*(M*(D*(2+‖u‖+L+(m : ℝ)))^ε*D^9) :=
      Finset.sum_le_sum hpoint
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- The inverse moment with any nonnegative finite weight on the exact
generic frequency set. The same actual numerical conductor is retained. -/
theorem exists_inverse_bound
    (hhom : F.IsHomogeneous 3)
    (hc : MicrolocalConductorDepth.Conclusion F f tables N C d₀ h)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ D : ℝ, 1 ≤ D →
      ∀ (u : Fin 10 → ℝ) (L : ℝ), 0 ≤ L → ∀ m : ℕ,
      ∀ (V : Finset (Fin 10 → ℤ)) (w : (Fin 10 → ℤ) → ℝ),
      (∀ v ∈ V, 0 ≤ w v) →
      (∀ v ∈ V, ∀ k, |(v k : ℝ)-u k| ≤ L) →
      (∀ v ∈ V, GoodFrequency F f tables v) →
      (∑ v ∈ V, ∑ q ∈ CubeFreeNonzeroAverageReduced.window D,
        w v*(‖completeCubicSum F q v‖ / CubeFreeFixedFrequency.conductor h q v)) ≤
        M*(D*(2+‖u‖+L+(m : ℝ)))^ε*D^((13 : ℝ)/2)*(∑ v ∈ V, w v) := by
  classical
  obtain ⟨M,hM,hbound⟩ := CubeFreeConductorMoments.exists_inverse_bound hhom hc ε hε
  refine ⟨M,hM,?_⟩
  intro D hD u L hL m V w hw hbox hgood
  have hpoint (v : Fin 10 → ℤ) (hv : v ∈ V) :
      (∑ q ∈ CubeFreeNonzeroAverageReduced.window D,
        w v*(‖completeCubicSum F q v‖ / CubeFreeFixedFrequency.conductor h q v)) ≤
        w v*(M*(D*(2+‖u‖+L+(m : ℝ)))^ε*D^((13 : ℝ)/2)) := by
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (hw v hv)
    apply (hbound v (hgood v hv) D hD).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (height_factor_le D ε hD hε.le u L hL m v (hbox v hv))
        (zero_le_one.trans hM)) (by positivity)
  calc
    _ ≤ ∑ v ∈ V, w v*(M*(D*(2+‖u‖+L+(m : ℝ)))^ε*D^((13 : ℝ)/2)) :=
      Finset.sum_le_sum hpoint
    _ = _ := by rw [← Finset.sum_mul]; ring

end CubicTenVariables.CubeFreeWeightedPointwiseReduced
