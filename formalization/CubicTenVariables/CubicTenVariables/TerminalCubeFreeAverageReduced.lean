import CubicTenVariables.TerminalFrequencyCount
import CubicTenVariables.CubeFreeNonzeroAverageReduced
import CubicTenVariables.ConductorPositiveMeanNumerics

/-! The terminal contribution to the complementary cube-free mean:
the literal B4 progression count and the actual coarse cube-free estimate
give the T D^9 term, with one constant before all summation parameters. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.TerminalCubeFreeAverageReduced
open MvPolynomial HessianTheorem11 ProjectiveMicrolocalData
open ConeComponentProgressionCount ConductorFixedFrequency
open scoped BigOperators

theorem of_data
    (spread : CubicPrincipalOpenUniform.Uniform)
    (cubicWeil : Literature.SmoothCubicWeil)
    (isolated : CubicSurfacePointCountReduced.IsolatedConjugateCubicSurfacePointCount)
    (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    {t : ℕ} (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10)
    (N B : ℕ) (hN : 1 ≤ N) (hgeo : Geometry F f)
    (hData : TenMicrolocalIncidence.Conclusion F f N B)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (D : ℝ) (u : Fin 10 → ℝ) (L : ℝ) (m : ℕ)
      (b : Fin 10 → ℤ), 1 ≤ D → 0 ≤ L → 0 < m →
      (∑ v ∈ points (OffTerminalFrequencyCertificate.exceptionalSet F) u L m b,
        ∑ q ∈ CubeFreeNonzeroAverageReduced.window D, ‖completeCubicSum F q v‖) ≤
        M*(D*(2+‖u‖+L+(m : ℝ)))^ε*(1+L/(m : ℝ))*D^9 := by
  classical
  obtain ⟨K,hK,hcount⟩ := TerminalFrequencyCount.exists_bound F hF hAn
  obtain ⟨A,hA,hfixed⟩ := CubeFreeNonzeroAverageReduced.of_data
    spread cubicWeil isolated pointcount F hF hAn f N B hN hgeo hData ε hε
  refine ⟨K*A,by nlinarith,?_⟩
  intro D u L m b hD hL hm
  let V := points (OffTerminalFrequencyCertificate.exceptionalSet F) u L m b
  let H : ℝ := 2+‖u‖+L+(m : ℝ)
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hpoint (v : Fin 10 → ℤ) (hv : v ∈ V) :
      (∑ q ∈ CubeFreeNonzeroAverageReduced.window D, ‖completeCubicSum F q v‖) ≤
        A*(D*H)^ε*D^9 := by
    have hx := (mem_points (OffTerminalFrequencyCertificate.exceptionalSet F) u L m b v).mp hv
    have hv0 : v ≠ 0 := by
      intro hz
      apply hx.2.2.1
      funext i
      simp [hz]
    have hvH := ConductorPositiveMeanNumerics.height_le u L hL m v hx.1
    have hhv : 0 ≤ frequencyHeight v := by dsimp [frequencyHeight]; positivity
    calc
      _ ≤ A*(D*frequencyHeight v)^ε*D^9 := hfixed v hv0 D hD
      _ ≤ A*(D*H)^ε*D^9 := by
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_left _ hA0
          exact Real.rpow_le_rpow (mul_nonneg hD0 hhv)
            (mul_le_mul_of_nonneg_left hvH hD0) hε.le
        · positivity
  have hc : (V.card : ℝ) ≤ K*(1+L/(m : ℝ)) := hcount u L hL m hm b
  calc
    _ ≤ ∑ v ∈ V, A*(D*H)^ε*D^9 := Finset.sum_le_sum hpoint
    _ = (V.card : ℝ)*(A*(D*H)^ε*D^9) := by simp
    _ ≤ (K*(1+L/(m : ℝ)))*(A*(D*H)^ε*D^9) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by dsimp [H]; ring

/-- The listed literature hypotheses and proved interfaces construct the geometric data;
the actual terminal sum itself is proved, not supplied as an input. -/
theorem exists_bound
    (microlocal : Literature.ProjectiveMicrolocalCertificate)
    (spread : CubicPrincipalOpenUniform.Uniform)
    (cubicWeil : Literature.SmoothCubicWeil)
    (isolated : CubicSurfacePointCountReduced.IsolatedConjugateCubicSurfacePointCount)
    (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (D : ℝ) (u : Fin 10 → ℝ) (L : ℝ) (m : ℕ)
      (b : Fin 10 → ℤ), 1 ≤ D → 0 ≤ L → 0 < m →
      (∑ v ∈ points (OffTerminalFrequencyCertificate.exceptionalSet F) u L m b,
        ∑ q ∈ CubeFreeNonzeroAverageReduced.window D, ‖completeCubicSum F q v‖) ≤
        M*(D*(2+‖u‖+L+(m : ℝ)))^ε*(1+L/(m : ℝ))*D^9 := by
  obtain ⟨t,f,N,B,hN,_hB,hgeo,hData⟩ := TenMicrolocalIncidenceData.exists_data
    microlocal F hF hAn
  exact of_data spread cubicWeil isolated pointcount F hF hAn f N B hN hgeo hData ε hε

end CubicTenVariables.TerminalCubeFreeAverageReduced
