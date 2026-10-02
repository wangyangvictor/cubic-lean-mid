import CubicTenVariables.LocalizedFiniteBlockAssembly
import CubicTenVariables.FlexibleClippedSaving
import CubicTenVariables.FlexibleTinyPhaseSaving
import CubicTenVariables.GlobalCountingNumerics
import CubicTenVariables.CountingArcGeometry

/-! Global power saving for the actual localized nonzero-frequency
contribution. A finite exact partition combines the tiny interval, the
modulus-one blocks and all remaining clipped blocks. The arithmetic shifted
average remains explicit; Poisson summation is the remaining named input. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.LocalizedGlobalNonzeroSaving
open MvPolynomial DeltaMethod RealRegularGradientChart LocalizedShiftedWindow
open LocalizedFiniteBlockAssembly
open scoped BigOperators

/-- One kernel family precedes the constants; the saving is uniform for
small nonnegative arc and scale losses η,ν and every admissible natural Q. -/
theorem exists_power_saving (poisson : Literature.SteinShakarchi2011Poisson)
    
    (G : MvPolynomial (Fin 10) ℤ) (hG : G.IsHomogeneous 3)
    (D : Data (map (Int.castRingHom ℝ) G)) (W : ℕ) (hW : 0 < W)
    (Ω : Set (Fin 10 → ZMod W)) (b : ℝ) (hb : b < 20/3)
    (hshift : CleanShiftedAverage G W Ω b)
    (p : ℕ → ℕ → ℝ → ℂ) (hp : KernelEstimates 1 p) :
    ∃ δ η₀ C P₀ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧ 1 ≤ C ∧ 4 ≤ P₀ ∧
      ∀ P Q : ℕ, P₀ ≤ (P:ℝ) → 1 ≤ Q → ∀ ν : ℝ, 0 ≤ ν →
      (P:ℝ)^((3:ℝ)/2-ν) ≤ (Q:ℝ) → (Q:ℝ) ≤ (P:ℝ)^((3:ℝ)/2) →
      ∀ η : ℝ, 0 ≤ η → η+ν ≤ η₀ →
        ‖LocalizedPoissonCount.nonzeroTerm G D.weight.weight P Q W Ω η p‖ ≤
          C*(P:ℝ)^(7-δ) := by
  obtain ⟨δb,ηb,Cb,Pb,hδb,hηb,hηb1,hCb,hPb,hblock⟩ :=
    FlexibleClippedSaving.exists_block_power_saving G hG D W hW Ω b hb hshift p hp
  obtain ⟨δs,ηs,Cs,Ps,hδs,hηs,hηs1,hCs,hPs,hsingle⟩ :=
    FlexibleClippedSaving.exists_one_power_saving G hG D W hW Ω p hp
  have hweight (y : Fin 10 → ℝ) : |D.weight.weight y| ≤ 1 := by
    rw [abs_of_nonneg (D.weight.bounds y).1]
    exact (D.weight.bounds y).2
  obtain ⟨Ct,hCt,htiny⟩ := FlexibleTinyPhaseSaving.exists_bound poisson G D.weight.weight
    D.weight.boxRadius W D.weight.supported D.weight.zero_at_origin
    D.weight.smooth D.weight.compact hW 1 hweight Ω p hp
  let d : ℝ := min 1 (min δb δs)
  have hd : 0 < d := lt_min zero_lt_one (lt_min hδb hδs)
  have hd1 : d ≤ 1 := min_le_left _ _
  have hdb : d ≤ δb := (min_le_right _ _).trans (min_le_left _ _)
  have hds : d ≤ δs := (min_le_right _ _).trans (min_le_right _ _)
  let C0 : ℝ := max Cb Cs
  have hC0 : 1 ≤ C0 := hCb.trans (le_max_left _ _)
  obtain ⟨Ca,hCa,habs⟩ := GlobalCountingNumerics.exists_global_block_absorption d hd
  refine ⟨d/2,min ηb ηs,Ct+C0*Ca,max Pb Ps,by positivity,by linarith,
    lt_min hηb hηs,(min_le_left _ _).trans hηb1,
    by nlinarith only [hCt,hC0,hCa],hPb.trans (le_max_left _ _),?_⟩
  intro P Q hP hQ ν hν hQlo hQhi η hη hηmax
  have hP4 : (4:ℝ) ≤ P := (hPb.trans (le_max_left _ _)).trans hP
  have hP1 : (1:ℝ) ≤ P := by linarith
  have hPpos : 0 < P := by exact_mod_cast (zero_lt_one.trans_le hP1)
  have hηb' : η+ν ≤ ηb := hηmax.trans (min_le_left _ _)
  have hηs' : η+ν ≤ ηs := hηmax.trans (min_le_right _ _)
  have hη1 : η ≤ 1 := by linarith
  have hcommon (a c : ℝ) (hda : d ≤ a) (hc : c ≤ C0) :
      c*(P:ℝ)^(7-a) ≤ C0*(P:ℝ)^(7-d) := by
    apply (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (Nat.cast_nonneg P) _)).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)) (zero_le_one.trans hC0)
  have hone (k : ℕ) (_hk : k ∈ Finset.range (FiniteDyadicPhases.count P)) :
      ‖oneBlock G D.weight.weight P Q W Ω
        (FiniteDyadicPhases.radius ((P:ℝ)^(-20:ℝ)) k) η p‖ ≤ C0*(P:ℝ)^(7-d) := by
    apply (hsingle P Q ((le_max_right _ _).trans hP) hQ ν hν hQlo hQhi
      (FiniteDyadicPhases.radius ((P:ℝ)^(-20:ℝ)) k) η
      (FiniteDyadicPhases.radius_pos _ (Real.rpow_pos_of_pos (by positivity) _) k)
      hη hηs').trans
    exact hcommon δs Cs hds (le_max_right _ _)
  have hbnd (j : ℕ) (hj : j ∈ Finset.range (FiniteDyadicModuli.count Q))
      (k : ℕ) (_hk : k ∈ Finset.range (FiniteDyadicPhases.count P)) :
      ‖LocalizedClippedFrequency.block G D.weight.weight P Q W Ω ((2:ℝ)^j)
        (FiniteDyadicPhases.radius ((P:ℝ)^(-20:ℝ)) k) η p‖ ≤ C0*(P:ℝ)^(7-d) := by
    have hr := CountingArcGeometry.dyadic_scale_bounds Q j hQ (Finset.mem_range.mp hj)
    apply (hblock P Q ((le_max_left _ _).trans hP) hQ ν hν hQlo hQhi ((2:ℝ)^j)
      (FiniteDyadicPhases.radius ((P:ℝ)^(-20:ℝ)) k) η hr.1 (hr.2.trans hQhi)
      (FiniteDyadicPhases.radius_pos _ (Real.rpow_pos_of_pos (by positivity) _) k) hη hηb').trans
    exact hcommon δb Cb hdb (le_max_left _ _)
  have ht := (htiny P Q hPpos hQ hQhi η).2
  have ha := norm_le_of_block_bounds poisson G D.weight.weight D.weight.boxRadius P
    D.weight.supported D.weight.zero_at_origin D.weight.smooth D.weight.compact hPpos
    Q W hQ hW Ω η hη1 p hp (Ct*(P:ℝ)^(-7:ℝ)) (C0*(P:ℝ)^(7-d)) ht hone hbnd
  have habsP := habs P Q hPpos hQ hQhi
  have htinyP : (P:ℝ)^(-7:ℝ) ≤ (P:ℝ)^(7-d/2) :=
    Real.rpow_le_rpow_of_exponent_le hP1 (by linarith only [hd1])
  apply ha.trans
  calc
    _ = Ct*(P:ℝ)^(-7:ℝ) + C0*
        ((((Nat.log 2 Q+2)*(Nat.log 2 (P^20)+1):ℕ):ℝ)*(P:ℝ)^(7-d)) := by ring
    _ ≤ Ct*(P:ℝ)^(7-d/2)+C0*(Ca*(P:ℝ)^(7-d/2)) :=
      add_le_add (mul_le_mul_of_nonneg_left htinyP (zero_le_one.trans hCt))
        (mul_le_mul_of_nonneg_left habsP (zero_le_one.trans hC0))
    _ = _ := by ring

end CubicTenVariables.LocalizedGlobalNonzeroSaving
