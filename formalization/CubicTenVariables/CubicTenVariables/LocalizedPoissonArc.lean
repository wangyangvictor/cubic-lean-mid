import CubicTenVariables.LocalizedPoisson
import CubicTenVariables.LocalizedGeneratingArc
import CubicTenVariables.DyadicFrequencyError

/-! Exact zero/nonzero decomposition on the genuine clipped delta-method
arcs. Every arc integrand is proved integrable. The infinite frequency sum
stays inside the integral; interchanging it with integration, and estimating
the resulting global remainder, are separate obligations. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.LocalizedPoissonArc
open MvPolynomial MeasureTheory DeltaMethod LocalizedPoisson
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def zeroContribution (G : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ)
    (P q W : ℕ) (Ω : Set (Fin n → ZMod W)) (θ : ℝ) : ℂ :=
  ((Nat.lcm q W:ℂ)^n)⁻¹ * frequencyTerm G w P q W Ω θ 0

def nonzeroContribution (G : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ)
    (P q W : ℕ) (Ω : Set (Fin n → ZMod W)) (θ : ℝ) : ℂ :=
  ((Nat.lcm q W:ℂ)^n)⁻¹ *
    ∑' v : Fin n → ℤ, if v=0 then 0 else frequencyTerm G w P q W Ω θ v

theorem identity_split (lit : Literature.SteinShakarchi2011Poisson)
    (G : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ) (A P : ℕ)
    (hw : WeightSupportedInBox w A) (hw0 : w 0=0)
    (hs : ContDiff ℝ ∞ w) (hc : HasCompactSupport w) (hP : 0 < P)
    (q W : ℕ) (hq : 0 < q) (hW : 0 < W)
    (Ω : Set (Fin n → ZMod W)) (θ : ℝ) :
    (∑ a : Fin q, if Nat.Coprime a.val q then
      localizedGeneratingSum G w A P W Ω ((a.val:ℝ)/(q:ℝ)+θ) else 0) =
      zeroContribution G w P q W Ω θ + nonzeroContribution G w P q W Ω θ := by
  rw [LocalizedPoisson.identity lit G w A P hw hw0 hs hc hP q W hq hW Ω θ,
    LocalizedPoisson.split_zero lit G w P hs hc hP q W hq hW Ω θ,mul_add]
  rfl

theorem continuous_zero (G : MvPolynomial (Fin n) ℤ)
    (w : (Fin n → ℝ) → ℝ) (hw : Continuous w) (hc : HasCompactSupport w)
    (P q W : ℕ) (hP : 0 < P) (Ω : Set (Fin n → ZMod W)) :
    Continuous (zeroContribution G w P q W Ω) := by
  exact continuous_const.mul (continuous_const.mul
    (DyadicFrequencyError.continuous_scaledIntegral _ w hw hc (P:ℝ)
      (by exact_mod_cast hP.ne') (localizedFrequency q W 0)))

/-- Continuity of the actual infinite nonzero-frequency contribution is
deduced from the exact Poisson identity, not from a presumed uniform tail. -/
theorem continuous_nonzero (lit : Literature.SteinShakarchi2011Poisson)
    (G : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ) (A P : ℕ)
    (hw : WeightSupportedInBox w A) (hw0 : w 0=0)
    (hs : ContDiff ℝ ∞ w) (hc : HasCompactSupport w) (hP : 0 < P)
    (q W : ℕ) (hq : 0 < q) (hW : 0 < W) (Ω : Set (Fin n → ZMod W)) :
    Continuous (nonzeroContribution G w P q W Ω) := by
  have he : nonzeroContribution G w P q W Ω = fun θ =>
      (∑ a : Fin q, if Nat.Coprime a.val q then
        localizedGeneratingSum G w A P W Ω ((a.val:ℝ)/(q:ℝ)+θ) else 0) -
        zeroContribution G w P q W Ω θ := by
    funext θ
    rw [identity_split lit G w A P hw hw0 hs hc hP q W hq hW Ω θ]
    abel
  rw [he]
  exact (LocalizedGeneratingArc.continuous_numerator_sum G w A P q W Ω).sub
    (continuous_zero G w hs.continuous hc P q W hP Ω)

theorem integrableOn_zero (G : MvPolynomial (Fin n) ℤ)
    (w : (Fin n → ℝ) → ℝ) (hw : Continuous w) (hc : HasCompactSupport w)
    (P Q q W : ℕ) (hP : 0 < P) (Ω : Set (Fin n → ZMod W))
    (η : ℝ) (p : ℕ → ℕ → ℝ → ℂ) (hp : Continuous (p Q q)) :
    IntegrableOn (fun θ => p Q q θ*zeroContribution G w P q W Ω θ) (arc Q q η) := by
  rw [arc_eq_Ioo]
  exact (hp.mul (continuous_zero G w hw hc P q W hP Ω)).integrableOn_Icc.mono_set
    Set.Ioo_subset_Icc_self

theorem integrableOn_nonzero (lit : Literature.SteinShakarchi2011Poisson)
    (G : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ) (A P : ℕ)
    (hw : WeightSupportedInBox w A) (hw0 : w 0=0)
    (hs : ContDiff ℝ ∞ w) (hc : HasCompactSupport w) (hP : 0 < P)
    (Q q W : ℕ) (hq : 0 < q) (hW : 0 < W) (Ω : Set (Fin n → ZMod W))
    (η : ℝ) (p : ℕ → ℕ → ℝ → ℂ) (hp : Continuous (p Q q)) :
    IntegrableOn (fun θ => p Q q θ*nonzeroContribution G w P q W Ω θ) (arc Q q η) := by
  rw [arc_eq_Ioo]
  exact (hp.mul (continuous_nonzero lit G w A P hw hw0 hs hc hP q W hq hW Ω)).integrableOn_Icc.mono_set
    Set.Ioo_subset_Icc_self

/-- Exact arc decomposition with the source's original numerator interval.
Both integrals are convergent; no phase endpoint or q=1 term is discarded. -/
theorem arc_decomposition (lit : Literature.SteinShakarchi2011Poisson)
    (G : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ) (A P : ℕ)
    (hw : WeightSupportedInBox w A) (hw0 : w 0=0)
    (hs : ContDiff ℝ ∞ w) (hc : HasCompactSupport w) (hP : 0 < P)
    (Q q W : ℕ) (hq : 0 < q) (hW : 0 < W) (Ω : Set (Fin n → ZMod W))
    (η : ℝ) (p : ℕ → ℕ → ℝ → ℂ) (hp : Continuous (p Q q)) :
    (∑ a ∈ Finset.Icc 1 q, if Nat.Coprime a q then
      ∫ θ in arc Q q η, p Q q θ *
        localizedGeneratingSum G w A P W Ω ((a:ℝ)/(q:ℝ)+θ) else 0) =
      (∫ θ in arc Q q η, p Q q θ*zeroContribution G w P q W Ω θ) +
      ∫ θ in arc Q q η, p Q q θ*nonzeroContribution G w P q W Ω θ := by
  rw [LocalizedGeneratingArc.sum_Icc_integrals_eq_integral_sum G w A P Q q W hq Ω η p hp]
  simp_rw [identity_split lit G w A P hw hw0 hs hc hP q W hq hW Ω,mul_add]
  exact integral_add (integrableOn_zero G w hs.continuous hc P Q q W hP Ω η p hp)
    (integrableOn_nonzero lit G w A P hw hw0 hs hc hP Q q W hq hW Ω η p hp)

end CubicTenVariables.LocalizedPoissonArc
