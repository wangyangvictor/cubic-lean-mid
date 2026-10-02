import CubicTenVariables.PeriodicCoefficientPoisson
import CubicTenVariables.LocalizedGeneratingFunction
import CubicTenVariables.OscillatorySchwartz
import CubicTenVariables.LocalizedPoissonCharacter

/-! Poisson summation for the literal localized polynomial generating sum.
The sole literature premise is generic Schwartz Poisson. The lattice,
periodic coefficient, Fourier transform and absolute convergence are
identified here, with the actual common modulus lcm(q,W).
No cubic degree, geometric hypothesis, or arithmetic estimate is needed. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.LocalizedPoisson
open MvPolynomial DeltaMethod OscillatoryLocalization
open scoped BigOperators ContDiff
variable {n : ℕ}

/-- The literal frequency summand, before the covolume normalization. -/
def frequencyTerm (G : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ)
    (P : ℕ) (q W : ℕ) (Ω : Set (Fin n → ZMod W)) (θ : ℝ)
    (v : Fin n → ℤ) : ℂ :=
  localizedCompleteCubicSum G q W Ω v *
    scaledIntegral (map (Int.castRingHom ℝ) G) w (P:ℝ) θ (localizedFrequency q W v)

/-- The compactly supported lattice wave has precisely the source sum. -/
theorem lattice_hasSum (G : MvPolynomial (Fin n) ℤ)
    (w : (Fin n → ℝ) → ℝ) (A P : ℕ)
    (hw : WeightSupportedInBox w A) (hw0 : w 0=0)
    (hs : ContDiff ℝ ∞ w) (hc : HasCompactSupport w) (hP : 0 < P)
    (q W : ℕ) (Ω : Set (Fin n → ZMod W)) (θ : ℝ) :
    HasSum (fun x : Fin n → ℤ => LocalizedPeriodicPhase.coefficient G q W Ω x *
      OscillatorySchwartz.schwartz (map (Int.castRingHom ℝ) G) w (P:ℝ) θ hs hc
        (by exact_mod_cast hP) (fun i => (x i:ℝ)))
      (∑ a : Fin q, if Nat.Coprime a.val q then
        localizedGeneratingSum G w A P W Ω ((a.val:ℝ)/(q:ℝ)+θ) else 0) := by
  simpa only [OscillatorySchwartz.schwartz_apply,OscillatorySchwartz.weight_integer,
    LocalizedGeneratingFunction.sampledPhase] using
    LocalizedGeneratingFunction.hasSum G w A P hw hw0 hP q W Ω θ

/-- Absolute convergence of the literal localized dual series. This does
not assume cancellation of the complete sums or a frequency-tail estimate. -/
theorem summable_norm (lit : Literature.SteinShakarchi2011Poisson)
    (G : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ) (P : ℕ)
    (hs : ContDiff ℝ ∞ w) (hc : HasCompactSupport w) (hP : 0 < P)
    (q W : ℕ) (hq : 0 < q) (hW : 0 < W)
    (Ω : Set (Fin n → ZMod W)) (θ : ℝ) :
    Summable (fun v : Fin n → ℤ => ‖frequencyTerm G w P q W Ω θ v‖) := by
  have h := FiniteCoefficientPoisson.summable_norm_character lit
    (OscillatorySchwartz.schwartz (map (Int.castRingHom ℝ) G) w (P:ℝ) θ hs hc
      (by exact_mod_cast hP)) (Nat.lcm q W:ℝ)
    (by exact_mod_cast Nat.lcm_pos hq hW)
    PeriodicCoefficientPoisson.realRepresentative
    (fun r : Fin n → Fin (Nat.lcm q W) =>
      LocalizedPeriodicPhase.coefficient G q W Ω (IntegerLatticeResidues.representative r))
  simpa only [LocalizedPoissonCharacter.character_eq_localizedCompleteCubicSum,
    OscillatorySchwartz.fourier_eq_scaledIntegral,frequencyTerm,localizedFrequency] using h

/-- Exact Poisson identity for the localized generating sum. The only
unproved input is the displayed general textbook Poisson proposition. -/
theorem identity (lit : Literature.SteinShakarchi2011Poisson)
    (G : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ) (A P : ℕ)
    (hw : WeightSupportedInBox w A) (hw0 : w 0=0)
    (hs : ContDiff ℝ ∞ w) (hc : HasCompactSupport w) (hP : 0 < P)
    (q W : ℕ) (hq : 0 < q) (hW : 0 < W)
    (Ω : Set (Fin n → ZMod W)) (θ : ℝ) :
    (∑ a : Fin q, if Nat.Coprime a.val q then
      localizedGeneratingSum G w A P W Ω ((a.val:ℝ)/(q:ℝ)+θ) else 0) =
      ((Nat.lcm q W:ℂ)^n)⁻¹ * ∑' v : Fin n → ℤ, frequencyTerm G w P q W Ω θ v := by
  have hl := lattice_hasSum G w A P hw hw0 hs hc hP q W Ω θ
  rw [← hl.tsum_eq]
  have h := PeriodicCoefficientPoisson.identity lit
    (OscillatorySchwartz.schwartz (map (Int.castRingHom ℝ) G) w (P:ℝ) θ hs hc
      (by exact_mod_cast hP)) (Nat.lcm q W) (Nat.lcm_pos hq hW)
    (LocalizedPeriodicPhase.coefficient G q W Ω) (fun r z =>
      LocalizedPeriodicPhase.coefficient_lattice_translate G q W (Nat.lcm q W) hq
        (Nat.dvd_lcm_left q W) (Nat.dvd_lcm_right q W) Ω
        (IntegerLatticeResidues.representative r) z) hl.summable
  simpa only [LocalizedPoissonCharacter.character_eq_localizedCompleteCubicSum,
    OscillatorySchwartz.fourier_eq_scaledIntegral,frequencyTerm,localizedFrequency] using h

/-- Removal of precisely the zero vector from the convergent frequency
series. The zero-frequency term is still an exact integral, not an asymptotic. -/
theorem split_zero (lit : Literature.SteinShakarchi2011Poisson)
    (G : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ) (P : ℕ)
    (hs : ContDiff ℝ ∞ w) (hc : HasCompactSupport w) (hP : 0 < P)
    (q W : ℕ) (hq : 0 < q) (hW : 0 < W)
    (Ω : Set (Fin n → ZMod W)) (θ : ℝ) :
    (∑' v : Fin n → ℤ, frequencyTerm G w P q W Ω θ v) =
      frequencyTerm G w P q W Ω θ 0 +
      ∑' v : Fin n → ℤ, if v=0 then 0 else frequencyTerm G w P q W Ω θ v := by
  classical
  exact (summable_norm lit G w P hs hc hP q W hq hW Ω θ).of_norm.tsum_eq_add_tsum_ite 0

end CubicTenVariables.LocalizedPoisson
