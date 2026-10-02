import CubicTenVariables.LocalizedPoissonArc
import CubicTenVariables.LocalizedDyadicFrequencyError
import CubicTenVariables.SummableIntegralMajorant

/-! The actual nonzero-frequency contribution on a clipped phase shell is
bounded by the previously defined dyadic error. Absolute convergence of
the shell masses is an explicit premise, supplied by the proved localized
analytic saving. No global shell summation is asserted in this module. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.LocalizedClippedFrequency
open MvPolynomial MeasureTheory DeltaMethod LocalizedPoisson LocalizedPoissonArc
open DyadicFrequencyError
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def nonzeroFrequencyTerm (G : MvPolynomial (Fin 10) ℤ) (w : (Fin 10 → ℝ) → ℝ)
    (P q W : ℕ) (Ω : Set (Fin 10 → ZMod W)) (v : Fin 10 → ℤ) (θ : ℝ) : ℂ :=
  if v=0 then 0 else frequencyTerm G w P q W Ω θ v

theorem continuous_term (G : MvPolynomial (Fin 10) ℤ)
    (w : (Fin 10 → ℝ) → ℝ) (hw : Continuous w) (hc : HasCompactSupport w)
    (P q W : ℕ) (hP : 0 < P) (Ω : Set (Fin 10 → ZMod W)) (v : Fin 10 → ℤ) :
    Continuous (nonzeroFrequencyTerm G w P q W Ω v) := by
  unfold nonzeroFrequencyTerm
  split_ifs
  · exact continuous_const
  · exact continuous_const.mul (continuous_scaledIntegral _ w hw hc (P:ℝ)
      (by exact_mod_cast hP.ne') (localizedFrequency q W v))

theorem integrableOn_term (G : MvPolynomial (Fin 10) ℤ)
    (w : (Fin 10 → ℝ) → ℝ) (hw : Continuous w) (hc : HasCompactSupport w)
    (P q W : ℕ) (hP : 0 < P) (Ω : Set (Fin 10 → ZMod W))
    (v : Fin 10 → ℤ) (φ : ℝ) :
    IntegrableOn (nonzeroFrequencyTerm G w P q W Ω v) (shell φ) :=
  (continuous_term G w hw hc P q W hP Ω v).integrableOn_Icc.mono_set
    (shell_subset_Icc φ)

/-- The mass of the literal oscillatory summand is precisely the existing
localized dyadic mass, with denominator lcm(q,W) and zero removed. -/
theorem norm_integral_eq_term (G : MvPolynomial (Fin 10) ℤ)
    (w : (Fin 10 → ℝ) → ℝ) (P q W : ℕ) (Ω : Set (Fin 10 → ZMod W))
    (v : Fin 10 → ℤ) (φ : ℝ) :
    (∫ θ in shell φ, ‖nonzeroFrequencyTerm G w P q W Ω v θ‖) =
      LocalizedDyadicFrequencyError.term G W Ω w (P:ℝ) φ q v := by
  by_cases hv : v=0
  · simp [nonzeroFrequencyTerm,LocalizedDyadicFrequencyError.term,hv]
  · simp only [nonzeroFrequencyTerm,if_neg hv,frequencyTerm,norm_mul,
      LocalizedDyadicFrequencyError.term,frequencyMass,LocalizedFrequencyComparison.frequency_eq]
    exact integral_const_mul _ _

/-- A bounded kernel on any part of the shell is controlled by the actual
localized shell mass. The covolume factor is retained exactly. -/
theorem clipped_bound (G : MvPolynomial (Fin 10) ℤ)
    (w : (Fin 10 → ℝ) → ℝ) (hw : Continuous w) (hc : HasCompactSupport w)
    (P q W : ℕ) (hP : 0 < P) (Ω : Set (Fin 10 → ZMod W)) (φ : ℝ)
    (S : Set ℝ) (hS : S ⊆ shell φ) (k : ℝ → ℂ) (hk : Measurable k)
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ θ ∈ S, ‖k θ‖ ≤ K)
    (hsum : Summable (LocalizedDyadicFrequencyError.term G W Ω w (P:ℝ) φ q)) :
    ‖∫ θ in S, k θ*nonzeroContribution G w P q W Ω θ‖ ≤
      K * (((Nat.lcm q W:ℝ)^10)⁻¹ *
        ∑' v : Fin 10 → ℤ, LocalizedDyadicFrequencyError.term G W Ω w (P:ℝ) φ q v) := by
  have hm : Summable (fun v : Fin 10 → ℤ =>
      ∫ θ in shell φ, ‖nonzeroFrequencyTerm G w P q W Ω v θ‖) := by
    simpa only [norm_integral_eq_term] using hsum
  have hb := (SummableIntegralMajorant.clipped_kernel_bound hS
    (nonzeroFrequencyTerm G w P q W Ω)
    (fun v => integrableOn_term G w hw hc P q W hP Ω v φ)
    hm k hk K hK hbound).2
  simp only [norm_integral_eq_term] at hb
  calc
    _ = ‖((Nat.lcm q W:ℂ)^10)⁻¹ *
        ∫ θ in S, k θ*∑' v : Fin 10 → ℤ, nonzeroFrequencyTerm G w P q W Ω v θ‖ := by
      congr 1
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with θ
      unfold nonzeroContribution nonzeroFrequencyTerm
      ring
    _ = ((Nat.lcm q W:ℝ)^10)⁻¹ *
        ‖∫ θ in S, k θ*∑' v : Fin 10 → ℤ, nonzeroFrequencyTerm G w P q W Ω v θ‖ := by
      rw [norm_mul,norm_inv,norm_pow,Complex.norm_natCast]
    _ ≤ ((Nat.lcm q W:ℝ)^10)⁻¹ *
        (K * ∑' v : Fin 10 → ℤ, LocalizedDyadicFrequencyError.term G W Ω w (P:ℝ) φ q v) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- One actual block, clipped both to q≤Q and to each q-dependent arc. -/
def block (G : MvPolynomial (Fin 10) ℤ) (w : (Fin 10 → ℝ) → ℝ)
    (P Q W : ℕ) (Ω : Set (Fin 10 → ZMod W)) (R φ η : ℝ)
    (p : ℕ → ℕ → ℝ → ℂ) : ℂ :=
  ∑ q ∈ moduli R, if q ≤ Q then
    ∫ θ in shell φ ∩ arc Q q η, p Q q θ*nonzeroContribution G w P q W Ω θ else 0

/-- The clipped counting block costs at most the kernel bound times the
literal dyadic error whose power saving was already proved. -/
theorem block_bound (G : MvPolynomial (Fin 10) ℤ)
    (w : (Fin 10 → ℝ) → ℝ) (hw : Continuous w) (hc : HasCompactSupport w)
    (P Q W : ℕ) (hP : 0 < P) (Ω : Set (Fin 10 → ZMod W)) (R φ η : ℝ)
    (p : ℕ → ℕ → ℝ → ℂ) (K : ℝ) (hK : 0 ≤ K)
    (hp : ∀ q ∈ moduli R, q ≤ Q → Measurable (p Q q))
    (hb : ∀ q ∈ moduli R, q ≤ Q → ∀ θ ∈ shell φ ∩ arc Q q η, ‖p Q q θ‖ ≤ K)
    (hsum : ∀ q ∈ moduli R,
      Summable (LocalizedDyadicFrequencyError.term G W Ω w (P:ℝ) φ q)) :
    ‖block G w P Q W Ω R φ η p‖ ≤
      K*LocalizedFrequencyComparison.error G W Ω w (P:ℝ) R φ := by
  unfold block
  rw [LocalizedDyadicFrequencyError.error_eq_sum,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro q hq
  by_cases hqQ : q ≤ Q
  · simp only [if_pos hqQ]
    exact clipped_bound G w hw hc P q W hP Ω φ (shell φ ∩ arc Q q η)
      Set.inter_subset_left (p Q q) (hp q hq hqQ) K hK (hb q hq hqQ) (hsum q hq)
  · simp only [if_neg hqQ,norm_zero]
    exact mul_nonneg hK (mul_nonneg (by positivity)
      (tsum_nonneg (LocalizedDyadicFrequencyError.term_nonneg G W Ω w (P:ℝ) φ q)))

end CubicTenVariables.LocalizedClippedFrequency
