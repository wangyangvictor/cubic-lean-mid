import CubicTenVariables.LocalizedFiniteBlockAssembly
import CubicTenVariables.SingletonNonzeroFrequencySaving

/-! The literal modulus-one clipped counting block inherits the proved
singleton error saving. Every positive phase width is covered, including
empty clipped arcs outside the admissible range. No arithmetic average or
Poisson premise is used; cubic localization is proved internally.
The kernel and its stated estimates are fixed before all saving constants. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.SingletonClippedSaving
open MvPolynomial MeasureTheory DeltaMethod RealRegularGradientChart DyadicFrequencyError
open LocalizedFiniteBlockAssembly LocalizedClippedFrequency

/-- A nonempty clipped modulus-one arc forces its exact phase range. -/
theorem phase_le_of_mem (P φ η : ℝ) (Q : ℕ)
    (hQ : (Q:ℝ)=P^((3:ℝ)/2)) {θ : ℝ}
    (hθ : θ ∈ shell φ ∩ arc Q 1 η) :
    φ ≤ (P^((3:ℝ)/2))^(-1+η) := by
  have hb : |θ| < (P^((3:ℝ)/2))^(-1+η) := by
    simpa only [arc,Set.mem_setOf_eq,Nat.cast_one,one_mul,hQ] using hθ.2
  exact (hθ.1.1.trans hb).le

/-- The inadmissible phase widths give an empty actual modulus-one block. -/
theorem oneBlock_eq_zero_of_not_le (G : MvPolynomial (Fin 10) ℤ)
    (w : (Fin 10 → ℝ) → ℝ) (P Q W : ℕ) (Ω : Set (Fin 10 → ZMod W))
    (φ η : ℝ) (p : ℕ → ℕ → ℝ → ℂ)
    (hQ : (Q:ℝ)=(P:ℝ)^((3:ℝ)/2))
    (hφ : ¬ φ ≤ ((P:ℝ)^((3:ℝ)/2))^(-1+η)) :
    oneBlock G w P Q W Ω φ η p=0 := by
  have he : shell φ ∩ arc Q 1 η=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro θ hθ
    exact hφ (phase_le_of_mem (P:ℝ) φ η Q hQ hθ)
  simp [oneBlock,he]

/-- The actual clipped integral is bounded by the exact singleton mass,
with lcm(1,W)=W and its full covolume normalization. -/
theorem oneBlock_le_error (G : MvPolynomial (Fin 10) ℤ)
    (w : (Fin 10 → ℝ) → ℝ) (hw : Continuous w) (hc : HasCompactSupport w)
    (P Q W : ℕ) (hP : 0 < P) (Ω : Set (Fin 10 → ZMod W))
    (φ η : ℝ) (p : ℕ → ℕ → ℝ → ℂ) (hp : Measurable (p Q 1))
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ θ ∈ shell φ ∩ arc Q 1 η, ‖p Q 1 θ‖ ≤ K)
    (hsum : Summable (LocalizedDyadicFrequencyError.term G W Ω w (P:ℝ) φ 1)) :
    ‖oneBlock G w P Q W Ω φ η p‖ ≤
      K*SingletonFrequencyTruncation.error G W Ω w (P:ℝ) φ := by
  simpa only [oneBlock,SingletonFrequencyTruncation.error,Nat.lcm_one_left] using
    clipped_bound G w hw hc P 1 W hP Ω φ (shell φ ∩ arc Q 1 η)
      Set.inter_subset_left (p Q 1) hp K hK hbound hsum

/-- Uniform actual clipped q=1 saving, with all positive phase widths and
constants chosen before P,Q,φ,η. The singleton needs no shifted-average
assumption. All convergence needed by the clipping step is proved upstream. -/
theorem exists_power_saving 
    (G : MvPolynomial (Fin 10) ℤ) (hG : G.IsHomogeneous 3)
    (D : Data (map (Int.castRingHom ℝ) G)) (W : ℕ) (hW : 0 < W)
    (Ω : Set (Fin 10 → ZMod W))
    (p : ℕ → ℕ → ℝ → ℂ) (hp : KernelEstimates 1 p) :
    ∃ δ η₀ C P₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1 ∧ 1 ≤ C ∧ 4 ≤ P₀ ∧
      ∀ P Q : ℕ, P₀ ≤ (P:ℝ) → 1 ≤ Q → (Q:ℝ)=(P:ℝ)^((3:ℝ)/2) →
      ∀ φ η : ℝ, 0 < φ → 0 ≤ η → η ≤ η₀ →
        ‖oneBlock G D.weight.weight P Q W Ω φ η p‖ ≤ C*(P:ℝ)^(7-δ) := by
  obtain ⟨δ,η₀,C,P₀,hδ,hη₀,hη1,hC,hP₀,hbound⟩ :=
    SingletonNonzeroFrequencySaving.exists_power_saving G hG D W hW Ω
  obtain ⟨K,hK,hkernel⟩ := hp.bounded
  refine ⟨δ,η₀,K*C,P₀,hδ,hη₀,hη1,one_le_mul_of_one_le_of_one_le hK hC,hP₀,?_⟩
  intro P Q hP hQ hQP φ η hφ hη hηmax
  have hPpos : 0 < P := by
    have : (0:ℝ) < P := by linarith
    exact_mod_cast this
  by_cases hphase : φ ≤ ((P:ℝ)^((3:ℝ)/2))^(-1+η)
  · obtain ⟨hsum,he⟩ := hbound (P:ℝ) φ η hP hφ hη hηmax hphase
    have hc := oneBlock_le_error G D.weight.weight D.weight.smooth.continuous D.weight.compact
      P Q W hPpos Ω φ η p (hp.smooth Q hQ 1 le_rfl hQ).continuous.measurable K
      (zero_le_one.trans hK) (fun θ _ => hkernel Q hQ 1 le_rfl hQ θ) hsum
    exact hc.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left he (zero_le_one.trans hK))
  · rw [oneBlock_eq_zero_of_not_le G D.weight.weight P Q W Ω φ η p hQP hphase,norm_zero]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg P) _)

end CubicTenVariables.SingletonClippedSaving
