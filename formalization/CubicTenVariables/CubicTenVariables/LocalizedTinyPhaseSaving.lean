import CubicTenVariables.LocalizedTinyPhase
import CubicTenVariables.TinyPhaseNumerics

/-! The entire tiny-phase interval, including q=1, contributes O(P^-7)
at Q=P^(3/2). This uses the finite physical generating sum and the zero
mode. No shifted-average hypothesis or oscillatory localization input is
needed; generic Poisson is the sole explicit literature premise. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.LocalizedTinyPhaseSaving
open MvPolynomial MeasureTheory DeltaMethod LocalizedPoissonArc
open scoped BigOperators ContDiff

def region (P Q q : ℕ) (η : ℝ) : Set ℝ :=
  Set.Icc (-((P:ℝ)^(-20:ℝ))) ((P:ℝ)^(-20:ℝ)) ∩ arc Q q η

def contribution (G : MvPolynomial (Fin 10) ℤ) (w : (Fin 10 → ℝ) → ℝ)
    (P Q W : ℕ) (Ω : Set (Fin 10 → ZMod W)) (η : ℝ)
    (p : ℕ → ℕ → ℝ → ℂ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 Q, ∫ θ in region P Q q η, p Q q θ*nonzeroContribution G w P q W Ω θ

/-- Constants precede P,Q and η. The actual phase interval is clipped to
every original kernel arc, and all positive moduli up to Q are retained. -/
theorem exists_bound (lit : Literature.SteinShakarchi2011Poisson)
    (G : MvPolynomial (Fin 10) ℤ) (w : (Fin 10 → ℝ) → ℝ) (A W : ℕ)
    (hw : WeightSupportedInBox w A) (hw0 : w 0=0)
    (hs : ContDiff ℝ ∞ w) (hc : HasCompactSupport w) (hW : 0 < W)
    (M : ℝ) (hM : ∀ y, |w y| ≤ M) (Ω : Set (Fin 10 → ZMod W))
    (p : ℕ → ℕ → ℝ → ℂ) (hp : KernelEstimates 1 p) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P Q : ℕ, 0 < P → 1 ≤ Q →
      (Q:ℝ)=(P:ℝ)^((3:ℝ)/2) → ∀ η : ℝ,
      (∀ q ∈ Finset.Icc 1 Q,
        IntegrableOn (fun θ => p Q q θ*nonzeroContribution G w P q W Ω θ) (region P Q q η)) ∧
      ‖contribution G w P Q W Ω η p‖ ≤ C*(P:ℝ)^(-7:ℝ) := by
  obtain ⟨K,hK,hkernel⟩ := hp.bounded
  let D : ℝ := M*((2*A+1:ℕ):ℝ)^10+∫ x : Fin 10 → ℝ, |w x|
  refine ⟨max 1 (2*K*D),le_max_left _ _,?_⟩
  intro P Q hP hQ hQP η
  have ht := LocalizedTinyPhase.sum_integrableOn_and_norm_le lit G w A P hw hw0 hs hc
    M hM hP Q W hW Ω (p Q) K ((P:ℝ)^(-20:ℝ)) (zero_le_one.trans hK)
    (Real.rpow_nonneg (Nat.cast_nonneg P) _) (fun q => region P Q q η)
    (fun q hq => (hp.smooth Q hQ q (Finset.mem_Icc.mp hq).1 (Finset.mem_Icc.mp hq).2).continuous)
    (fun _ _ => Set.inter_subset_left)
    (fun q hq θ _ => hkernel Q hQ q (Finset.mem_Icc.mp hq).1 (Finset.mem_Icc.mp hq).2 θ)
  refine ⟨ht.1,ht.2.trans ?_⟩
  change 2*(P:ℝ)^(-20:ℝ)*K*(Q:ℝ)^2*(P:ℝ)^10*D ≤ _
  rw [TinyPhaseNumerics.coefficient_identity (P:ℝ) (Q:ℝ) K D (by exact_mod_cast hP) hQP]
  exact mul_le_mul_of_nonneg_right (le_max_right _ _)
    (Real.rpow_nonneg (Nat.cast_nonneg P) _)

end CubicTenVariables.LocalizedTinyPhaseSaving
