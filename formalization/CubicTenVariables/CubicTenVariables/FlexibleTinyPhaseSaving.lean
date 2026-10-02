import CubicTenVariables.LocalizedTinyPhaseSaving
import CubicTenVariables.FlexibleCountingNumerics

/-! The actual complete tiny-phase contribution is O(P^-7) for every
positive integer cutoff Q≤P^(3/2). Every original arc and q=1 are retained.
Only generic Schwartz Poisson and the stated kernel estimates are inputs. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.FlexibleTinyPhaseSaving
open MvPolynomial MeasureTheory DeltaMethod LocalizedPoissonArc LocalizedTinyPhaseSaving
open scoped BigOperators ContDiff

/-- Constants precede P,Q and η, and no lower bound on Q relative to P
is required for this short-interval estimate. -/
theorem exists_bound (lit : Literature.SteinShakarchi2011Poisson)
    (G : MvPolynomial (Fin 10) ℤ) (w : (Fin 10 → ℝ) → ℝ) (A W : ℕ)
    (hw : WeightSupportedInBox w A) (hw0 : w 0=0)
    (hs : ContDiff ℝ ∞ w) (hc : HasCompactSupport w) (hW : 0 < W)
    (M : ℝ) (hM : ∀ y, |w y| ≤ M) (Ω : Set (Fin 10 → ZMod W))
    (p : ℕ → ℕ → ℝ → ℂ) (hp : KernelEstimates 1 p) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P Q : ℕ, 0 < P → 1 ≤ Q →
      (Q:ℝ) ≤ (P:ℝ)^((3:ℝ)/2) → ∀ η : ℝ,
      (∀ q ∈ Finset.Icc 1 Q,
        IntegrableOn (fun θ => p Q q θ*nonzeroContribution G w P q W Ω θ) (region P Q q η)) ∧
      ‖contribution G w P Q W Ω η p‖ ≤ C*(P:ℝ)^(-7:ℝ) := by
  obtain ⟨K,hK,hkernel⟩ := hp.bounded
  let D : ℝ := M*((2*A+1:ℕ):ℝ)^10+∫ x : Fin 10 → ℝ, |w x|
  have hM0 : 0 ≤ M := (abs_nonneg (w 0)).trans (hM 0)
  have hm : 0 ≤ ∫ x : Fin 10 → ℝ, |w x| := integral_nonneg fun _ => abs_nonneg _
  have hD : 0 ≤ D := by dsimp [D]; positivity
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
  apply (FlexibleCountingNumerics.tiny_coefficient_le (P:ℝ) (Q:ℝ) K D
    (by exact_mod_cast hP) (Nat.cast_nonneg Q) hQP (zero_le_one.trans hK) hD).trans
  exact mul_le_mul_of_nonneg_right (le_max_right _ _)
    (Real.rpow_nonneg (Nat.cast_nonneg P) _)

end CubicTenVariables.FlexibleTinyPhaseSaving
