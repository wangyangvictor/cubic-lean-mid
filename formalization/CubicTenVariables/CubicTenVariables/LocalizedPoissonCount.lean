import CubicTenVariables.LocalizedPoissonArc
import CubicTenVariables.ConstructedDeltaSource

/-! The actual localized count equals the exact zero-frequency contribution
plus the exact nonzero-frequency contribution and the scalar delta error.
Delta kernels are constructed internally; general Schwartz Poisson remains
an explicit premise of this wrapper. Neither a positive main-term asymptotic nor a power-saving
bound on the global nonzero contribution is asserted here. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.LocalizedPoissonCount
open MvPolynomial MeasureTheory DeltaMethod LocalizedPoissonArc
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def zeroTerm (G : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ)
    (P Q W : ℕ) (Ω : Set (Fin n → ZMod W)) (η : ℝ)
    (p : ℕ → ℕ → ℝ → ℂ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 Q, ∫ θ in arc Q q η, p Q q θ*zeroContribution G w P q W Ω θ

def nonzeroTerm (G : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ)
    (P Q W : ℕ) (Ω : Set (Fin n → ZMod W)) (η : ℝ)
    (p : ℕ → ℕ → ℝ → ℂ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 Q, ∫ θ in arc Q q η, p Q q θ*nonzeroContribution G w P q W Ω θ

/-- Exact decomposition of every term in the source's delta approximation,
including q=1 and the clipped arcs. -/
theorem approximation_eq (lit : Literature.SteinShakarchi2011Poisson)
    (G : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ) (A P : ℕ)
    (hw : WeightSupportedInBox w A) (hw0 : w 0=0)
    (hs : ContDiff ℝ ∞ w) (hc : HasCompactSupport w) (hP : 0 < P)
    (Q W : ℕ) (hW : 0 < W) (Ω : Set (Fin n → ZMod W)) (η : ℝ)
    (p : ℕ → ℕ → ℝ → ℂ) (hp : ∀ q ∈ Finset.Icc 1 Q, Continuous (p Q q)) :
    (∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ Finset.Icc 1 q, if Nat.Coprime a q then
      ∫ θ in arc Q q η, p Q q θ *
        localizedGeneratingSum G w A P W Ω ((a:ℝ)/(q:ℝ)+θ) else 0) =
      zeroTerm G w P Q W Ω η p + nonzeroTerm G w P Q W Ω η p := by
  unfold zeroTerm nonzeroTerm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  exact arc_decomposition lit G w A P hw hw0 hs hc hP Q q W
    (Finset.mem_Icc.mp hq).1 hW Ω η p (hp q hq)

/-- A single kernel family precedes η, N and the physical scales. The only
error estimated here is the inherited P^n Q^(-Nη) scalar delta error. -/
theorem exists_count_decomposition
    
    (poisson : Literature.SteinShakarchi2011Poisson)
    (G : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ) (A W : ℕ)
    (hw : WeightSupportedInBox w A) (hw0 : w 0=0)
    (hs : ContDiff ℝ ∞ w) (hc : HasCompactSupport w) (hW : 0 < W)
    (M : ℝ) (hM : ∀ y, |w y| ≤ M) (Ω : Set (Fin n → ZMod W)) :
    ∃ p : ℕ → ℕ → ℝ → ℂ, KernelEstimates 1 p ∧
      ∀ η : ℝ, 0 < η → ∀ N : ℕ, 1 ≤ N → ∃ C : ℝ, 1 ≤ C ∧
        ∀ P Q : ℕ, 1 ≤ P → 1 ≤ Q →
          ‖(localizedWeightedCount G w A P W Ω:ℂ) -
            (zeroTerm G w P Q W Ω η p + nonzeroTerm G w P Q W Ω η p)‖ ≤
          C*(P:ℝ)^n*(Q:ℝ)^(-(N:ℝ)*η) := by
  obtain ⟨p,hp,h⟩ := ConstructedDeltaSource.exists_localized_count_power_error G w M hM A W Ω
  refine ⟨p,hp,?_⟩
  intro η hη N hN
  obtain ⟨C,hC,hbound⟩ := h η hη N hN
  refine ⟨C,hC,?_⟩
  intro P Q hP hQ
  have hb := hbound P Q hP hQ
  rw [approximation_eq poisson G w A P hw hw0 hs hc hP Q W hW Ω η p
    (fun q hq => (hp.smooth Q hQ q
      (Finset.mem_Icc.mp hq).1 (Finset.mem_Icc.mp hq).2).continuous)] at hb
  exact hb

end CubicTenVariables.LocalizedPoissonCount
