import CubicTenVariables.LocalizedPoissonCount
import CubicTenVariables.LocalizedTinyPhaseSaving
import CubicTenVariables.LocalizedClippedFrequency
import CubicTenVariables.FiniteDyadicPhases
import CubicTenVariables.FiniteDyadicModuli

/-! Exact finite assembly of the actual global nonzero-frequency term.
The tiny interval and every dyadic shell are disjoint with the source's
endpoint conventions. No infinite sum of uniform shell bounds is used. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.LocalizedFiniteBlockAssembly
open MvPolynomial MeasureTheory DeltaMethod DyadicFrequencyError LocalizedPoissonArc
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable

def phaseBlock (G : MvPolynomial (Fin 10) ℤ) (w : (Fin 10 → ℝ) → ℝ)
    (P Q W : ℕ) (Ω : Set (Fin 10 → ZMod W)) (φ η : ℝ)
    (p : ℕ → ℕ → ℝ → ℂ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 Q, ∫ θ in shell φ ∩ arc Q q η,
    p Q q θ*nonzeroContribution G w P q W Ω θ

def oneBlock (G : MvPolynomial (Fin 10) ℤ) (w : (Fin 10 → ℝ) → ℝ)
    (P Q W : ℕ) (Ω : Set (Fin 10 → ZMod W)) (φ η : ℝ)
    (p : ℕ → ℕ → ℝ → ℂ) : ℂ :=
  ∫ θ in shell φ ∩ arc Q 1 η, p Q 1 θ*nonzeroContribution G w P 1 W Ω θ

/-- The actual global frequency contribution is split into finitely many
phase shells and the exact tiny interval, including q=1 throughout. -/
theorem phase_decomposition (lit : Literature.SteinShakarchi2011Poisson)
    (G : MvPolynomial (Fin 10) ℤ) (w : (Fin 10 → ℝ) → ℝ) (A P : ℕ)
    (hw : WeightSupportedInBox w A) (hw0 : w 0=0)
    (hs : ContDiff ℝ ∞ w) (hc : HasCompactSupport w) (hP : 0 < P)
    (Q W : ℕ) (hQ : 1 ≤ Q) (hW : 0 < W) (Ω : Set (Fin 10 → ZMod W))
    (η : ℝ) (hη : η ≤ 1) (p : ℕ → ℕ → ℝ → ℂ) (hp : KernelEstimates 1 p) :
    LocalizedPoissonCount.nonzeroTerm G w P Q W Ω η p =
      LocalizedTinyPhaseSaving.contribution G w P Q W Ω η p +
      ∑ k ∈ Finset.range (FiniteDyadicPhases.count P),
        phaseBlock G w P Q W Ω (FiniteDyadicPhases.radius ((P:ℝ)^(-20:ℝ)) k) η p := by
  have he (q : ℕ) (hq : q ∈ Finset.Icc 1 Q) :=
    FiniteDyadicPhases.arc_integral_partition P Q q hP hQ (Finset.mem_Icc.mp hq).1 η hη
      (fun θ => p Q q θ*nonzeroContribution G w P q W Ω θ)
      (integrableOn_nonzero lit G w A P hw hw0 hs hc hP Q q W
        (Finset.mem_Icc.mp hq).1 hW Ω η p
        (hp.smooth Q hQ q (Finset.mem_Icc.mp hq).1 (Finset.mem_Icc.mp hq).2).continuous)
  unfold LocalizedPoissonCount.nonzeroTerm LocalizedTinyPhaseSaving.contribution
    LocalizedTinyPhaseSaving.region phaseBlock
  calc
    _ = ∑ q ∈ Finset.Icc 1 Q,
        ((∫ θ in arc Q q η ∩ Set.Icc (-((P:ℝ)^(-20:ℝ))) ((P:ℝ)^(-20:ℝ)),
          p Q q θ*nonzeroContribution G w P q W Ω θ) +
          ∑ k ∈ Finset.range (FiniteDyadicPhases.count P),
            ∫ θ in shell (FiniteDyadicPhases.radius ((P:ℝ)^(-20:ℝ)) k) ∩ arc Q q η,
              p Q q θ*nonzeroContribution G w P q W Ω θ) :=
      Finset.sum_congr rfl he
    _ = _ := by
      rw [Finset.sum_add_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro q _
        rw [Set.inter_comm]
      · exact Finset.sum_comm

/-- The modulus partition retains q=1 as its own literal integral. -/
theorem modulus_decomposition (G : MvPolynomial (Fin 10) ℤ)
    (w : (Fin 10 → ℝ) → ℝ) (P Q W : ℕ) (hQ : 1 ≤ Q)
    (Ω : Set (Fin 10 → ZMod W)) (φ η : ℝ) (p : ℕ → ℕ → ℝ → ℂ) :
    phaseBlock G w P Q W Ω φ η p = oneBlock G w P Q W Ω φ η p +
      ∑ j ∈ Finset.range (FiniteDyadicModuli.count Q),
        LocalizedClippedFrequency.block G w P Q W Ω ((2:ℝ)^j) φ η p :=
  FiniteDyadicModuli.sum_Icc_eq_one_add_blocks Q hQ _

/-- Full exact finite decomposition of the actual global nonzero term. -/
theorem decomposition (lit : Literature.SteinShakarchi2011Poisson)
    (G : MvPolynomial (Fin 10) ℤ) (w : (Fin 10 → ℝ) → ℝ) (A P : ℕ)
    (hw : WeightSupportedInBox w A) (hw0 : w 0=0)
    (hs : ContDiff ℝ ∞ w) (hc : HasCompactSupport w) (hP : 0 < P)
    (Q W : ℕ) (hQ : 1 ≤ Q) (hW : 0 < W) (Ω : Set (Fin 10 → ZMod W))
    (η : ℝ) (hη : η ≤ 1) (p : ℕ → ℕ → ℝ → ℂ) (hp : KernelEstimates 1 p) :
    LocalizedPoissonCount.nonzeroTerm G w P Q W Ω η p =
      LocalizedTinyPhaseSaving.contribution G w P Q W Ω η p +
        ((∑ k ∈ Finset.range (FiniteDyadicPhases.count P),
          oneBlock G w P Q W Ω (FiniteDyadicPhases.radius ((P:ℝ)^(-20:ℝ)) k) η p) +
        ∑ j ∈ Finset.range (FiniteDyadicModuli.count Q),
          ∑ k ∈ Finset.range (FiniteDyadicPhases.count P),
            LocalizedClippedFrequency.block G w P Q W Ω ((2:ℝ)^j)
              (FiniteDyadicPhases.radius ((P:ℝ)^(-20:ℝ)) k) η p) := by
  rw [phase_decomposition lit G w A P hw hw0 hs hc hP Q W hQ hW Ω η hη p hp]
  simp_rw [modulus_decomposition G w P Q W hQ Ω]
  rw [Finset.sum_add_distrib]
  congr 1
  congr 1
  exact Finset.sum_comm

/-- Uniform bounds for the actual finite blocks imply the exact
logarithmic block-count loss, including the extra modulus-one family. -/
theorem norm_le_of_block_bounds (lit : Literature.SteinShakarchi2011Poisson)
    (G : MvPolynomial (Fin 10) ℤ) (w : (Fin 10 → ℝ) → ℝ) (A P : ℕ)
    (hw : WeightSupportedInBox w A) (hw0 : w 0=0)
    (hs : ContDiff ℝ ∞ w) (hc : HasCompactSupport w) (hP : 0 < P)
    (Q W : ℕ) (hQ : 1 ≤ Q) (hW : 0 < W) (Ω : Set (Fin 10 → ZMod W))
    (η : ℝ) (hη : η ≤ 1) (p : ℕ → ℕ → ℝ → ℂ) (hp : KernelEstimates 1 p)
    (T B : ℝ) (hT : ‖LocalizedTinyPhaseSaving.contribution G w P Q W Ω η p‖ ≤ T)
    (hOne : ∀ k ∈ Finset.range (FiniteDyadicPhases.count P),
      ‖oneBlock G w P Q W Ω (FiniteDyadicPhases.radius ((P:ℝ)^(-20:ℝ)) k) η p‖ ≤ B)
    (hBlock : ∀ j ∈ Finset.range (FiniteDyadicModuli.count Q),
      ∀ k ∈ Finset.range (FiniteDyadicPhases.count P),
      ‖LocalizedClippedFrequency.block G w P Q W Ω ((2:ℝ)^j)
        (FiniteDyadicPhases.radius ((P:ℝ)^(-20:ℝ)) k) η p‖ ≤ B) :
    ‖LocalizedPoissonCount.nonzeroTerm G w P Q W Ω η p‖ ≤
      T + (((Nat.log 2 Q+2)*(Nat.log 2 (P^20)+1):ℕ):ℝ)*B := by
  rw [decomposition lit G w A P hw hw0 hs hc hP Q W hQ hW Ω η hη p hp]
  apply (norm_add_le _ _).trans
  apply (add_le_add hT (norm_add_le _ _)).trans
  have ho := (norm_sum_le _ _).trans (Finset.sum_le_sum hOne)
  have hb := (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j hj =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum (hBlock j hj))))
  calc
    _ ≤ T + ((FiniteDyadicPhases.count P:ℝ)*B +
        (FiniteDyadicModuli.count Q:ℝ)*((FiniteDyadicPhases.count P:ℝ)*B)) := by
      simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] using
        add_le_add (le_refl T) (add_le_add ho hb)
    _ = _ := by
      simp only [FiniteDyadicPhases.count,FiniteDyadicModuli.count,Nat.cast_add,
        Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]
      ring

end CubicTenVariables.LocalizedFiniteBlockAssembly
