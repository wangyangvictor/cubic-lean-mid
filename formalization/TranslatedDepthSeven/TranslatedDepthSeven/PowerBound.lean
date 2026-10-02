import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Tactic

/-!
# Uniform power bounds

This file gives an explicit, elementary replacement for the informal
notation

`f(H,T) \ll_\varepsilon H^\varepsilon T^(a+\varepsilon)`.

The bases are nonnegative reals because the functions being bounded are
cardinalities.  The exponent is a real number, so rational exponents in the
terminal ledger can be represented exactly.
-/

namespace TranslatedDepthSeven

/-- A two-parameter nonnegative quantity, such as a cardinality. -/
abbrev CountFunction := NNReal → NNReal → NNReal

/-- The explicit majorant occurring in a uniform power bound. -/
noncomputable def powerEnvelope (C H T : NNReal) (a ε : ℝ) : NNReal :=
  C * H ^ ε * T ^ (a + ε)

/--
`UniformPowerBound f a` means that, for every positive `ε`, there is one
constant, independent of `H` and `T`, such that

`f H T ≤ C * H^ε * T^(a+ε)`

whenever both scale parameters are at least one.
The additional condition `T ≤ H` is exactly the relation between the two
scales in the translated counting problem; including it avoids demanding
irrelevant estimates at unrealizable pairs of scales.
-/
def UniformPowerBound (f : CountFunction) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : NNReal, ∀ H T : NNReal, 1 ≤ H → 1 ≤ T → T ≤ H →
      f H T ≤ powerEnvelope C H T a ε

/-- One implied constant for every member of a finite family. -/
def UniformFamilyPowerBound {ι : Type*} [Fintype ι]
    (f : ι → CountFunction) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : NNReal, ∀ i H T, 1 ≤ H → 1 ≤ T → T ≤ H →
      f i H T ≤ powerEnvelope C H T a ε

namespace UniformPowerBound

theorem zero (a : ℝ) : UniformPowerBound (fun _ _ ↦ 0) a := by
  intro ε hε
  exact ⟨0, by simp [powerEnvelope]⟩

theorem mono {f g : CountFunction} {a : ℝ}
    (hfg : ∀ H T, f H T ≤ g H T) (hg : UniformPowerBound g a) :
    UniformPowerBound f a := by
  intro ε hε
  obtain ⟨C, hC⟩ := hg ε hε
  refine ⟨C, ?_⟩
  intro H T hH hT hTH
  exact (hfg H T).trans (hC H T hH hT hTH)

theorem add {f g : CountFunction} {a : ℝ}
    (hf : UniformPowerBound f a) (hg : UniformPowerBound g a) :
    UniformPowerBound (fun H T ↦ f H T + g H T) a := by
  intro ε hε
  obtain ⟨Cf, hf⟩ := hf ε hε
  obtain ⟨Cg, hg⟩ := hg ε hε
  refine ⟨Cf + Cg, ?_⟩
  intro H T hH hT hTH
  calc
    f H T + g H T ≤ powerEnvelope Cf H T a ε + powerEnvelope Cg H T a ε :=
      add_le_add (hf H T hH hT hTH) (hg H T hH hT hTH)
    _ = powerEnvelope (Cf + Cg) H T a ε := by
      simp only [powerEnvelope]
      ring

theorem const_mul (c : NNReal) {f : CountFunction} {a : ℝ}
    (hf : UniformPowerBound f a) :
    UniformPowerBound (fun H T ↦ c * f H T) a := by
  intro ε hε
  obtain ⟨C, hC⟩ := hf ε hε
  refine ⟨c * C, ?_⟩
  intro H T hH hT hTH
  calc
    c * f H T ≤ c * powerEnvelope C H T a ε :=
      mul_le_mul_right (hC H T hH hT hTH) c
    _ = powerEnvelope (c * C) H T a ε := by
      simp only [powerEnvelope]
      ring

/-- Products of uniform power bounds add their exponents.  The requested
epsilon is split equally between the two factors. -/
theorem mul {f g : CountFunction} {a b : ℝ}
    (hf : UniformPowerBound f a) (hg : UniformPowerBound g b) :
    UniformPowerBound (fun H T ↦ f H T * g H T) (a + b) := by
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨Cf, hf⟩ := hf δ hδ
  obtain ⟨Cg, hg⟩ := hg δ hδ
  refine ⟨Cf * Cg, ?_⟩
  intro H T hH hT hTH
  have hH0 : H ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hH)
  have hT0 : T ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hT)
  have hδδ : δ + δ = ε := by dsimp [δ]; ring
  have habδ : (a + δ) + (b + δ) = (a + b) + ε := by
    rw [← hδδ]
    ring
  calc
    f H T * g H T ≤
        powerEnvelope Cf H T a δ * powerEnvelope Cg H T b δ :=
      mul_le_mul (hf H T hH hT hTH) (hg H T hH hT hTH)
        (by positivity) (by positivity)
    _ = (Cf * Cg) * (H ^ δ * H ^ δ) *
        (T ^ (a + δ) * T ^ (b + δ)) := by
      simp only [powerEnvelope]
      ring
    _ = (Cf * Cg) * H ^ ε * T ^ ((a + b) + ε) := by
      rw [← NNReal.rpow_add hH0, hδδ, ← NNReal.rpow_add hT0, habδ]
    _ = powerEnvelope (Cf * Cg) H T (a + b) ε := rfl

theorem weaken {f : CountFunction} {a b : ℝ} (hab : a ≤ b)
    (hf : UniformPowerBound f a) : UniformPowerBound f b := by
  intro ε hε
  obtain ⟨C, hC⟩ := hf ε hε
  refine ⟨C, ?_⟩
  intro H T hH hT hTH
  refine (hC H T hH hT hTH).trans ?_
  unfold powerEnvelope
  apply mul_le_mul_right
  exact NNReal.rpow_le_rpow_of_exponent_le hT (by linarith)

theorem finset_sum {ι : Type*} (s : Finset ι) (f : ι → CountFunction) {a : ℝ}
    (hf : ∀ i ∈ s, UniformPowerBound (f i) a) :
    UniformPowerBound (fun H T ↦ ∑ i ∈ s, f i H T) a := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using zero a
  | @insert i s hi ih =>
      have hiBound : UniformPowerBound (f i) a :=
        hf i (Finset.mem_insert_self i s)
      have hsBound : UniformPowerBound (fun H T ↦ ∑ j ∈ s, f j H T) a := by
        apply ih
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)
      simpa only [Finset.sum_insert hi] using hiBound.add hsBound

end UniformPowerBound

/-- Pointwise uniform estimates over a finite index set admit one common
constant.  This is the exact finite-family uniformization used for the fixed
collection of depth-seven fivefolds. -/
theorem uniformFamilyPowerBound_of_pointwise {ι : Type*} [Fintype ι]
    (f : ι → CountFunction) {a : ℝ}
    (hf : ∀ i, UniformPowerBound (f i) a) :
    UniformFamilyPowerBound f a := by
  classical
  have hsum : UniformPowerBound (fun H T ↦ ∑ i : ι, f i H T) a := by
    apply UniformPowerBound.finset_sum Finset.univ f
    intro i hi
    exact hf i
  intro ε hε
  obtain ⟨C, hC⟩ := hsum ε hε
  refine ⟨C, ?_⟩
  intro i H T hH hT hTH
  have hi : f i H T ≤ ∑ j : ι, f j H T := by
    exact Finset.single_le_sum (fun j _ ↦ zero_le (f j H T)) (Finset.mem_univ i)
  exact hi.trans (hC H T hH hT hTH)

end TranslatedDepthSeven
