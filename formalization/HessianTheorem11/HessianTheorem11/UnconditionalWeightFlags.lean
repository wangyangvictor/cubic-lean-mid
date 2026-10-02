import HessianTheorem11.UnconditionalWeightGlobal
import HessianTheorem11.UnconditionalWeightUnique
import HessianTheorem11.UnconditionalCommonFlags

/-! Common splittings and strict convexity give equality of the actual
weighted flags of equal-norm global maximizers. No flag uniqueness input. -/
noncomputable section
namespace HessianTheorem11.UnconditionalWeightOptimization
open MvPolynomial RationalDescent PolynomialRestriction PolynomialWeightTransport Module
open UnconditionalFlags
variable {K : Type*} [Field K] {n : ℕ}

def frameBasis (f : WeightFrame K n) : Basis (Fin n) K (Fin n → K) :=
  (Pi.basisFun K (Fin n)).map (frameEquiv f.matrix f.injective)

@[simp] theorem frameBasis_apply (f : WeightFrame K n) (i : Fin n) :
    frameBasis f i = fun j => f.matrix j i := by
  simp [frameBasis,frameEquiv_apply,Matrix.col]
  rfl

theorem frameBasis_flag (f : WeightFrame K n) :
    basisFlag (frameBasis f) f.weight = f.flag := by
  funext a
  simp only [basisFlag,WeightFrame.flag,frameBasis_apply]

theorem realWeight_norm_of_square_sum (w u : Fin n → ℤ)
    (h : ∑ i, (w i : ℝ)^2 = ∑ i, (u i : ℝ)^2) :
    ‖realWeight w‖ = ‖realWeight u‖ := by
  simpa [realWeight,EuclideanSpace.norm_eq,Real.norm_eq_abs,sq_abs] using congrArg Real.sqrt h

theorem positive_of_same_flag
    (F : MvPolynomial (Fin n) K) (B C : Matrix (Fin n) (Fin n) K)
    (v w : Fin n → ℤ) (hB : Function.Injective B.mulVec)
    (hflags : weightFlag B v = weightFlag C w)
    (hp : HasPositiveWeights (restrict B F) v) :
    HasPositiveWeights (restrict C F) w := by
  have h := lowerBound_of_same_flag F B C v w hB hflags 1 (by
    intro e he
    have := hp e he
    omega)
  intro e he
  have := h e he
  omega

theorem instability_of_same_flag
    (F : MvPolynomial (Fin n) K) (hne : F ≠ 0)
    (f g : WeightFrame K n) (hflags : f.flag = g.flag)
    (hnorm : ‖realWeight f.weight‖ = ‖realWeight g.weight‖) :
    f.instability F = g.instability F := by
  have hm := minimumWeight_of_same_flag F f.matrix g.matrix f.weight g.weight
    f.injective g.injective hflags
    (support_nonempty.mpr (restrict_nonzero F hne f.matrix f.injective))
    (support_nonempty.mpr (restrict_nonzero F hne g.matrix g.injective))
  rw [instability_eq_finiteSpeed,instability_eq_finiteSpeed,finiteSpeed,finiteSpeed,hnorm]
  exact congrArg (fun a : ℤ => (a : ℝ) / ‖realWeight g.weight‖) hm

/-- Two globally maximizing frames with the same norm have the identical
integer-indexed filtration. Galois conjugation preserves the norm literally. -/
theorem maximizing_flag_eq_of_norm_eq
    (F : MvPolynomial (Fin n) K) (hne : F ≠ 0)
    (f g : WeightFrame K n) (hf : MaximizingFrame F f) (hg : MaximizingFrame F g)
    (hnorm : ‖realWeight f.weight‖ = ‖realWeight g.weight‖) : f.flag = g.flag := by
  classical
  obtain ⟨b,w,u,hw,hu,hws,hus⟩ :=
    exists_common_weighted_basis (frameBasis f) (frameBasis g) f.weight g.weight
  have hwflag : weightFlag (basisMatrix b) w = f.flag := by
    rw [frameBasis_flag] at hw
    exact hw
  have huflag : weightFlag (basisMatrix b) u = g.flag := by
    rw [frameBasis_flag] at hu
    exact hu
  have hwsum : ∑ i, w i = 0 := by
    have h := hws (fun z => (z : ℝ))
    have hfzero : (∑ i, (f.weight i : ℝ)) = 0 := by exact_mod_cast f.sum_zero
    rw [hfzero] at h
    exact_mod_cast h
  have husum : ∑ i, u i = 0 := by
    have h := hus (fun z => (z : ℝ))
    have hgzero : (∑ i, (g.weight i : ℝ)) = 0 := by exact_mod_cast g.sum_zero
    rw [hgzero] at h
    exact_mod_cast h
  have hwnorm := realWeight_norm_of_square_sum w f.weight (hws (fun z => (z : ℝ)^2))
  have hunorm := realWeight_norm_of_square_sum u g.weight (hus (fun z => (z : ℝ)^2))
  let fw : WeightFrame K n := ⟨basisMatrix b,basisMatrix_injective b,w,hwsum⟩
  let gu : WeightFrame K n := ⟨basisMatrix b,basisMatrix_injective b,u,husum⟩
  have hwpos : fw.Positive F :=
    positive_of_same_flag F f.matrix (basisMatrix b) f.weight w f.injective hwflag.symm hf.1
  have hupos : gu.Positive F :=
    positive_of_same_flag F g.matrix (basisMatrix b) g.weight u g.injective huflag.symm hg.1
  have hfspeed : fw.instability F = f.instability F :=
    instability_of_same_flag F hne fw f hwflag hwnorm
  have hgspeed : gu.instability F = g.instability F :=
    instability_of_same_flag F hne gu g huflag hunorm
  have hwmax : ∀ v : Fin n → ℤ, (∑ i, v i) = 0 →
      finiteSpeed (restrict (basisMatrix b) F).support v ≤
        finiteSpeed (restrict (basisMatrix b) F).support w := by
    intro v hv
    let fv : WeightFrame K n := ⟨basisMatrix b,basisMatrix_injective b,v,hv⟩
    have h := hf.2 fv
    rw [← hfspeed,instability_eq_finiteSpeed,instability_eq_finiteSpeed] at h
    exact h
  have humax : ∀ v : Fin n → ℤ, (∑ i, v i) = 0 →
      finiteSpeed (restrict (basisMatrix b) F).support v ≤
        finiteSpeed (restrict (basisMatrix b) F).support u := by
    intro v hv
    let gv : WeightFrame K n := ⟨basisMatrix b,basisMatrix_injective b,v,hv⟩
    have h := hg.2 gv
    rw [← hgspeed,instability_eq_finiteSpeed,instability_eq_finiteSpeed] at h
    exact h
  have he : w = u := same_norm_integer_maximizers_equal
    (support_nonempty.mpr (restrict_nonzero F hne _ (basisMatrix_injective b)))
    w u hwsum husum hwpos hupos hwmax humax (hwnorm.trans (hnorm.trans hunorm.symm))
  rw [← hwflag,← huflag,he]

end HessianTheorem11.UnconditionalWeightOptimization
