import HessianTheorem11.UnconditionalOrbitMaximumDefs
import HessianTheorem11.UnconditionalOrbitFlagOrder
import HessianTheorem11.UnconditionalWeightFlags

/-! Actual relative order, admissibility, and normalized speed pass
between special-linear splittings of the same integer-indexed flag. -/
noncomputable section
namespace HessianTheorem11.UnconditionalOrbitGlobal
open MvPolynomial PolynomialRestriction PolynomialWeightTransport RationalDescent ReducedRelative
  UnconditionalOrbitIdeal UnconditionalWeightOptimization
variable {K : Type*} [Field K] [Infinite K] {n d : ℕ}

theorem admissible_of_same_flag
    (F : MvPolynomial (Fin n) K) (f g : WeightFrame K n)
    (hflags : f.flag = g.flag)
    (hf : HasNonnegativeWeights (restrict f.matrix F) f.weight) :
    HasNonnegativeWeights (restrict g.matrix F) g.weight :=
  lowerBound_of_same_flag F f.matrix g.matrix f.weight g.weight f.injective hflags 0 hf

theorem relativeSpeed_eq_order_div_norm
    (F : MvPolynomial (Fin n) K) (S : Set (MvPolynomial (Fin n) K))
    (f : WeightFrame K n) :
    relativeSpeed d F S f = (relativeOrder d F S f : ℝ) / ‖realWeight f.weight‖ := by
  simp [relativeSpeed,realWeight,EuclideanSpace.norm_eq,Real.norm_eq_abs,sq_abs]

theorem relativeSpeed_of_same_flag
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (S : Set (MvPolynomial (Fin n) K)) (hclosed : coefficientClosed S)
    (hS : slInvariant S) (hhom : ∀ G ∈ S, G.IsHomogeneous d) (hnot : F ∉ S)
    (f g : WeightFrame K n) (hf : f.matrix.det = 1) (hg : g.matrix.det = 1)
    (hflags : f.flag = g.flag)
    (hfv : HasNonnegativeWeights (restrict f.matrix F) f.weight)
    (hnorm : ‖realWeight f.weight‖ = ‖realWeight g.weight‖) :
    relativeSpeed d F S f = relativeSpeed d F S g := by
  rw [relativeSpeed_eq_order_div_norm,relativeSpeed_eq_order_div_norm,hnorm,
    relativeOrder_of_same_flag F hF S hclosed hS hhom hnot f g hf hg hflags
      hfv (admissible_of_same_flag F f g hflags hfv)]

theorem slMaximizingFrame_of_same_flag
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (S : Set (MvPolynomial (Fin n) K)) (hclosed : coefficientClosed S)
    (hS : slInvariant S) (hhom : ∀ G ∈ S, G.IsHomogeneous d) (hnot : F ∉ S)
    (f g : WeightFrame K n) (hf : SLMaximizingFrame d F S f)
    (hg : g.matrix.det = 1) (hflags : f.flag = g.flag)
    (hnorm : ‖realWeight f.weight‖ = ‖realWeight g.weight‖) :
    SLMaximizingFrame d F S g := by
  have hgv := admissible_of_same_flag F f g hflags hf.admissible
  have horder := relativeOrder_of_same_flag F hF S hclosed hS hhom hnot
    f g hf.det_one hg hflags hf.admissible hgv
  have hspeed := relativeSpeed_of_same_flag F hF S hclosed hS hhom hnot
    f g hf.det_one hg hflags hf.admissible hnorm
  refine ⟨hg,?_,hgv,horder ▸ hf.positive_order,?_⟩
  · intro hz
    have hnorm0 : ‖realWeight f.weight‖ = 0 := by
      rw [hnorm,hz]
      have he : realWeight (0 : Fin n → ℤ) = 0 := by
        ext i
        simp [realWeight]
      rw [he,norm_zero]
    have hr := norm_eq_zero.mp hnorm0
    apply hf.nonzero
    funext i
    have hi := congrArg (fun v : WeightSpace n => v i) hr
    change (f.weight i : ℝ) = 0 at hi
    exact_mod_cast hi
  · intro v hvdet hvadm
    rw [← hspeed]
    exact hf.maximal v hvdet hvadm

end HessianTheorem11.UnconditionalOrbitGlobal
