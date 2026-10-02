import HessianTheorem11.ReducedRelativeKempf

/-! The intermediate SL maximizing frame uses the actual relative ideal
order and its Euclidean normalization. Primitivity is unnecessary here. -/
noncomputable section
namespace HessianTheorem11.UnconditionalOrbitGlobal
open MvPolynomial PolynomialRestriction RationalDescent ReducedRelative
variable {K : Type*} [Field K] {n : ℕ}

structure SLMaximizingFrame (d : ℕ) (F : MvPolynomial (Fin n) K)
    (S : Set (MvPolynomial (Fin n) K)) (f : WeightFrame K n) : Prop where
  det_one : f.matrix.det = 1
  nonzero : f.weight ≠ 0
  admissible : HasNonnegativeWeights (restrict f.matrix F) f.weight
  positive_order : 0 < relativeOrder d F S f
  maximal : ∀ g : WeightFrame K n, g.matrix.det = 1 →
    HasNonnegativeWeights (restrict g.matrix F) g.weight →
    relativeSpeed d F S g ≤ relativeSpeed d F S f

end HessianTheorem11.UnconditionalOrbitGlobal
