import HessianTheorem11.UnconditionalOrbitOrderTransport

/-! The actual relative target-ideal order depends only on the weighted
flag of an admissible special-linear frame. The two indexed weight lists
may differ, as required for comparison in a common apartment. -/
noncomputable section
namespace HessianTheorem11.UnconditionalOrbitIdeal
open MvPolynomial PolynomialRestriction PolynomialWeightTransport ReducedRelative
open RationalDescent UnconditionalWeightOptimization
variable {K : Type*} [Field K] [Infinite K] {n d : ℕ}

theorem relativeOrder_le_of_same_flag
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (S : Set (MvPolynomial (Fin n) K)) (hclosed : coefficientClosed S)
    (hS : slInvariant S) (hhom : ∀ G ∈ S, G.IsHomogeneous d) (hnot : F ∉ S)
    (f g : WeightFrame K n) (hf : f.matrix.det = 1) (hg : g.matrix.det = 1)
    (hflags : f.flag = g.flag)
    (hfv : HasNonnegativeWeights (restrict f.matrix F) f.weight)
    (hgv : HasNonnegativeWeights (restrict g.matrix F) g.weight) :
    relativeOrder d F S f ≤ relativeOrder d F S g := by
  let A := frameTransition f.matrix g.matrix f.injective
  have hA : f.matrix * A = g.matrix := matrix_mul_frameTransition f.matrix g.matrix f.injective
  have hdet : A.det = 1 := by
    have h := congrArg Matrix.det hA
    rwa [Matrix.det_mul,hf,hg,one_mul] at h
  have he : restrict A (restrict f.matrix F) = restrict g.matrix F := by
    rw [restrict_restrict,hA]
  have hnot' : restrict f.matrix F ∉ S := by
    intro h
    apply hnot
    have hi : f.matrix⁻¹.det = 1 := by rw [Matrix.det_nonsing_inv,hf,Ring.inverse_one]
    have h' := hS f.matrix⁻¹ hi _ h
    rwa [restrict_restrict,Matrix.mul_nonsing_inv f.matrix (hf ▸ isUnit_one),restrict_one] at h'
  have ht := identity_order_le_of_weight_triangular (restrict f.matrix F)
    (homogeneous_restrict _ F hF) S hclosed hS hhom hnot' A hdet f.weight g.weight
    f.sum_zero g.sum_zero (transition_weights_of_flags f.matrix g.matrix f.weight g.weight f.injective hflags)
    hfv (he.symm ▸ hgv)
  rw [he] at ht
  rw [relativeOrder_coordinate F hF S hclosed hS hhom hnot f hf,
    relativeOrder_coordinate F hF S hclosed hS hhom hnot g hg]
  exact ht

theorem relativeOrder_of_same_flag
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (S : Set (MvPolynomial (Fin n) K)) (hclosed : coefficientClosed S)
    (hS : slInvariant S) (hhom : ∀ G ∈ S, G.IsHomogeneous d) (hnot : F ∉ S)
    (f g : WeightFrame K n) (hf : f.matrix.det = 1) (hg : g.matrix.det = 1)
    (hflags : f.flag = g.flag)
    (hfv : HasNonnegativeWeights (restrict f.matrix F) f.weight)
    (hgv : HasNonnegativeWeights (restrict g.matrix F) g.weight) :
    relativeOrder d F S f = relativeOrder d F S g :=
  Nat.le_antisymm (relativeOrder_le_of_same_flag F hF S hclosed hS hhom hnot f g hf hg hflags hfv hgv)
    (relativeOrder_le_of_same_flag F hF S hclosed hS hhom hnot g f hg hf hflags.symm hgv hfv)

end HessianTheorem11.UnconditionalOrbitIdeal
