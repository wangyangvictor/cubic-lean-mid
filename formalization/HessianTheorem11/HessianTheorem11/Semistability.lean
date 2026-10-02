import HessianTheorem11.CubicWeights
import HessianTheorem11.PolynomialRestriction
import HessianTheorem11.RationalWeights

/-!
An explicit algebraic weight-semistability predicate, its rational anisotropy
proof, and the centered-weight consequence needed for radial inequalities.
This module does not assert geometric descent from rational semistability.
-/

noncomputable section

namespace HessianTheorem11

open MvPolynomial

/-- No injective linear coordinate change makes every occurring monomial
strictly positive for a zero-total integral variable weighting. -/
def WeightSemistable {K : Type*} [CommRing K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) : Prop :=
  ∀ B : Matrix (Fin n) (Fin n) K, Function.Injective B.mulVec →
    ∀ w : Fin n → ℤ, (∑ i, w i) = 0 →
      HasPositiveWeights (PolynomialRestriction.restrict B F) w → False

/-- Anisotropy excludes destabilizing weights in every rational basis.
This is a rational statement; scalar-extension descent remains separate. -/
theorem rational_weightSemistable {n : ℕ}
    (F : AnisotropicCubic n) (hn : 0 < n) : WeightSemistable F.polynomial := by
  intro B hB w hsum hpositive
  let G : AnisotropicCubic n := PolynomialRestriction.restrictedCubic B F hB
  have hnonnegative : HasNonnegativeMonomialWeights G.polynomial w := by
    intro d hd
    exact le_of_lt (hpositive d hd)
  have hwzero : w = 0 :=
    rational_zero_sum_admissible_weights_trivial G w hnonnegative hsum
  exact positiveWeights_nontrivial G.polynomial
    (anisotropic_polynomial_ne_zero hn G) w hpositive hwzero

/-- Semistability implies that any nonnegative-support variable weighting
has nonnegative total weight, in every injective linear coordinate system.
The proof constructs the centered integral weighting explicitly. -/
theorem WeightSemistable.nonnegative_weight_sum
    {K : Type*} [CommRing K] {n : ℕ}
    {F : MvPolynomial (Fin n) K} (hsemi : WeightSemistable F)
    (hF : F.IsHomogeneous 3)
    (B : Matrix (Fin n) (Fin n) K) (hB : Function.Injective B.mulVec)
    (w : Fin n → ℤ)
    (hW : HasNonnegativeWeights (PolynomialRestriction.restrict B F) w) :
    0 ≤ ∑ i, w i := by
  by_contra hnegative
  exact hsemi B hB (centeredWeights w) (sum_centeredWeights w)
    (positive_centeredWeights_of_negative_sum (PolynomialRestriction.restrict B F)
      (PolynomialRestriction.homogeneous_restrict B F hF) w hW (by omega))

/-- A convenience form whose support premise is the actual third-partial
tensor after the indicated coordinate change. -/
theorem WeightSemistable.nonnegative_weight_sum_of_thirdPartials
    {K : Type*} [Field K] [CharZero K] {n : ℕ}
    {F : MvPolynomial (Fin n) K} (hsemi : WeightSemistable F)
    (hF : F.IsHomogeneous 3)
    (B : Matrix (Fin n) (Fin n) K) (hB : Function.Injective B.mulVec)
    (w : Fin n → ℤ)
    (hT : ∀ i j k,
      thirdPartialCoefficient (PolynomialRestriction.restrict B F) i j k ≠ 0 →
        0 ≤ w i + w j + w k) : 0 ≤ ∑ i, w i :=
  hsemi.nonnegative_weight_sum hF B hB w
    (nonnegativeWeights_of_thirdPartials (PolynomialRestriction.restrict B F)
      (PolynomialRestriction.homogeneous_restrict B F hF) w hT)

end HessianTheorem11
