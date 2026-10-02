import CubicTenVariables.FixedLeadingSurfaceCoordinateTransport
import TranslatedDepthSeven.CharacteristicPolynomialHeight

/-!
# Coefficient height under a fixed integral polynomial substitution

On equations of bounded total degree, a fixed integral substitution
increases maximum coefficient height by a fixed multiplicative constant.
The proof expands in a finite set of literal monomials. In particular,
the normalization chosen from a fixed leading form does not introduce
constants depending on the varying lower coefficients.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace CubicTenVariables.FixedPolynomialSubstitutionHeight
open MvPolynomial TranslatedDepthSeven
open scoped BigOperators

def exponentBox {σ : Type*} [Fintype σ] (d : ℕ) : Finset (σ →₀ ℕ) := by
  classical
  exact Finset.univ.image (fun μ : σ → Fin (d + 1) =>
    Finsupp.equivFunOnFinite.symm (fun i => (μ i).val))

theorem support_subset_exponentBox {σ : Type*} [Fintype σ]
    (g : MvPolynomial σ ℤ) {d : ℕ} (hdegree : g.totalDegree ≤ d) :
    g.support ⊆ exponentBox d := by
  classical
  intro μ hμ
  refine Finset.mem_image.mpr ⟨fun i => ⟨μ i, Nat.lt_succ_iff.mpr
    ((Finsupp.le_degree i μ).trans ((le_totalDegree hμ).trans hdegree))⟩,
      Finset.mem_univ _, ?_⟩
  ext i
  rfl

theorem coeff_natAbs_le_height {σ : Type*} (g : MvPolynomial σ ℤ)
    (μ : σ →₀ ℕ) : (g.coeff μ).natAbs ≤ mvPolynomialCoefficientNatAbsMax g := by
  classical
  by_cases hμ : μ ∈ g.support
  · exact coeff_natAbs_le_mvPolynomialCoefficientNatAbsMax g hμ
  · simp [notMem_support_iff.mp hμ]

/-- This constant depends only on the fixed substitution and degree bound. -/
def substitutionHeightConstant {σ τ : Type*} [Fintype σ]
    (φ : MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial τ ℤ) (d : ℕ) : ℕ :=
  max 1 (∑ μ ∈ exponentBox (σ := σ) d,
    mvPolynomialCoefficientNatAbsMax (φ (monomial μ 1)))

theorem substitutionHeightConstant_pos {σ τ : Type*} [Fintype σ]
    (φ : MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial τ ℤ) (d : ℕ) :
    0 < substitutionHeightConstant φ d :=
  lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

theorem height_substitution_le {σ τ : Type*} [Fintype σ]
    (φ : MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial τ ℤ) (d : ℕ)
    (g : MvPolynomial σ ℤ) (hdegree : g.totalDegree ≤ d) :
    mvPolynomialCoefficientNatAbsMax (φ g) ≤
      substitutionHeightConstant φ d * mvPolynomialCoefficientNatAbsMax g := by
  classical
  apply Finset.sup_le
  intro ν _hν
  have hexp : φ g = ∑ μ ∈ g.support, C (g.coeff μ) * φ (monomial μ 1) := by
    conv_lhs => rw [g.as_sum]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro μ _hμ
    have hm : monomial μ (g.coeff μ) = C (g.coeff μ) * monomial μ 1 := by
      rw [C_mul_monomial, mul_one]
    rw [hm, map_mul]
    rw [show φ (C (g.coeff μ)) = C (g.coeff μ) from φ.commutes (g.coeff μ)]
  rw [hexp, coeff_sum]
  calc
    _ ≤ ∑ μ ∈ g.support,
        ((C (g.coeff μ) * φ (monomial μ 1)).coeff ν).natAbs :=
      int_natAbs_sum_le_sum_natAbs _ _
    _ ≤ ∑ μ ∈ g.support,
        mvPolynomialCoefficientNatAbsMax g *
          mvPolynomialCoefficientNatAbsMax (φ (monomial μ 1)) := by
      apply Finset.sum_le_sum
      intro μ hμ
      rw [coeff_C_mul, Int.natAbs_mul]
      exact Nat.mul_le_mul (coeff_natAbs_le_height g μ)
        (coeff_natAbs_le_height _ ν)
    _ ≤ ∑ μ ∈ exponentBox (σ := σ) d,
        mvPolynomialCoefficientNatAbsMax g *
          mvPolynomialCoefficientNatAbsMax (φ (monomial μ 1)) :=
      Finset.sum_le_sum_of_subset (support_subset_exponentBox g hdegree)
    _ = mvPolynomialCoefficientNatAbsMax g *
        ∑ μ ∈ exponentBox (σ := σ) d,
          mvPolynomialCoefficientNatAbsMax (φ (monomial μ 1)) := by
      rw [Finset.mul_sum]
    _ ≤ substitutionHeightConstant φ d * mvPolynomialCoefficientNatAbsMax g := by
      rw [mul_comm (substitutionHeightConstant φ d)]
      exact Nat.mul_le_mul_left _ (Nat.le_max_right _ _)

/-- For H above the fixed constant, normalization only increases the
height exponent by one. -/
theorem height_substitution_le_power {σ τ : Type*} [Fintype σ]
    (φ : MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial τ ℤ) (d : ℕ)
    (g : MvPolynomial σ ℤ) (hdegree : g.totalDegree ≤ d)
    {H e : ℕ} (hH : substitutionHeightConstant φ d ≤ H)
    (hheight : mvPolynomialCoefficientNatAbsMax g ≤ H ^ e) :
    mvPolynomialCoefficientNatAbsMax (φ g) ≤ H ^ (e + 1) := by
  calc
    _ ≤ substitutionHeightConstant φ d * mvPolynomialCoefficientNatAbsMax g :=
      height_substitution_le φ d g hdegree
    _ ≤ H * H ^ e := Nat.mul_le_mul hH hheight
    _ = H ^ (e + 1) := by rw [pow_succ, mul_comm]

end CubicTenVariables.FixedPolynomialSubstitutionHeight
