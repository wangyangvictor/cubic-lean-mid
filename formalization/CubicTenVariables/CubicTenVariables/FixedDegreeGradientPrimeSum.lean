import TranslatedDepthSeven.HypersurfaceMixedResiduePrimeSum

/-!
# Mixed-prime loss uniform over equations of polynomially bounded height

The old fixed-equation wrapper absorbs its coefficient constant by requiring
the box height to exceed that constant.  That quantifier order is unsuitable
when the equation varies with the box.  Here an explicit coefficient bound
`height(f) ≤ H^e` gives exponent `e+d+2` and a threshold depending only on the
degree.  This proves the gradient-discard part of the mixed-prime estimate;
the occupied-class point-count bound remains a separate hypothesis.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace CubicTenVariables.FixedDegreeGradientPrimeSum
open MvPolynomial TranslatedDepthSeven
open scoped BigOperators

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem support_card_le_of_totalDegree_le
    {σ : Type*} [Fintype σ] (f : MvPolynomial σ ℤ) {d : ℕ}
    (hdegree : f.totalDegree ≤ d) :
    f.support.card ≤ (d + 1) ^ Fintype.card σ := by
  classical
  let Φ : {μ // μ ∈ f.support} → (σ → Fin (d + 1)) := fun μ i =>
    ⟨μ.1 i, Nat.lt_succ_iff.mpr <|
      (Finsupp.le_degree i μ.1).trans ((MvPolynomial.le_totalDegree μ.2).trans hdegree)⟩
  have hinj : Function.Injective Φ := by
    intro μ ν h
    apply Subtype.ext
    ext i
    exact congrArg Fin.val (congrFun h i)
  simpa using Fintype.card_le_of_injective Φ hinj

/-- The threshold is independent of the coefficients of `f`. -/
theorem eval_pderiv_natAbs_le_uniform_height_power
    {n d e H : ℕ} (f : MvPolynomial (Fin n) ℤ)
    (hH : max 2 ((d + 1) ^ n * d) ≤ H)
    (hdegree : f.totalDegree ≤ d)
    (hcoeff : mvPolynomialCoefficientNatAbsMax f ≤ H ^ e)
    (x : Fin n → ℤ) (hx : ∀ i, (x i).natAbs ≤ H) (v : Fin n) :
    (eval x (pderiv v f)).natAbs ≤ H ^ (e + d + 2) := by
  have hH1 : 1 ≤ H := (by omega : 1 ≤ max 2 ((d + 1) ^ n * d)).trans hH
  have hconstant : (d + 1) ^ n * d ≤ H := (Nat.le_max_right _ _).trans hH
  have hs : f.support.card ≤ (d + 1) ^ n := by
    simpa using support_card_le_of_totalDegree_le f hdegree
  have heval := eval_pderiv_natAbs_le_support_mul_degree_mul_coeff_mul_pow f x v
    (fun μ hμ => (coeff_natAbs_le_mvPolynomialCoefficientNatAbsMax f hμ).trans hcoeff)
    hdegree hx
  rw [max_eq_right hH1] at heval
  calc
    (eval x (pderiv v f)).natAbs ≤ f.support.card * d * H ^ e * H ^ d := heval
    _ ≤ H * H ^ e * H ^ d := Nat.mul_le_mul_right _
      (Nat.mul_le_mul_right _ ((Nat.mul_le_mul_right d hs).trans hconstant))
    _ = H ^ (e + d + 1) := by rw [pow_add, pow_succ]; ring
    _ ≤ H ^ (e + d + 2) := Nat.pow_le_pow_right hH1 (by omega)

/-- The product of bad primes is bounded uniformly even when the defining
equation varies with `H`. -/
theorem badPrimeProduct_le_uniform_height_power
    {d e H : ℕ} (F : MvPolynomial (Fin 4) ℤ)
    (hH : max 2 ((d + 1) ^ 3 * d) ≤ H)
    (hdegree : (surfaceHypersurfaceFirstChartDehomogenize F).totalDegree ≤ d)
    (hcoeff : mvPolynomialCoefficientNatAbsMax
      (surfaceHypersurfaceFirstChartDehomogenize F) ≤ H ^ e)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (x : Fin 3 → ℤ) (hx : ∀ i, (x i).natAbs ≤ H)
    (hgrad : ∃ v, eval x (pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) ≠ 0) :
    letI : DecidablePred (hypersurfaceAffineGradientBadReduction F x) := Classical.decPred _
    (∏ p ∈ P.filter (hypersurfaceAffineGradientBadReduction F x), p) ≤ H ^ (e + d + 2) := by
  classical
  obtain ⟨v, hv⟩ := hgrad
  exact (hypersurface_badPrimeProduct_le_partial_natAbs F x P hP v hv).trans
    (eval_pderiv_natAbs_le_uniform_height_power _ hH hdegree hcoeff x hx v)

/-- The sharp mixed-prime estimate now has an explicit exponent chosen from
degree and coefficient-growth exponent, before the equation, columns, and
prime set. Repeated columns are allowed. -/
theorem mixedResidue_log_lower_bound_uniform_height
    {d e H : ℕ} (F : MvPolynomial (Fin 4) ℤ)
    (hH : max 2 ((d + 1) ^ 3 * d) ≤ H)
    (hdegree : (surfaceHypersurfaceFirstChartDehomogenize F).totalDegree ≤ d)
    (hcoeff : mvPolynomialCoefficientNatAbsMax
      (surfaceHypersurfaceFirstChartDehomogenize F) ≤ H ^ e)
    (K : ℝ) (hK : 0 < K)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, Real.log (H : ℝ) ≤ (p : ℝ))
    {ι : Type*} [Fintype ι] (y : ι → Fin 3 → ℤ)
    (hbox : ∀ j i, (y j i).natAbs ≤ H)
    (hgrad : ∀ j, ∃ v, eval (y j)
      (pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) ≠ 0)
    (hclasses : ∀ p ∈ P,
      (Fintype.card (SurfaceOccupiedSmoothResidueClass p
        (surfaceHypersurfaceFirstChartDehomogenize F) y) : ℝ) ≤ K * (p : ℝ) ^ 2) :
    (2 * Real.sqrt 2 / 3) / Real.sqrt K *
          (Fintype.card ι : ℝ) ^ (3 / 2 : ℝ) *
          (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) -
        (Real.sqrt 2 * (e + d + 2 : ℕ) / Real.sqrt K) *
          ((Fintype.card ι : ℝ) * Real.sqrt (Fintype.card ι : ℝ)) -
        2 * Fintype.card ι * (∑ p ∈ P, Real.log (p : ℝ)) ≤
      ∑ p ∈ P,
        (hypersurfaceSmoothResidueExponent p
          (surfaceHypersurfaceFirstChartDehomogenize F) y : ℝ) * Real.log (p : ℝ) := by
  classical
  have hprodR (j : ι) (_hj : j ∈ (Finset.univ : Finset ι)) :
      (∏ p ∈ P.filter (hypersurfaceAffineGradientBadReduction F (y j)), (p : ℝ)) ≤
        (H : ℝ) ^ ((e + d + 2 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    have h := badPrimeProduct_le_uniform_height_power F hH hdegree hcoeff
      P hP (y j) (hbox j) (hgrad j)
    have hcast : ((∏ p ∈ P.filter (hypersurfaceAffineGradientBadReduction F (y j)), p : ℕ) : ℝ) ≤
        ((H ^ (e + d + 2) : ℕ) : ℝ) := by exact_mod_cast h
    simpa only [Nat.cast_prod, Nat.cast_pow] using hcast
  have hHone : (1 : ℝ) < H := by
    exact_mod_cast (show 1 < H by omega)
  have hbad := smoothSurface_discard_log_loss_le_of_row_products Finset.univ P
    (fun j => hypersurfaceAffineGradientBadReduction F (y j)) H
    ((e + d + 2 : ℕ) : ℝ) hHone
    (fun p hp => (hP p hp).pos) hlarge hprodR
  apply hypersurfaceSmoothResidueExponent_primeSum_lower_bound_of_badReduction
    P _ y K (e + d + 2 : ℕ) hK hP hclasses
  simpa only [Fintype.card_subtype, Finset.card_univ,
    not_surfaceGradientNonzeroMod_firstChart_iff_badReduction] using hbad

end CubicTenVariables.FixedDegreeGradientPrimeSum
