import HessianTheorem11.UnconditionalValuationWeights
import HessianTheorem11.PolynomialWeightTransport
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! Diagonal restriction and valuation support for actual polynomials. -/
noncomputable section
namespace HessianTheorem11.UnconditionalValuationWeights
open MvPolynomial PolynomialRestriction
variable {K σ : Type*} [Field K] [Fintype σ] [DecidableEq σ]

/-- Exact coefficient formula for an arbitrary diagonal matrix, with no
assumption that the diagonal entries are powers of one parameter. -/
theorem restrict_diagonal_monomial (d : σ → K) (e : σ →₀ ℕ) (c : K) :
    restrict (Matrix.diagonal d) (monomial e c) =
      monomial e (c * ∏ i, d i ^ e i) := by
  have hlin (i : σ) : linearForms (Matrix.diagonal d) i = C (d i) * X i := by
    simp [linearForms,Matrix.diagonal_apply,apply_ite,ite_mul]
  change aeval _ (monomial e c) = _
  rw [aeval_monomial]
  simp only [hlin,mul_pow,Finset.prod_mul_distrib,←map_pow,←map_prod,Finsupp.prod]
  have hp : (∏ i ∈ e.support, d i ^ e i) = ∏ i, d i ^ e i :=
    e.prod_fintype _ (fun _ => pow_zero _)
  rw [hp,←C_mul_monomial,monomial_eq]
  simp [Finsupp.prod]

theorem coeff_restrict_diagonal (d : σ → K) (F : MvPolynomial σ K) (e : σ →₀ ℕ) :
    coeff e (restrict (Matrix.diagonal d) F) = coeff e F * ∏ i, d i ^ e i := by
  classical
  have h : restrict (Matrix.diagonal d) F =
      ∑ m ∈ F.support, monomial m (coeff m F * ∏ i, d i ^ m i) := by
    calc
      _ = ∑ m ∈ F.support, restrict (Matrix.diagonal d) (monomial m (coeff m F)) := by
        simpa only [restrict,map_sum] using
          congrArg (restrict (Matrix.diagonal d)) F.as_sum
      _ = _ := by
        apply Finset.sum_congr rfl
        intro m hm
        exact restrict_diagonal_monomial d m (coeff m F)
  rw [h]
  by_cases he : coeff e F = 0 <;>
    simp [coeff_sum,coeff_monomial,Finset.sum_ite_eq',he]

variable (V : ValuationSubring K)

def residuePolynomial (F : MvPolynomial σ V) : MvPolynomial σ (IsLocalRing.ResidueField V) :=
  map (IsLocalRing.residue V) F

omit [Fintype σ] [DecidableEq σ] in
theorem residue_coeff_ne_zero_iff (F : MvPolynomial σ V) (e : σ →₀ ℕ) :
    coeff e (residuePolynomial V F) ≠ 0 ↔ coeff e F ∉ IsLocalRing.maximalIdeal V := by
  simp only [residuePolynomial,coeff_map,ne_eq,IsLocalRing.residue_eq_zero_iff]

/-- A residue-supported monomial of an integral polynomial has nonnegative
valuation weight whenever the diagonally transformed polynomial is integral. -/
theorem residue_support_nonnegative {n : ℕ}
    (F P : MvPolynomial (Fin n) V) (d : Fin n → Kˣ)
    (hP : restrict (Matrix.diagonal (fun i => (d i : K))) (map V.subtype F) = map V.subtype P)
    (e : Fin n →₀ ℕ) (he : coeff e (residuePolynomial V F) ≠ 0) :
    0 ≤ UnconditionalOrderedWeights.value (fun i => (e i : ℤ))
      (fun i => weight V (d i)) := by
  have hc := (residue_coeff_ne_zero_iff V F e).mp he
  have hv := congrArg (coeff e) hP
  rw [coeff_restrict_diagonal,coeff_map,coeff_map] at hv
  apply character_nonnegative V d (fun i => (e i : ℤ)) (coeff e F) hc
  have heq : ((coeff e F : V) : K) * ((∏ i, d i ^ (e i : ℤ) : Kˣ) : K) = ((coeff e P : V) : K) := by
    simpa only [Units.coe_prod,Units.val_zpow_eq_zpow_val,zpow_natCast] using hv
  rw [heq]
  exact (coeff e P).property

/-- If the scaled coefficient vanishes in the residue polynomial, the
valuation weight of a surviving source monomial is strictly positive. -/
theorem residue_support_positive {n : ℕ}
    (F P : MvPolynomial (Fin n) V) (d : Fin n → Kˣ)
    (hP : restrict (Matrix.diagonal (fun i => (d i : K))) (map V.subtype F) = map V.subtype P)
    (e : Fin n →₀ ℕ) (he : coeff e (residuePolynomial V F) ≠ 0)
    (hz : coeff e (residuePolynomial V P) = 0) :
    0 < UnconditionalOrderedWeights.value (fun i => (e i : ℤ))
      (fun i => weight V (d i)) := by
  have hc := (residue_coeff_ne_zero_iff V F e).mp he
  have hv := congrArg (coeff e) hP
  rw [coeff_restrict_diagonal,coeff_map,coeff_map] at hv
  have hcz : coeff e P ∈ IsLocalRing.maximalIdeal V := by
    simpa only [residuePolynomial,coeff_map,IsLocalRing.residue_eq_zero_iff] using hz
  apply character_positive V d (fun i => (e i : ℤ)) (coeff e F) (coeff e P) hc hcz
  simpa only [Units.coe_prod,Units.val_zpow_eq_zpow_val,zpow_natCast] using hv.symm

/-- Removing an integral invertible right frame from an integral transformed
polynomial keeps the middle diagonal transform integral. This uses the actual
inverse frame over V and actual polynomial restriction, not coefficient bounds. -/
theorem exists_integral_diagonal_middle {n : ℕ}
    (F P : MvPolynomial (Fin n) V) (A B : Matrix (Fin n) (Fin n) V)
    (hB : IsUnit B) (d : Fin n → K)
    (he : restrict (UnconditionalValuationMatrix.matrixMap V A * Matrix.diagonal d *
      UnconditionalValuationMatrix.matrixMap V B) (map V.subtype F) = map V.subtype P) :
    ∃ Q : MvPolynomial (Fin n) V,
      restrict (Matrix.diagonal d) (map V.subtype (restrict A F)) = map V.subtype Q := by
  obtain ⟨b,rfl⟩ := hB
  refine ⟨restrict (↑(b⁻¹) : Matrix (Fin n) (Fin n) V) P,?_⟩
  have hbb : UnconditionalValuationMatrix.matrixMap V (↑b : Matrix (Fin n) (Fin n) V) *
      UnconditionalValuationMatrix.matrixMap V (↑(b⁻¹) : Matrix (Fin n) (Fin n) V) = 1 := by
    rw [←map_mul]
    simp
  have h := congrArg (restrict (UnconditionalValuationMatrix.matrixMap V (↑(b⁻¹) : Matrix (Fin n) (Fin n) V))) he
  rw [PolynomialWeightTransport.restrict_restrict,
    Matrix.mul_assoc _ _ (UnconditionalValuationMatrix.matrixMap V (↑(b⁻¹) : Matrix (Fin n) (Fin n) V)),hbb,
    Matrix.mul_one] at h
  rw [←PolynomialWeightTransport.restrict_restrict] at h
  simpa only [map_restrict] using h

end HessianTheorem11.UnconditionalValuationWeights
