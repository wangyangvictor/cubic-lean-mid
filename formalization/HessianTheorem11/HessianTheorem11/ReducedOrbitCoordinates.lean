import HessianTheorem11.NonzeroLimitTransport
import Mathlib.Algebra.Order.Antidiag.Finsupp

/-! Invertible linear coordinates preserve closed special-linear orbits.
Continuity is proved using actual finite polynomial expressions for the
coefficients of a restricted homogeneous form. No orbit theorem is assumed. -/
noncomputable section
namespace HessianTheorem11.ReducedOrbitCoordinates
open MvPolynomial Matrix PolynomialRestriction PolynomialWeightTransport NonzeroLimitTransport
variable {K : Type*} [Field K] {n d : ℕ}

def degreeMonomials (n d : ℕ) : Finset (Fin n →₀ ℕ) :=
  Finset.univ.finsuppAntidiag d

theorem homogeneous_fixed_sum (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d) :
    F = ∑ e ∈ degreeMonomials n d, monomial e (coeff e F) := by
  classical
  conv_lhs => rw [F.as_sum]
  apply Finset.sum_subset
  · intro e he
    apply Finset.mem_finsuppAntidiag'.mpr
    refine ⟨?_, Finset.subset_univ _⟩
    simpa [Finsupp.weight_apply, smul_eq_mul] using hF (Finsupp.mem_support_iff.mp he)
  · intro e he hn
    have hc : coeff e F = 0 := Finsupp.notMem_support_iff.mp hn
    rw [hc, map_zero]

def coefficientRestriction (B : Matrix (Fin n) (Fin n) K) (d : ℕ)
    (e : Fin n →₀ ℕ) : MvPolynomial (Fin n →₀ ℕ) K :=
  ∑ m ∈ degreeMonomials n d,
    C (coeff e (restrict B (monomial m 1))) * X m

theorem eval_coefficientRestriction (B : Matrix (Fin n) (Fin n) K)
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d) (e : Fin n →₀ ℕ) :
    eval (fun m => coeff m F) (coefficientRestriction B d e) =
      coeff e (restrict B F) := by
  classical
  have hm (m : Fin n →₀ ℕ) (c : K) :
      restrict B (monomial m c) = C c * restrict B (monomial m 1) := by
    rw [show monomial m c = C c * monomial m 1 by rw [C_mul_monomial, mul_one]]
    simp [restrict]
  calc
    _ = ∑ m ∈ degreeMonomials n d,
        coeff e (restrict B (monomial m 1)) * coeff m F := by
      simp [coefficientRestriction]
    _ = ∑ m ∈ degreeMonomials n d,
        coeff e (restrict B (monomial m (coeff m F))) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [hm m (coeff m F), coeff_C_mul, mul_comm]
    _ = coeff e (restrict B (∑ m ∈ degreeMonomials n d, monomial m (coeff m F))) := by
      simp only [restrict, map_sum, coeff_sum]
    _ = coeff e (restrict B F) := by rw [← homogeneous_fixed_sum F hF]

theorem slOrbitClosure_homogeneous (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous d) (G : MvPolynomial (Fin n) K)
    (hG : G ∈ slOrbitClosure F) : G.IsHomogeneous d := by
  intro e he
  by_contra hn
  have hz := hG (X e) (by
    intro H hH
    obtain ⟨B,hB,rfl⟩ := hH
    simp only [eval_X]
    by_contra hne
    exact hn (homogeneous_restrict B F hF hne))
  exact he (by simpa only [eval_X] using hz)

theorem restrict_mem_slOrbit (B : Matrix (Fin n) (Fin n) K)
    (hB : IsUnit B.det) (F G : MvPolynomial (Fin n) K)
    (hG : G ∈ slOrbit F) : restrict B G ∈ slOrbit (restrict B F) := by
  obtain ⟨A,hA,rfl⟩ := hG
  refine ⟨B⁻¹*A*B, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_mul, hA, mul_one,
      ← Matrix.det_mul, Matrix.nonsing_inv_mul B hB, Matrix.det_one]
  · rw [restrict_restrict, restrict_restrict]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv B hB, one_mul]

theorem slOrbitClosure_restrict (B : Matrix (Fin n) (Fin n) K)
    (hB : IsUnit B.det) (F G : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous d) (hG : G ∈ slOrbitClosure F) :
    restrict B G ∈ slOrbitClosure (restrict B F) := by
  have hGh := slOrbitClosure_homogeneous F hF G hG
  intro P hP
  let Q := aeval (coefficientRestriction B d) P
  have he (H : MvPolynomial (Fin n) K) (hH : H.IsHomogeneous d) :
      eval (fun m => coeff m H) Q = eval (fun m => coeff m (restrict B H)) P := by
    change aeval (fun m => coeff m H) (aeval (coefficientRestriction B d) P) = _
    rw [MvPolynomial.comp_aeval_apply]
    have hc : (fun e => aeval (fun m => coeff m H) (coefficientRestriction B d e)) =
        (fun e => coeff e (restrict B H)) :=
      funext (eval_coefficientRestriction B H hH)
    rw [hc]
    rfl
  have hz : eval (fun m => coeff m G) Q = 0 := hG Q (by
    intro H hH
    have hHh : H.IsHomogeneous d := by
      obtain ⟨A,hA,rfl⟩ := hH
      exact homogeneous_restrict A F hF
    rw [he H hHh]
    exact hP _ (restrict_mem_slOrbit B hB F H hH))
  rwa [he G hGh] at hz

/-- Closedness of the actual SL orbit is invariant under any invertible
linear coordinate change, for arbitrary homogeneous degree over any field. -/
theorem closedSLOrbit_restrict (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous d) (hclosed : ClosedSLOrbit F)
    (B : Matrix (Fin n) (Fin n) K) (hB : Function.Injective B.mulVec) :
    ClosedSLOrbit (restrict B F) := by
  have hu : IsUnit B.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hB)
  have hi : IsUnit B⁻¹.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.isUnit_nonsing_inv_iff.mpr (Matrix.mulVec_injective_iff_isUnit.mp hB))
  intro G hG
  have hg := slOrbitClosure_restrict B⁻¹ hi (restrict B F) G
    (homogeneous_restrict B F hF) hG
  rw [restrict_restrict, Matrix.mul_nonsing_inv B hu, restrict_one] at hg
  have hm := restrict_mem_slOrbit B hu F (restrict B⁻¹ G) (hclosed hg)
  rwa [restrict_restrict, Matrix.nonsing_inv_mul B hu, restrict_one] at hm

end HessianTheorem11.ReducedOrbitCoordinates
