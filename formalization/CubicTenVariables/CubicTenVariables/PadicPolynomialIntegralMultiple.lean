import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! A nonzero scalar clears the p-adic denominators of a finite polynomial.
The scalar is the inverse of a coefficient of maximal norm. This constructs
the actual integral polynomial and preserves its homogeneous degree. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PadicPolynomialIntegralMultiple
open MvPolynomial

/-- Every finite polynomial over Qp has a nonzero scalar multiple with
actual integral coefficients. The zero polynomial is included. -/
theorem exists_integral_multiple {p : ℕ} [Fact p.Prime] {σ : Type*}
    (F : MvPolynomial σ ℚ_[p]) :
    ∃ c : ℚ_[p], c≠0 ∧ ∃ G : MvPolynomial σ ℤ_[p],
      map (algebraMap ℤ_[p] ℚ_[p]) G=C c*F := by
  classical
  by_cases hF : F=0
  · subst F
    exact ⟨1,one_ne_zero,0,by simp⟩
  obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image F.support
    (fun m => ‖coeff m F‖) (support_nonempty.mpr hF)
  have hj0 : coeff j F≠0 := mem_support_iff.mp hj
  let c : ℚ_[p] := (coeff j F)⁻¹
  have hbound (m : σ →₀ ℕ) : ‖c*coeff m F‖≤1 := by
    have hle : ‖coeff m F‖≤‖coeff j F‖ := by
      by_cases hm : m∈F.support
      · exact hmax m hm
      · rw [notMem_support_iff.mp hm,norm_zero]
        exact norm_nonneg _
    calc
      ‖c*coeff m F‖=‖coeff m F‖/‖coeff j F‖ := by
        simp only [c,norm_mul,norm_inv,div_eq_mul_inv,mul_comm]
      _ ≤ 1 := (div_le_one (norm_pos_iff.mpr hj0)).mpr hle
  have hrange : C c*F ∈ Set.range (map (algebraMap ℤ_[p] ℚ_[p])) := by
    apply mem_range_map_iff_coeffs_subset.mpr
    intro r hr
    obtain ⟨m,_,hm⟩ := mem_coeffs_iff.mp hr
    rw [hm,coeff_C_mul]
    exact ⟨⟨c*coeff m F,hbound m⟩,rfl⟩
  obtain ⟨G,hG⟩ := hrange
  exact ⟨c,inv_ne_zero hj0,G,hG⟩

/-- Clearing denominators preserves the literal homogeneous degree under
the injective coefficient map from Zp to Qp. -/
theorem exists_homogeneous_integral_multiple {p : ℕ} [Fact p.Prime]
    {σ : Type*} {d : ℕ} (F : MvPolynomial σ ℚ_[p]) (hF : F.IsHomogeneous d) :
    ∃ c : ℚ_[p], c≠0 ∧ ∃ G : MvPolynomial σ ℤ_[p], G.IsHomogeneous d ∧
      map (algebraMap ℤ_[p] ℚ_[p]) G=C c*F := by
  obtain ⟨c,hc,G,hG⟩ := exists_integral_multiple F
  refine ⟨c,hc,G,?_,hG⟩
  apply IsHomogeneous.of_map (f := algebraMap ℤ_[p] ℚ_[p])
    (fun _ _ h => PadicInt.ext h)
  rw [hG]
  exact hF.C_mul c

end CubicTenVariables.PadicPolynomialIntegralMultiple
