import CubicTenVariables.FiniteClassMajorant
import CubicTenVariables.IntegerResidueClasses
import CubicTenVariables.WeightedResidueMaximum

/-! Extract a residue-class majorant from the actual unit-weight residue
maximum inequality on every subset of the finite frequency set. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ResidueMajorantExtraction
open IntegerResidueClasses (residue)
open scoped BigOperators

/-- A transversal has at most one point in each residue class. -/
theorem maximum_unit_le_one (m : ℕ) [NeZero m] {n : ℕ}
    (U : Finset (Fin n → ℤ))
    (hinj : Set.InjOn (residue m) (U : Set (Fin n → ℤ))) :
    WeightedResidueMaximum.maximum m U (fun _ => 1) ≤ 1 := by
  classical
  obtain ⟨b,hb⟩ := WeightedResidueMaximum.maximum_attained m U (fun _ => 1)
  rw [hb,WeightedResidueMaximum.classWeight]
  have hcard : (U.filter (fun v => (fun k => (v k : ZMod m)) = b)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro v hv w hw
    obtain ⟨hv,hvb⟩ := Finset.mem_filter.mp hv
    obtain ⟨hw,hwb⟩ := Finset.mem_filter.mp hw
    exact hinj hv hw (hvb.trans hwb.symm)
  have hreal : ((U.filter (fun v => (fun k => (v k : ZMod m)) = b)).card : ℝ) ≤ 1 := by
    exact_mod_cast hcard
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using hreal

/-- Only the unit-weight inequalities on subsets are required. The
extracted majorant dominates `a` on the original finite set and has mass
at most `K`; the function `a` itself need not be periodic. -/
theorem exists_majorant (m : ℕ) [NeZero m] {n : ℕ}
    (V : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → ℝ) (K : ℝ)
    (ha : ∀ v ∈ V, 0 ≤ a v) (hK : 0 ≤ K)
    (hbound : ∀ U : Finset (Fin n → ℤ), U ⊆ V →
      (∑ v ∈ U, a v) ≤ K*WeightedResidueMaximum.maximum m U (fun _ => 1)) :
    ∃ P : (Fin n → ZMod m) → ℝ, (∀ b, 0 ≤ P b) ∧
      (∀ v ∈ V, a v ≤ P (residue m v)) ∧ (∑ b, P b) ≤ K := by
  apply FiniteClassMajorant.exists_majorant V (residue m) a K ha hK
  intro U hU hinj
  have hm := mul_le_mul_of_nonneg_left (maximum_unit_le_one m U hinj) hK
  simpa only [mul_one] using (hbound U hU).trans hm

end CubicTenVariables.ResidueMajorantExtraction
