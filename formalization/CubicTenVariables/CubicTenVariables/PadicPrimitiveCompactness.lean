import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sequences

/-! Compactness closes a supplied sequence of primitive approximate zeros.
The coordinate equal to one may vary along the sequence. No construction
of approximate zeros, matrix descent, or local-solubility input is assumed
implicitly. No homogeneity is needed for this final compactness step. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PadicPrimitiveCompactness
open MvPolynomial Filter Topology

variable {p n : ℕ} [Fact p.Prime]

/-- A finite union of closed coordinate hyperplanes inside integral vectors. -/
def coordinateOne : Set (Fin n → ℤ_[p]) := {x | ∃ i, x i=1}

theorem isCompact_coordinateOne : IsCompact (coordinateOne (p := p) (n := n)) := by
  have hc : IsClosed (coordinateOne (p := p) (n := n)) := by
    unfold coordinateOne
    simp only [Set.setOf_exists]
    exact isClosed_iUnion_of_finite (fun i => isClosed_eq (continuous_apply i) continuous_const)
  exact hc.isCompact

/-- A sequence of integral vectors with one coordinate exactly one and
polynomial values tending to zero has an actual integral zero with one
coordinate exactly one. The selected coordinate need not be constant. -/
theorem exists_integral_zero_of_tendsto (F : MvPolynomial (Fin n) ℚ_[p])
    (x : ℕ → (Fin n → ℤ_[p])) (hx : ∀ r, ∃ i, x r i=1)
    (hlim : Tendsto (fun r => eval (fun i => (x r i : ℚ_[p])) F) atTop (𝓝 0)) :
    ∃ y : Fin n → ℤ_[p], (∃ i, y i=1) ∧ eval (fun i => (y i : ℚ_[p])) F=0 := by
  obtain ⟨y,hy,φ,hφ,hconv⟩ := isCompact_coordinateOne.tendsto_subseq hx
  have hc : Continuous (fun y : Fin n → ℤ_[p] => eval (fun i => (y i : ℚ_[p])) F) :=
    F.continuous_eval.comp (continuous_pi (fun i =>
      continuous_subtype_val.comp (continuous_apply i)))
  refine ⟨y,hy,?_⟩
  exact tendsto_nhds_unique (hc.continuousAt.tendsto.comp hconv) (hlim.comp hφ.tendsto_atTop)

/-- The same conclusion displayed literally in the p-adic field, including
integrality, the coordinate-one normalization, and nonzeroness. -/
theorem exists_zero_of_tendsto (F : MvPolynomial (Fin n) ℚ_[p])
    (x : ℕ → (Fin n → ℤ_[p])) (hx : ∀ r, ∃ i, x r i=1)
    (hlim : Tendsto (fun r => eval (fun i => (x r i : ℚ_[p])) F) atTop (𝓝 0)) :
    ∃ y : Fin n → ℚ_[p], (∀ i, ‖y i‖≤1) ∧ (∃ i, y i=1) ∧ y≠0 ∧ eval y F=0 := by
  obtain ⟨y,⟨i,hi⟩,hy⟩ := exists_integral_zero_of_tendsto F x hx hlim
  refine ⟨fun j => (y j : ℚ_[p]),fun j => (y j).property,⟨i,?_⟩,?_,hy⟩
  · change (y i : ℚ_[p])=1
    rw [hi,PadicInt.coe_one]
  · intro hzero
    have h := congrFun hzero i
    exact one_ne_zero (by simpa only [hi,PadicInt.coe_one,Pi.zero_apply] using h)

end CubicTenVariables.PadicPrimitiveCompactness
