import CubicTenVariables.NormedPolynomialChart
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-!
# Open coordinate patches of actual smooth polynomial zeros

Over any complete nontrivially normed field, a polynomial zero with a
nonzero selected first partial has a patch whose remaining coordinates fill
an open neighborhood. The zeros stay in any prescribed open neighborhood,
and the same partial remains nonzero. The proof restricts the actual
coordinate-replacement chart and uses its inverse on the zero-coordinate
slice. It requires no smoothness theorem for that inverse.
-/

noncomputable section

namespace CubicTenVariables.ZeroPatch

open MvPolynomial
open NormedPolynomialChart

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]

/-- Near a smooth zero, the remaining coordinates range over a nonempty
open neighborhood, with actual smooth zeros lifting every parameter value.
The lifted points all lie in the prescribed open neighborhood `U`. -/
theorem exists_open_zero_patch {m : ℕ}
    (F : MvPolynomial (Fin (m + 1)) K) (i : Fin (m + 1))
    (x : Fin (m + 1) → K) (hx : eval x F = 0)
    (hi : eval x (pderiv i F) ≠ 0)
    (U : Set (Fin (m + 1) → K)) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ V : Set (Fin m → K), IsOpen V ∧ i.removeNth x ∈ V ∧ V.Nonempty ∧
      ∀ y ∈ V, ∃ z : Fin (m + 1) → K,
        z ∈ U ∧ eval z F = 0 ∧ eval z (pderiv i F) ≠ 0 ∧ i.removeNth z = y := by
  classical
  let S : Set (Fin (m + 1) → K) := U ∩ {z | eval z (pderiv i F) ≠ 0}
  have hpartial : IsOpen {z : Fin (m + 1) → K | eval z (pderiv i F) ≠ 0} :=
    isOpen_ne.preimage (contDiff_eval (pderiv i F)).continuous
  have hS : IsOpen S := hU.inter hpartial
  let e := (coordinateChart F i x hi).restrOpen S hS
  have hxe : x ∈ e.source := ⟨mem_coordinateChart_source F i x hi, hxU, hi⟩
  let V : Set (Fin m → K) := (fun y => i.insertNth (0 : K) y) ⁻¹' e.target
  have hV : IsOpen V :=
    e.open_target.preimage (continuous_const.finInsertNth i continuous_id)
  have hcentre : e x = i.insertNth (0 : K) (i.removeNth x) := by
    change coordinateMap F i x = _
    simp only [coordinateMap, Fin.insertNth_removeNth, hx]
  have hxV : i.removeNth x ∈ V := by
    change i.insertNth (0 : K) (i.removeNth x) ∈ e.target
    rw [← hcentre]
    exact e.map_source hxe
  refine ⟨V, hV, hxV, ⟨i.removeNth x, hxV⟩, ?_⟩
  intro y hy
  have hyt : i.insertNth (0 : K) y ∈ e.target := hy
  let z := e.symm (i.insertNth (0 : K) y)
  have hzs : z ∈ e.source := e.map_target hyt
  have hzS : z ∈ S := hzs.2
  have hcoord : coordinateMap F i z = i.insertNth (0 : K) y := e.right_inv hyt
  have hzero : eval z F = 0 := by
    have he := congrFun hcoord i
    simpa only [coordinateMap_apply_same, Fin.insertNth_apply_same] using he
  have hremove : i.removeNth z = y := by
    have he := congrArg i.removeNth hcoord
    simpa only [coordinateMap, Fin.removeNth_update, Fin.removeNth_insertNth] using he
  exact ⟨z, hzS.1, hzero, hzS.2, hremove⟩

end CubicTenVariables.ZeroPatch
