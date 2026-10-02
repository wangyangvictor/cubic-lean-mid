import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Constant polynomial norms on an explicit p-adic neighborhood

The neighborhood below is defined by strict inequalities for the actual
polynomial values and for every coordinate displacement. Polynomial
continuity makes it open. The ultrametric inequality makes the nonzero
polynomial norms locally constant and preserves integral coordinates and
a selected unit coordinate. No compactness or implicit-function premise
is used.
-/

noncomputable section

namespace CubicTenVariables.PadicPolynomialNeighborhood

open MvPolynomial

variable {p n : ℕ} [Fact p.Prime]

/-- An explicit simultaneous neighborhood: both polynomial values move by
less than their nonzero norms, and every coordinate moves by norm less than one. -/
def polynomialNeighborhood
    (P D : MvPolynomial (Fin n) ℚ_[p]) (x : Fin n → ℚ_[p]) :
    Set (Fin n → ℚ_[p]) :=
  {y | ‖eval y P - eval x P‖ < ‖eval x P‖} ∩
  {y | ‖eval y D - eval x D‖ < ‖eval x D‖} ∩
  {y | ∀ i, ‖y i - x i‖ < 1}

theorem isOpen_polynomialNeighborhood
    (P D : MvPolynomial (Fin n) ℚ_[p]) (x : Fin n → ℚ_[p]) :
    IsOpen (polynomialNeighborhood P D x) := by
  have hcoords : IsOpen {y : Fin n → ℚ_[p] | ∀ i, ‖y i - x i‖ < 1} := by
    simpa only [Set.iInter_setOf] using
      (isOpen_iInter_of_finite (fun i : Fin n =>
        isOpen_lt (((continuous_apply i).sub continuous_const).norm) continuous_const))
  exact ((isOpen_lt ((P.continuous_eval.sub continuous_const).norm) continuous_const).inter
    (isOpen_lt ((D.continuous_eval.sub continuous_const).norm) continuous_const)).inter hcoords

theorem mem_polynomialNeighborhood
    (P D : MvPolynomial (Fin n) ℚ_[p]) (x : Fin n → ℚ_[p])
    (hP : eval x P ≠ 0) (hD : eval x D ≠ 0) :
    x ∈ polynomialNeighborhood P D x := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa only [Set.mem_setOf_eq, sub_self, norm_zero] using norm_pos_iff.mpr hP
  · simpa only [Set.mem_setOf_eq, sub_self, norm_zero] using norm_pos_iff.mpr hD
  · intro i
    simp

/-- On the explicit neighborhood, the two actual polynomial values have
exactly the norms they had at its center. -/
theorem polynomial_norms_eq
    (P D : MvPolynomial (Fin n) ℚ_[p]) (x y : Fin n → ℚ_[p])
    (hy : y ∈ polynomialNeighborhood P D x) :
    ‖eval y P‖ = ‖eval x P‖ ∧ ‖eval y D‖ = ‖eval x D‖ :=
  ⟨Padic.norm_eq_of_norm_sub_lt_right hy.1.1,
    Padic.norm_eq_of_norm_sub_lt_right hy.1.2⟩

/-- Integral coordinates remain integral on this open neighborhood,
including coordinates that vanish at the center. -/
theorem coordinate_norms_le_one
    (P D : MvPolynomial (Fin n) ℚ_[p]) (x y : Fin n → ℚ_[p])
    (hx : ∀ i, ‖x i‖ ≤ 1) (hy : y ∈ polynomialNeighborhood P D x) :
    ∀ i, ‖y i‖ ≤ 1 := by
  intro i
  calc
    ‖y i‖ = ‖(y i - x i) + x i‖ := by rw [sub_add_cancel]
    _ ≤ max ‖y i - x i‖ ‖x i‖ := Padic.nonarchimedean _ _
    _ ≤ 1 := max_le (le_of_lt (hy.2 i)) (hx i)

/-- A selected unit coordinate retains norm exactly one. -/
theorem selected_coordinate_norm_eq_one
    (P D : MvPolynomial (Fin n) ℚ_[p]) (x y : Fin n → ℚ_[p])
    (j : Fin n) (hj : ‖x j‖ = 1) (hy : y ∈ polynomialNeighborhood P D x) :
    ‖y j‖ = 1 := by
  have he : ‖y j‖ = ‖x j‖ :=
    Padic.norm_eq_of_norm_sub_lt_right (by simpa only [hj] using hy.2 j)
  exact he.trans hj

/-- The two nonzero polynomial norms and a selected unit coordinate can
be preserved simultaneously on an actual open neighborhood. -/
theorem exists_open_constant_norm_neighborhood
    (P D : MvPolynomial (Fin n) ℚ_[p]) (x : Fin n → ℚ_[p])
    (hP : eval x P ≠ 0) (hD : eval x D ≠ 0)
    (j : Fin n) (hj : ‖x j‖ = 1) :
    ∃ U : Set (Fin n → ℚ_[p]), IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ‖eval y P‖ = ‖eval x P‖ ∧
        ‖eval y D‖ = ‖eval x D‖ ∧ ‖y j‖ = 1 := by
  refine ⟨polynomialNeighborhood P D x, isOpen_polynomialNeighborhood P D x,
    mem_polynomialNeighborhood P D x hP hD, ?_⟩
  intro y hy
  have h := polynomial_norms_eq P D x y hy
  exact ⟨h.1, h.2, selected_coordinate_norm_eq_one P D x y j hj hy⟩

/-- At an integral center with a unit coordinate, the same neighborhood
preserves integrality, that unit coordinate, and both polynomial norms. -/
theorem exists_open_integral_constant_norm_neighborhood
    (P D : MvPolynomial (Fin n) ℚ_[p]) (x : Fin n → ℚ_[p])
    (hP : eval x P ≠ 0) (hD : eval x D ≠ 0)
    (hx : ∀ i, ‖x i‖ ≤ 1) (j : Fin n) (hj : ‖x j‖ = 1) :
    ∃ U : Set (Fin n → ℚ_[p]), IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, (∀ i, ‖y i‖ ≤ 1) ∧ ‖y j‖ = 1 ∧
        ‖eval y P‖ = ‖eval x P‖ ∧ ‖eval y D‖ = ‖eval x D‖ := by
  refine ⟨polynomialNeighborhood P D x, isOpen_polynomialNeighborhood P D x,
    mem_polynomialNeighborhood P D x hP hD, ?_⟩
  intro y hy
  exact ⟨coordinate_norms_le_one P D x y hx hy,
    selected_coordinate_norm_eq_one P D x y j hj hy,
    polynomial_norms_eq P D x y hy⟩

end CubicTenVariables.PadicPolynomialNeighborhood
