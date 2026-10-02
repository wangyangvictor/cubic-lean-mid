import CubicTenVariables.NormedPolynomialChart
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Selected gradient coordinates and a quantitative local inverse estimate

A nonzero, possibly nonprincipal Hessian minor makes the selected first
partials together with the untouched input coordinates locally
antilipschitz. Both index selections are derived to be injective from the
literal minor. No inverse estimate or Jacobian identity is assumed.
-/

noncomputable section
namespace CubicTenVariables.SelectedGradientCoordinates

open MvPolynomial HessianTheorem11
open scoped NNReal

/-- Strict differentiability with an invertible derivative gives an actual
open neighborhood on which the map has a lower distance bound. No
completeness assumption is needed for this implication. -/
theorem exists_open_antilipschitz_of_strictFDerivAt
    {K E G : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup G] [NormedSpace K G]
    (f : E → G) (x : E) (L : E ≃L[K] G)
    (hf : HasStrictFDerivAt f (L : E →L[K] G) x) :
    ∃ (U : Set E) (C : ℝ≥0),
      x ∈ U ∧ IsOpen U ∧ AntilipschitzWith C (U.restrict f) := by
  obtain ⟨U, hx, hU, ha⟩ := hf.approximates_deriv_on_open_nhds
  refine ⟨U, _, hx, hU, ha.antilipschitz ?_⟩
  exact L.subsingleton_or_nnnorm_symm_pos.imp id
    (fun h => NNReal.half_lt_self (ne_of_gt (inv_pos.mpr h)))

theorem rows_injective_of_submatrix_det_ne_zero
    {K : Type*} [CommRing K] {n r : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (rows cols : Fin r → Fin n)
    (hdet : (M.submatrix rows cols).det ≠ 0) : Function.Injective rows := by
  intro a b hab
  by_contra hne
  exact hdet (Matrix.det_zero_of_row_eq hne (by ext c; simp [Matrix.submatrix, hab]))

theorem cols_injective_of_submatrix_det_ne_zero
    {K : Type*} [CommRing K] {n r : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (rows cols : Fin r → Fin n)
    (hdet : (M.submatrix rows cols).det ≠ 0) : Function.Injective cols := by
  intro a b hab
  by_contra hne
  exact hdet (Matrix.det_zero_of_column_eq hne (by intro c; simp [Matrix.submatrix, hab]))

/-- The coordinates not among the selected input columns. -/
abbrev Complement {n r : ℕ} (cols : Fin r → Fin n) :=
  {j : Fin n // j ∉ Set.range cols}

attribute [local instance] Classical.propDecidable

/-- The literal linear map: selected matrix rows, followed by untouched
input coordinates. Rows and columns need not coincide. -/
def selectedLinearMap {K : Type*} [Field K] {n r : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (rows cols : Fin r → Fin n) :
    (Fin n → K) →ₗ[K] ((Fin r → K) × (Complement cols → K)) where
  toFun v := (fun a => (M.mulVec v) (rows a), fun j => v j)
  map_add' v w := by
    ext a <;> simp [Matrix.mulVec_add]
  map_smul' c v := by
    ext a <;> simp [Matrix.mulVec_smul]

@[simp] theorem selectedLinearMap_apply {K : Type*} [Field K] {n r : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (rows cols : Fin r → Fin n) (v : Fin n → K) :
    selectedLinearMap M rows cols v =
      (fun a => ∑ j, M (rows a) j * v j, fun j : Complement cols => v j) := rfl

/-- A vector supported on the selected columns has its matrix pairing
computed by the selected submatrix. -/
theorem sum_eq_selected_sum {K : Type*} [Field K] {n r : ℕ}
    (cols : Fin r → Fin n) (hc : Function.Injective cols)
    (a v : Fin n → K) (hv : ∀ j, j ∉ Set.range cols → v j = 0) :
    (∑ j, a j * v j) = ∑ b, a (cols b) * v (cols b) := by
  exact (Fintype.sum_of_injective cols hc _ _
    (fun j hj => by simp [hv j hj]) (fun _ => rfl)).symm

/-- The selected minor is the only invertibility assumption needed for
this actual linear coordinate map. -/
theorem selectedLinearMap_injective {K : Type*} [Field K] {n r : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (rows cols : Fin r → Fin n)
    (hdet : (M.submatrix rows cols).det ≠ 0) :
    Function.Injective (selectedLinearMap M rows cols) := by
  have hc := cols_injective_of_submatrix_det_ne_zero M rows cols hdet
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro v hv
  have hvcomp : ∀ j, j ∉ Set.range cols → v j = 0 := by
    intro j hj
    exact congrFun (congrArg Prod.snd hv) ⟨j, hj⟩
  have hselected : (M.submatrix rows cols).mulVec (fun a => v (cols a)) = 0 := by
    funext a
    have hrow := congrFun (congrArg Prod.fst hv) a
    change (∑ j, M (rows a) j * v j) = 0 at hrow
    rw [sum_eq_selected_sum cols hc _ v hvcomp] at hrow
    exact hrow
  have hselectedzero : (fun a => v (cols a)) = 0 := by
    apply Matrix.mulVec_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
    simpa using hselected
  funext j
  by_cases hj : j ∈ Set.range cols
  · obtain ⟨a, rfl⟩ := hj
    exact congrFun hselectedzero a
  · exact hvcomp j hj

/-- Exact dimension equality for the selected coordinates and their
complement, including empty selections and zero ambient dimension. -/
theorem finrank_selected_output {K : Type*} [Field K] {n r : ℕ}
    (cols : Fin r → Fin n) (hc : Function.Injective cols) :
    Module.finrank K (Fin n → K) =
      Module.finrank K ((Fin r → K) × (Complement cols → K)) := by
  have hrange : Fintype.card (Set.range cols) = r := by
    rw [← Fintype.card_congr (Equiv.ofInjective cols hc), Fintype.card_fin]
  have hle : r ≤ n := by
    simpa using Fintype.card_le_of_injective cols hc
  simp only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  change n = r + Fintype.card {j : Fin n // ¬ j ∈ Set.range cols}
  rw [Fintype.card_subtype_compl, Fintype.card_fin, hrange]
  omega

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]

/-- The selected linear map with its proved finite-dimensional continuity. -/
def selectedCLM {n r : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (rows cols : Fin r → Fin n) :
    (Fin n → K) →L[K] ((Fin r → K) × (Complement cols → K)) :=
  (selectedLinearMap M rows cols).toContinuousLinearMap

@[simp] theorem selectedCLM_apply {n r : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (rows cols : Fin r → Fin n) (v : Fin n → K) :
    selectedCLM M rows cols v =
      (fun a => ∑ j, M (rows a) j * v j, fun j : Complement cols => v j) := rfl

/-- Actual derivative-coordinate equivalence furnished by the nonzero minor. -/
def selectedCLE {n r : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (rows cols : Fin r → Fin n) (hdet : (M.submatrix rows cols).det ≠ 0) :
    (Fin n → K) ≃L[K] ((Fin r → K) × (Complement cols → K)) :=
  ((selectedLinearMap M rows cols).linearEquivOfInjective
    (selectedLinearMap_injective M rows cols hdet)
    (finrank_selected_output cols
      (cols_injective_of_submatrix_det_ne_zero M rows cols hdet))).toContinuousLinearEquiv

@[simp] theorem selectedCLE_toContinuousLinearMap {n r : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (rows cols : Fin r → Fin n)
    (hdet : (M.submatrix rows cols).det ≠ 0) :
    (selectedCLE M rows cols hdet : (Fin n → K) →L[K]
      ((Fin r → K) × (Complement cols → K))) = selectedCLM M rows cols := by
  ext v : 1
  rfl

/-- Selected actual formal first partials, followed by the untouched
input coordinates. The input-column choice is independent of the
selected gradient-row choice. -/
def selectedGradientCoordinates {n r : ℕ} (F : MvPolynomial (Fin n) K)
    (rows cols : Fin r → Fin n) (z : Fin n → K) :
    (Fin r → K) × (Complement cols → K) :=
  (fun a => eval z (pderiv (rows a) F), fun j => z j)

theorem hasStrictFDerivAt_selectedGradientCoordinates {n r : ℕ}
    (F : MvPolynomial (Fin n) K) (rows cols : Fin r → Fin n) (x : Fin n → K) :
    HasStrictFDerivAt (selectedGradientCoordinates F rows cols)
      (selectedCLM (hessian F x) rows cols) x := by
  have hfirst : HasStrictFDerivAt
      (fun z : Fin n → K => fun a : Fin r => eval z (pderiv (rows a) F))
      (ContinuousLinearMap.pi fun a =>
        NormedPolynomialChart.evalDerivative (pderiv (rows a) F) x) x :=
    hasStrictFDerivAt_pi.mpr
      (fun a => NormedPolynomialChart.hasStrictFDerivAt_eval (pderiv (rows a) F) x)
  have hsecond : HasStrictFDerivAt
      (fun z : Fin n → K => fun j : Complement cols => z j)
      (ContinuousLinearMap.pi fun j : Complement cols =>
        (ContinuousLinearMap.proj (j : Fin n) : (Fin n → K) →L[K] K)) x :=
    hasStrictFDerivAt_pi.mpr (fun j => hasStrictFDerivAt_apply (j : Fin n) x)
  convert hfirst.prodMk hsecond using 1
  ext v a <;> simp [selectedCLM_apply, NormedPolynomialChart.evalDerivative_apply,
    hessian, hessianPolynomial]

/-- The derivative is the actual continuous linear equivalence determined
by the displayed possibly nonprincipal Hessian minor. -/
theorem hasStrictFDerivAt_selectedGradientCoordinates_equiv {n r : ℕ}
    (F : MvPolynomial (Fin n) K) (rows cols : Fin r → Fin n) (x : Fin n → K)
    (hdet : ((hessian F x).submatrix rows cols).det ≠ 0) :
    HasStrictFDerivAt (selectedGradientCoordinates F rows cols)
      (selectedCLE (hessian F x) rows cols hdet :
        (Fin n → K) →L[K] ((Fin r → K) × (Complement cols → K))) x := by
  simpa using hasStrictFDerivAt_selectedGradientCoordinates F rows cols x

/-- A nonzero actual Hessian minor provides an open patch with a genuine
lower-distance estimate for selected gradients and untouched coordinates. -/
theorem exists_selectedGradient_antilipschitz {n r : ℕ}
    (F : MvPolynomial (Fin n) K) (rows cols : Fin r → Fin n) (x : Fin n → K)
    (hdet : ((hessian F x).submatrix rows cols).det ≠ 0) :
    ∃ (U : Set (Fin n → K)) (C : ℝ≥0), x ∈ U ∧ IsOpen U ∧
      AntilipschitzWith C (U.restrict (selectedGradientCoordinates F rows cols)) :=
  exists_open_antilipschitz_of_strictFDerivAt _ x
    (selectedCLE (hessian F x) rows cols hdet)
    (hasStrictFDerivAt_selectedGradientCoordinates_equiv F rows cols x hdet)

end CubicTenVariables.SelectedGradientCoordinates
