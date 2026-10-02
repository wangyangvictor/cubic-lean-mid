import CubicTenVariables.SelectedGradientCoordinates
import CubicTenVariables.PadicCongruenceNeighborhood

/-!
# An integral p-adic selected-gradient inverse estimate on a congruence coset

For an actual integer polynomial, the selected first partials are evaluated
in the p-adic integers. Their coercions agree with the actual p-adic field
gradient. A nonzero Hessian minor at an integral center therefore supplies
an open integral patch with a lower-distance estimate, containing a literal
congruence coset. No homogeneity, local-solubility, or inverse-bound premise
is introduced.
-/

noncomputable section
namespace CubicTenVariables.IntegralGradientPatch

open MvPolynomial HessianTheorem11 SelectedGradientCoordinates
open scoped NNReal

variable (p : ℕ) [Fact p.Prime]

/-- The selected formal first partials of the actual integer polynomial,
evaluated in the ring of p-adic integers. -/
def integralSelectedGradient {n r : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (rows : Fin r → Fin n) (z : Fin n → ℤ_[p]) : Fin r → ℤ_[p] :=
  fun a => eval₂ (Int.castRingHom ℤ_[p]) z (pderiv (rows a) F)

/-- The actual integral gradient coerces to the field-valued gradient of
the coefficient image of the same integer polynomial. -/
theorem coe_integralSelectedGradient {n r : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (rows : Fin r → Fin n) (z : Fin n → ℤ_[p]) (a : Fin r) :
    (integralSelectedGradient p F rows z a : ℚ_[p]) =
      eval (fun j => (z j : ℚ_[p]))
        (pderiv (rows a) (map (Int.castRingHom ℚ_[p]) F)) := by
  have hcomp : (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]).comp
      (Int.castRingHom ℤ_[p]) = Int.castRingHom ℚ_[p] := by
    ext m
    simp
  change PadicInt.Coe.ringHom
    (eval₂ (Int.castRingHom ℤ_[p]) z (pderiv (rows a) F)) = _
  rw [eval₂_comp_left, hcomp, pderiv_map, eval_map]
  rfl

/-- Literal pair of integral selected gradient values and untouched
coordinates. This is the output used in the residue comparison. -/
def integralGradientCoordinates {n r : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (rows cols : Fin r → Fin n) (z : Fin n → ℤ_[p]) :
    (Fin r → ℤ_[p]) × (Complement cols → ℤ_[p]) :=
  (integralSelectedGradient p F rows z, fun j => z j)

/-- Both components of the integral coordinate map match the actual
selected-gradient coordinate map over the p-adic field. -/
theorem coe_integralGradientCoordinates {n r : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (rows cols : Fin r → Fin n) (z : Fin n → ℤ_[p]) :
    ((fun a => ((integralGradientCoordinates p F rows cols z).1 a : ℚ_[p])),
     (fun j => ((integralGradientCoordinates p F rows cols z).2 j : ℚ_[p]))) =
      selectedGradientCoordinates (map (Int.castRingHom ℚ_[p]) F) rows cols
        (fun j => (z j : ℚ_[p])) := by
  ext a
  · exact coe_integralSelectedGradient p F rows z a
  · rfl

/-- Coercion preserves the exact maximum norm, including an empty index type. -/
theorem norm_coe_pi {ι : Type*} [Fintype ι] (z : ι → ℤ_[p]) :
    ‖fun i => (z i : ℚ_[p])‖ = ‖z‖ := rfl

/-- The field-valued output difference has exactly the norm of the
integral gradient difference and the complementary coordinate difference. -/
theorem norm_selectedGradient_sub_eq {n r : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (rows cols : Fin r → Fin n) (z w : Fin n → ℤ_[p]) :
    ‖selectedGradientCoordinates (map (Int.castRingHom ℚ_[p]) F) rows cols
        (fun j => (z j : ℚ_[p])) -
      selectedGradientCoordinates (map (Int.castRingHom ℚ_[p]) F) rows cols
        (fun j => (w j : ℚ_[p]))‖ =
      ‖(integralSelectedGradient p F rows z - integralSelectedGradient p F rows w,
        fun j : Complement cols => z j - w j)‖ := by
  rw [← coe_integralGradientCoordinates, ← coe_integralGradientCoordinates]
  rfl

/-- Coercion of the literal integral coset point is the exact field-valued
perturbation used by the open-neighborhood theorem. -/
theorem coe_coset {n : ℕ} (ξ z : Fin n → ℤ_[p]) (M : ℕ) :
    (fun j => ((ξ + (p : ℤ_[p]) ^ M • z) j : ℚ_[p])) =
      (fun j => (ξ j : ℚ_[p])) + (p : ℚ_[p]) ^ M • (fun j => (z j : ℚ_[p])) := by
  funext j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, PadicInt.coe_add,
    PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast]

/-- A supplied integral center with a nonzero actual Hessian minor yields
an open integral patch and a literal congruence coset on which the integral
selected gradient plus untouched coordinates has a uniform inverse norm
bound. The constant and the coset exponent are chosen before the points. -/
theorem exists_integral_gradient_coset_patch {n r : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (rows cols : Fin r → Fin n)
    (ξ : Fin n → ℤ_[p])
    (hdet : ((hessian (map (Int.castRingHom ℚ_[p]) F)
      (fun j => (ξ j : ℚ_[p]))).submatrix rows cols).det ≠ 0) :
    ∃ (U : Set (Fin n → ℤ_[p])) (C : ℝ≥0) (M : ℕ),
      ξ ∈ U ∧ IsOpen U ∧ 1 ≤ M ∧
      (∀ t : Fin n → ℤ_[p], ξ + (p : ℤ_[p]) ^ M • t ∈ U) ∧
      ∀ z ∈ U, ∀ w ∈ U,
        ‖z - w‖ ≤ (C : ℝ) *
          ‖(integralSelectedGradient p F rows z - integralSelectedGradient p F rows w,
            fun j : Complement cols => z j - w j)‖ := by
  obtain ⟨V, C, hξ, hV, hA⟩ := exists_selectedGradient_antilipschitz
    (map (Int.castRingHom ℚ_[p]) F) rows cols (fun j => (ξ j : ℚ_[p])) hdet
  let U : Set (Fin n → ℤ_[p]) := (fun z => fun j => (z j : ℚ_[p])) ⁻¹' V
  have hU : IsOpen U := hV.preimage (continuous_pi
    (fun j => continuous_subtype_val.comp (continuous_apply j)))
  obtain ⟨M, hM, hcoset⟩ := PadicCongruenceNeighborhood.exists_power_coset_subset
    p (fun j => (ξ j : ℚ_[p])) V hV hξ
  refine ⟨U, C, M, hξ, hU, hM, ?_, ?_⟩
  · intro t
    change (fun j => ((ξ + (p : ℤ_[p]) ^ M • t) j : ℚ_[p])) ∈ V
    rw [coe_coset]
    exact hcoset t
  · intro z hz w hw
    have hbound := hA.le_mul_dist
      (⟨fun j => (z j : ℚ_[p]), hz⟩ : V)
      (⟨fun j => (w j : ℚ_[p]), hw⟩ : V)
    change dist (fun j => (z j : ℚ_[p])) (fun j => (w j : ℚ_[p])) ≤
      (C : ℝ) * dist
        (selectedGradientCoordinates (map (Int.castRingHom ℚ_[p]) F) rows cols
          (fun j => (z j : ℚ_[p])))
        (selectedGradientCoordinates (map (Int.castRingHom ℚ_[p]) F) rows cols
          (fun j => (w j : ℚ_[p]))) at hbound
    rw [dist_eq_norm, dist_eq_norm, norm_selectedGradient_sub_eq] at hbound
    exact hbound

end CubicTenVariables.IntegralGradientPatch
