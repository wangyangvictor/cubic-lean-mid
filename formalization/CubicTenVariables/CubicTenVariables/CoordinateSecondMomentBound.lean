import CubicTenVariables.CoordinateSecondMoment
import CubicTenVariables.SecondMomentDeviation

/-! Exact second-moment assembly from a nonzero exceptional polynomial
and bounds for the actual binary slice counts. The geometric construction
of that polynomial and the good-fiber Weil estimate remain separate. -/

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace CubicTenVariables.CoordinateSecondMomentBound
open MvPolynomial BinarySliceCounting CoordinateSecondMoment ProjectiveFourierIdentity
open scoped BigOperators Classical
variable {K : Type*} [Field K] [Fintype K] {n : ℕ}

theorem coordinate_bound (hn : 3 ≤ n) (ψ : AddChar K ℂ) (hψ : ψ ≠ 1)
    (F : MvPolynomial (Fin n) K) (e : Fin 2 ↪ Fin n)
    (G : MvPolynomial (Complement e) K) (hG : G ≠ 0) (B : ℝ) (hB : 0 ≤ B)
    (htriv : ∀ w, (sliceCount F e w : ℝ) ≤ 3*(Fintype.card K : ℝ))
    (hgood : ∀ w, eval w G ≠ 0 →
      ((sliceCount F e w : ℝ)-(Fintype.card K : ℝ))^2 ≤ B*(Fintype.card K : ℝ)) :
    ∑ v : Complement e → K, ‖normalizedFourierSum ψ F (combine e 0 v)‖^2 ≤
      (B+4*(G.totalDegree : ℝ))*(Fintype.card K : ℝ)^(2*n-3) := by
  have hm : 1 ≤ Fintype.card (Complement e) := by rw [card_complement]; omega
  have h := SecondMomentDeviation.sum_sq_le_of_polynomial hm G hG
    (sliceCount F e) B hB htriv hgood
  rw [card_complement] at h
  rw [coordinate_second_moment ψ hψ F e]
  calc
    _ ≤ (Fintype.card K : ℝ)^(n-2) *
        ((B+4*(G.totalDegree : ℝ))*(Fintype.card K : ℝ)^((n-2)+1)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = (B+4*(G.totalDegree : ℝ))*
        ((Fintype.card K : ℝ)^(n-2)*(Fintype.card K : ℝ)^((n-2)+1)) := by ring
    _ = _ := by
      have he : (n-2)+((n-2)+1) = 2*n-3 := by omega
      rw [← pow_add, he]

/-- The same bound, with the left side literally summed over all ambient
frequencies satisfying the two coordinate equations, including zero. -/
theorem coordinate_plane_bound (hn : 3 ≤ n) (ψ : AddChar K ℂ) (hψ : ψ ≠ 1)
    (F : MvPolynomial (Fin n) K) (e : Fin 2 ↪ Fin n)
    (G : MvPolynomial (Complement e) K) (hG : G ≠ 0) (B : ℝ) (hB : 0 ≤ B)
    (htriv : ∀ w, (sliceCount F e w : ℝ) ≤ 3*(Fintype.card K : ℝ))
    (hgood : ∀ w, eval w G ≠ 0 →
      ((sliceCount F e w : ℝ)-(Fintype.card K : ℝ))^2 ≤ B*(Fintype.card K : ℝ)) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin n → K => ∀ j : Fin 2, v (e j) = 0),
      ‖normalizedFourierSum ψ F v‖^2 ≤
        (B+4*(G.totalDegree : ℝ))*(Fintype.card K : ℝ)^(2*n-3) := by
  rw [coordinate_plane_second_moment ψ hψ F e,
    ← coordinate_second_moment ψ hψ F e]
  exact coordinate_bound hn ψ hψ F e G hG B hB htriv hgood

end CubicTenVariables.CoordinateSecondMomentBound
