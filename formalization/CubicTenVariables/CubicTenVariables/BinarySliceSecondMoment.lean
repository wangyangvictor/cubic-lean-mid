import CubicTenVariables.BinarySliceGeometry
import CubicTenVariables.CoordinateSecondMomentBound
import CubicTenVariables.Literature.AffinePlaneCurveWeil

/-! Applying the generic curve estimate to the actual binary fibers.
No slice-count estimate is retained as an assumption: the remaining
application hypothesis is geometric integrality away from a supplied
nonzero exceptional polynomial. -/

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace CubicTenVariables.BinarySliceSecondMoment
open MvPolynomial BinarySliceCounting BinarySliceGeometry CoordinateSecondMoment
open FiniteFieldPolynomialZeros ProjectiveFourierIdentity
open scoped BigOperators Classical

theorem sliceCount_eq_zeros {K : Type*} [Field K] [Fintype K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (e : Fin 2 ↪ Fin n) (w : Complement e → K) :
    sliceCount F e w = (zeros (slice e F w)).card := by
  unfold sliceCount zeros
  apply congrArg Finset.card
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, eval_slice]

theorem sliceCount_eq_natCard {K : Type*} [Field K] [Fintype K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (e : Fin 2 ↪ Fin n) (w : Complement e → K) :
    sliceCount F e w = Nat.card {z : Fin 2 → K // eval z (slice e F w) = 0} := by
  rw [natCard_zeros, sliceCount_eq_zeros]

theorem sliceCount_le_three_mul {K : Type*} [Field K] [Fintype K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (hF : F.totalDegree ≤ 3)
    (e : Fin 2 ↪ Fin n) (w : Complement e → K) (hw : slice e F w ≠ 0) :
    sliceCount F e w ≤ 3*Fintype.card K := by
  rw [sliceCount_eq_zeros]
  simpa only [Fintype.card_fin, Nat.reduceSub, pow_one] using
    card_zeros_le_degree_mul (slice e F w) hw 3 ((totalDegree_slice_le e F w).trans hF)

/-- One Weil constant works before all finite fields, cubics and chosen
coordinate pairs. The exceptional polynomial and its geometric-integrality
property remain explicit; they are not literature assumptions here. -/
theorem exists_coordinate_bound (weil : Literature.AffinePlaneCubicWeil) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (K : Type) [Field K] [Fintype K]
      (_ : (2 : K) ≠ 0) (_ : (3 : K) ≠ 0)
      (n : ℕ), 3 ≤ n → ∀ (F : MvPolynomial (Fin n) K), F.totalDegree ≤ 3 →
      ∀ (e : Fin 2 ↪ Fin n) (G : MvPolynomial (Complement e) K), G ≠ 0 →
      (∀ w : Complement e → K, (slice e F w).totalDegree = 3) →
      (∀ w : Complement e → K, eval w G ≠ 0 →
        IsDomain (MvPolynomial (Fin 2) (AlgebraicClosure K) ⧸ Ideal.span
          {map (algebraMap K (AlgebraicClosure K)) (slice e F w)})) →
      ∀ (ψ : AddChar K ℂ), ψ ≠ 1 →
        ∑ v ∈ Finset.univ.filter (fun v : Fin n → K => ∀ j : Fin 2, v (e j) = 0),
          ‖normalizedFourierSum ψ F v‖^2 ≤
            (B+4*(G.totalDegree : ℝ))*(Fintype.card K : ℝ)^(2*n-3) := by
  obtain ⟨B,hB,hweil⟩ := weil
  refine ⟨B,hB,?_⟩
  intro K _ _ h2 h3 n hn F hF e G hG hdegree hgeo ψ hψ
  apply CoordinateSecondMomentBound.coordinate_plane_bound hn ψ hψ F e G hG B
    (zero_le_one.trans hB)
  · intro w
    have hw : slice e F w ≠ 0 := by
      intro hz
      have h := hdegree w
      rw [hz, totalDegree_zero] at h
      omega
    exact_mod_cast sliceCount_le_three_mul F hF e w hw
  · intro w hw
    rw [sliceCount_eq_natCard]
    exact hweil K (slice e F w) h2 h3 (hdegree w) (hgeo w hw)

end CubicTenVariables.BinarySliceSecondMoment
