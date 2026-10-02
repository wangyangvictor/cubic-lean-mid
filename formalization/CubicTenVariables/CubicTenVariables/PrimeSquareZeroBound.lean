import CubicTenVariables.PrimeSquareStationaryBound
import CubicTenVariables.CubicFiniteFieldMass

/-! All-prime prime-square bounds when the frequency reduces to zero.
The exact stationary support is contained in a scalar times the actual
singular residue set. The already proved uniform gradient-zero count
supplies the exponent seventeen in ten variables, including bad primes. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CubicTenVariables.PrimeSquareZeroBound
open MvPolynomial PrimeSquareStationaryBound
attribute [local instance] Classical.propDecidable

/-- A stationary pair at a zero reduced frequency has zero gradient;
forgetting its hypersurface equation and scalar unit condition gives this
literal finite upper bound. -/
theorem card_stationaryPairs_le_gradient_count {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (p : ℕ) [Fact p.Prime] (v : Fin n → ℤ)
    (hv : (fun i => (v i : ZMod p)) = 0) :
    (stationaryPairs F (ZMod p) (fun i => (v i : ZMod p))).card ≤
      p * Nat.card {x : Fin n → ZMod p //
        HessianTheorem11.gradient (map (Int.castRingHom (ZMod p)) F) x = 0} := by
  classical
  let Z : Finset (Fin n → ZMod p) := Finset.univ.filter fun x =>
    HessianTheorem11.gradient (map (Int.castRingHom (ZMod p)) F) x = 0
  have hsub : stationaryPairs F (ZMod p) (fun i => (v i : ZMod p)) ⊆
      (Finset.univ : Finset (ZMod p)).product Z := by
    intro z hz
    rcases (mem_stationaryPairs F (ZMod p) _ z).mp hz with ⟨hb,_,he⟩
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    funext i
    have hvi := congrFun hv i
    simp only [Pi.zero_apply] at hvi ⊢
    have hi := he i
    rw [hvi, neg_zero] at hi
    have hi0 := (mul_eq_zero.mp hi).resolve_left hb
    simpa only [HessianTheorem11.gradient, pderiv_map, ← eval₂_eq_eval_map] using hi0
  have hc : Z.card = Nat.card {x : Fin n → ZMod p //
      HessianTheorem11.gradient (map (Int.castRingHom (ZMod p)) F) x = 0} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc
    _ ≤ ((Finset.univ : Finset (ZMod p)).product Z).card := Finset.card_le_card hsub
    _ = (Finset.univ : Finset (ZMod p)).card * Z.card := Finset.card_product _ _
    _ = _ := by rw [Finset.card_univ, ZMod.card, hc]

/-- One constant precedes the prime and integer frequency; no exceptional
prime is discarded. -/
theorem exists_bound (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : HessianTheorem11.Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : ℕ) [Fact p.Prime] (v : Fin 10 → ℤ),
      (fun i => (v i : ZMod p)) = 0 →
      ‖completeCubicSum F (p^2) v‖ ≤ C * (p : ℝ)^17 := by
  obtain ⟨C,hC,hbound⟩ := CubicFiniteFieldMass.exists_uniform_gradient_zero_bound F hF hA
  refine ⟨(C : ℝ),by exact_mod_cast hC,?_⟩
  intro p hp v hv
  have hc := (card_stationaryPairs_le_gradient_count F p v hv).trans
    (Nat.mul_le_mul_left p (hbound p hp.out))
  have hcr : ((stationaryPairs F (ZMod p) (fun i => (v i : ZMod p))).card : ℝ) ≤
      (p : ℝ) * ((C : ℝ)*(p : ℝ)^5) := by exact_mod_cast hc
  calc
    ‖completeCubicSum F (p^2) v‖ ≤ (p : ℝ)^11 *
        ((stationaryPairs F (ZMod p) (fun i => (v i : ZMod p))).card : ℝ) :=
      norm_completeCubicSum_le_stationaryPairs F hF p v
    _ ≤ (p : ℝ)^11 * ((p : ℝ)*((C : ℝ)*(p : ℝ)^5)) :=
      mul_le_mul_of_nonneg_left hcr (by positivity)
    _ = (C : ℝ)*(p : ℝ)^17 := by ring

/-- In particular this applies to the literal zero integer frequency. -/
theorem exists_zero_frequency_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3)
    (hA : HessianTheorem11.Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : ℕ) [Fact p.Prime],
      ‖completeCubicSum F (p^2) 0‖ ≤ C * (p : ℝ)^17 := by
  obtain ⟨C,hC,hbound⟩ := exists_bound F hF hA
  refine ⟨C,hC,?_⟩
  intro p hp
  exact hbound p 0 (by funext i; exact Int.cast_zero)

end CubicTenVariables.PrimeSquareZeroBound
