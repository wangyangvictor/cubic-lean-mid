import CubicTenVariables.TerminalProfileProduct
import CubicTenVariables.SmithGlobalExponents

/-! Global weighted Smith assembly with literal complete cubic sums. -/

noncomputable section
namespace CubicTenVariables.GlobalSmithBound
open MvPolynomial HessianTheorem11 SmithProfileNumerics
open scoped BigOperators

/-- The global assembly consumes proved local masses; it introduces no analytic input. -/
theorem weighted_completeCubicSum_le {ι : Type*} [Fintype ι]
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hp : Function.Injective p)
    (a t : ι → ℕ) (hcase : ∀ i, t i ≤ a i ∨ p i ≠ 2)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hmass : ∀ i, SmithProfileMassBound.profileMass F (p i) (a i) (t i) ≤
      (p i : ℝ)^(((10*t i : ℕ) : ℝ)+(phi (a i) (t i) : ℝ)+ε*(a i : ℝ)))
    (V : Finset (Fin 10 → ℤ)) (w : (Fin 10 → ℤ) → ℝ)
    (hw : ∀ v ∈ V, 0 ≤ w v) :
    (∑ v ∈ V, w v * ‖completeCubicSum F ((∏ i, p i^a i)^2*(∏ i, p i^t i)) v‖) ≤
      (((∏ i, p i^a i)^2*(∏ i, p i^t i) : ℕ) : ℝ)^ε *
        WeightedResidueMaximum.maximum (∏ i, p i^a i) V w *
          ∏ i, (p i : ℝ)^(localD (a i) (t i) : ℝ) := by
  classical
  let A := ∏ i, p i^a i
  let T := ∏ i, p i^t i
  let E := WeightedResidueMaximum.maximum A V w
  let B := ∏ i, (p i : ℝ)^(((10*t i : ℕ) : ℝ)+(phi (a i) (t i) : ℝ)+ε*(a i : ℝ))
  let D := ∏ i, (p i : ℝ)^(localD (a i) (t i) : ℝ)
  have hp0 (i : ι) : 0 < p i := (Fact.out : (p i).Prime).pos
  have hA : 0 < A := Finset.prod_pos (fun i _ => pow_pos (hp0 i) _)
  have hT : 0 < T := Finset.prod_pos (fun i _ => pow_pos (hp0 i) _)
  have hE : 0 ≤ E := WeightedResidueMaximum.maximum_nonneg A V w hw
  have hB : 0 ≤ B := Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hD : 0 ≤ D := Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hmass0 (i : ι) : 0 ≤ SmithProfileMassBound.profileMass F (p i) (a i) (t i) := by
    unfold SmithProfileMassBound.profileMass
    apply Finset.sum_nonneg
    intro y _
    split_ifs <;> positivity
  have htotal : FlexibleLifting.zeroFiberTerminalTotal F A T ≤ B :=
    (TerminalProfileProduct.zeroFiberTerminalTotal_le_prod_profileMass F hF p hp a t hcase).trans
      (Finset.prod_le_prod (fun i _ => hmass0 i) (fun i _ => hmass i))
  have htotient : (Nat.totient (A^2*T) : ℝ) ≤ ((A^2*T : ℕ) : ℝ) := by
    exact_mod_cast Nat.totient_le (A^2*T)
  have halgebra : (A : ℝ)^10*((A^2*T : ℕ) : ℝ)*B = (A : ℝ)^ε*D :=
    SmithGlobalExponents.combined_localD p a t hp0 ε
  change _ ≤ ((A^2*T : ℕ) : ℝ)^ε*E*D
  calc
    _ ≤ (A : ℝ)^10*(Nat.totient (A^2*T) : ℝ)*E*
        FlexibleLifting.zeroFiberTerminalTotal F A T :=
      FlexibleLifting.weighted_completeCubicSum_le F hF A T V w hw
    _ ≤ (A : ℝ)^10*(Nat.totient (A^2*T) : ℝ)*E*B :=
      mul_le_mul_of_nonneg_left htotal (mul_nonneg (by positivity) hE)
    _ ≤ (A : ℝ)^10*((A^2*T : ℕ) : ℝ)*E*B :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htotient (by positivity)) hE) hB
    _ = (A : ℝ)^ε*E*D := by
      calc
        _ = ((A : ℝ)^10*((A^2*T : ℕ) : ℝ)*B)*E := by ring
        _ = _ := by rw [halgebra]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (SmithGlobalExponents.parameter_rpow_le A T hA hT ε hε) hE) hD

end CubicTenVariables.GlobalSmithBound
