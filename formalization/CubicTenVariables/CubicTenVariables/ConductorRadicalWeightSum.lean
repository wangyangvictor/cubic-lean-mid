import CubicTenVariables.PrimeConstantEpsilonBound
import CubicTenVariables.PositiveReciprocalSum
import CubicTenVariables.GcdReciprocalSquareSum

/-! Summation of the actual prime-factor constants left by the two local
residue bounds. The squarefree/coprime restrictions may be dropped: a
convergent square-reciprocal sum and a small-power harmonic bound suffice. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ConductorRadicalWeightSum
open scoped BigOperators

/-- One constant precedes the radical cutoff and every finite positive
pair family. The estimate does not assume squarefreeness or coprimality. -/
theorem exists_bound (C : ℝ) (hC : 1 ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ T : ℝ, 1 ≤ T → ∀ Q : Finset (ℕ × ℕ),
      (∀ x ∈ Q, 1 ≤ x.1 ∧ 1 ≤ x.2 ∧ ((x.1*x.2 : ℕ) : ℝ) ≤ T) →
      (∑ x ∈ Q, C^(x.1.primeFactors.card+x.2.primeFactors.card) /
        ((x.1 : ℝ)^2*(x.2 : ℝ))) ≤ M*T^ε := by
  classical
  obtain ⟨A,hA,hcoeff⟩ := PrimeConstantEpsilonBound.exists_two_factor_bound C hC
    (ε/2) (by linarith)
  obtain ⟨B,hB,harmonic⟩ := PositiveReciprocalSum.exists_uniform_inverse_bound
    (ε/2) (by linarith)
  obtain ⟨R,hR,hsquares⟩ := GcdReciprocalSquareSum.exists_bound
  refine ⟨A*R*B,?_,?_⟩
  · have hAR : 1 ≤ A*R := by nlinarith
    nlinarith
  intro T hT Q hQ
  let U := Q.image Prod.fst
  let V := Q.image Prod.snd
  have hU (a : ℕ) (ha : a ∈ U) : 1 ≤ a := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
    exact (hQ x hx).1
  have hV (b : ℕ) (hb : b ∈ V) : 1 ≤ b ∧ (b : ℝ) ≤ T := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hb
    have hxQ := hQ x hx
    refine ⟨hxQ.2.1,?_⟩
    have ha : (1 : ℝ) ≤ x.1 := by exact_mod_cast hxQ.1
    have hb : (0 : ℝ) ≤ x.2 := Nat.cast_nonneg _
    have hm := mul_le_mul_of_nonneg_right ha hb
    rw [one_mul] at hm
    exact hm.trans (by simpa only [Nat.cast_mul] using hxQ.2.2)
  have hsub : Q ⊆ U ×ˢ V := by
    intro x hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx,Finset.mem_image_of_mem _ hx⟩
  have hsumU : (∑ a ∈ U, 1/(a : ℝ)^2) ≤ R := by
    simpa only [Nat.gcd_one_right,Nat.cast_one,one_pow,Nat.divisors_one,
      Finset.card_singleton,mul_one] using hsquares 1 (by norm_num) U hU
  have hsumV : (∑ b ∈ V, (b : ℝ)⁻¹) ≤ B*T^(ε/2) :=
    harmonic T hT V (fun b hb => by have hp := (hV b hb).1; omega)
      (fun b hb => (hV b hb).2)
  have hsum : (∑ x ∈ Q, (1/(x.1 : ℝ)^2)*(x.2 : ℝ)⁻¹) ≤ R*(B*T^(ε/2)) := by
    calc
      _ ≤ ∑ x ∈ U ×ˢ V, (1/(x.1 : ℝ)^2)*(x.2 : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => by positivity)
      _ = (∑ a ∈ U, 1/(a : ℝ)^2)*(∑ b ∈ V, (b : ℝ)⁻¹) := by
        rw [Finset.sum_product,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
      _ ≤ R*(B*T^(ε/2)) := mul_le_mul hsumU hsumV
        (Finset.sum_nonneg fun b _ => by positivity) (by linarith)
  have hpoint (x : ℕ × ℕ) (hx : x ∈ Q) :
      C^(x.1.primeFactors.card+x.2.primeFactors.card) / ((x.1 : ℝ)^2*(x.2 : ℝ)) ≤
        (A*T^(ε/2))*((1/(x.1 : ℝ)^2)*(x.2 : ℝ)⁻¹) := by
    have hc := (hcoeff x.1 x.2 (hQ x hx).1 (hQ x hx).2.1).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hQ x hx).2.2 (by linarith)) (by linarith))
    calc
      _ ≤ (A*T^(ε/2))/((x.1 : ℝ)^2*(x.2 : ℝ)) :=
        div_le_div_of_nonneg_right hc (by positivity)
      _ = _ := by simp only [div_eq_mul_inv,mul_inv_rev,one_mul]; ring
  have hpow : T^(ε/2)*T^(ε/2) = T^ε := by
    rw [← Real.rpow_add (by linarith : 0 < T)]
    congr 1
    ring
  calc
    _ ≤ ∑ x ∈ Q, (A*T^(ε/2))*((1/(x.1 : ℝ)^2)*(x.2 : ℝ)⁻¹) :=
      Finset.sum_le_sum hpoint
    _ = (A*T^(ε/2))*(∑ x ∈ Q, (1/(x.1 : ℝ)^2)*(x.2 : ℝ)⁻¹) :=
      by rw [Finset.mul_sum]
    _ ≤ (A*T^(ε/2))*(R*(B*T^(ε/2))) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (A*R*B)*(T^(ε/2)*T^(ε/2)) := by ring
    _ = (A*R*B)*T^ε := by rw [hpow]

end CubicTenVariables.ConductorRadicalWeightSum
