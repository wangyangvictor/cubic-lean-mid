import CubicTenVariables.FiniteFieldPolynomialZeros
import CubicTenVariables.Literature.FiniteFieldPointCounts
import Mathlib.Data.Fintype.BigOperators

/-! Exact projection counts for an equation linear in one coordinate.
For a cubic projected from a rational double point, the equation has the
form t Q(x) + C(x). The count below keeps both exceptional loci explicitly;
no bound for their intersection and no existence of a double point is assumed
as an unproved theorem. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.SingularCubicFiberCount
open MvPolynomial
open scoped BigOperators Classical

variable {K α : Type*} [Field K] [Fintype K] [Fintype α]

theorem card_linear_fiber (a b : K) :
    Nat.card {t : K // t*a+b=0} =
      if a=0 then (if b=0 then Fintype.card K else 0) else 1 := by
  classical
  by_cases ha : a=0
  · by_cases hb : b=0 <;> simp [ha,hb,Nat.card_eq_fintype_card]
  · have he (t : K) : t*a+b=0 ↔ t=(-b)/a := by
      constructor
      · intro h
        apply (eq_div_iff ha).mpr
        linear_combination h
      · intro h
        rw [h]
        field_simp
        ring
    simp only [ha,if_false]
    rw [Nat.card_congr (Equiv.subtypeEquivRight he),Nat.card_eq_fintype_card,
      Fintype.card_subtype_eq]

theorem card_linear_fibers (Q C : α → K) :
    Nat.card {z : α × K // z.2*Q z.1+C z.1=0} =
      ∑ x : α, Nat.card {t : K // t*Q x+C x=0} := by
  classical
  let e : {z : α × K // z.2*Q z.1+C z.1=0} ≃
      (Σ x : α, {t : K // t*Q x+C x=0}) :=
    { toFun := fun z => ⟨z.1.1,⟨z.1.2,z.2⟩⟩
      invFun := fun z => ⟨(z.1,z.2.1),z.2.2⟩
      left_inv := fun z => by cases z; rfl
      right_inv := fun z => by cases z; rfl }
  simpa only [Nat.card_sigma] using Nat.card_congr e

/-- Exact count, without truncated natural subtraction. Each point outside
Q=0 has one lift; each point on Q=C=0 has every possible lift. -/
theorem card_linear_incidence (Q C : α → K) :
    Nat.card {z : α × K // z.2*Q z.1+C z.1=0} +
      Nat.card {x : α // Q x=0} =
    Fintype.card α + Fintype.card K * Nat.card {x : α // Q x=0 ∧ C x=0} := by
  classical
  rw [card_linear_fibers]
  simp_rw [card_linear_fiber]
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype,Finset.card_eq_sum_ones,
    Finset.sum_filter]
  rw [← Finset.sum_add_distrib,Finset.mul_sum,
    Fintype.card_eq_sum_ones (α := α),← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hq : Q x=0 <;> by_cases hc : C x=0 <;> simp [hq,hc,add_comm]

/-- The signed error is exactly the difference of the two exceptional
point counts, in the ordinary real-number normalization. -/
theorem linear_incidence_error (Q C : α → K) :
    (Nat.card {z : α × K // z.2*Q z.1+C z.1=0} : ℝ) - Fintype.card α =
      (Fintype.card K : ℝ)*Nat.card {x : α // Q x=0 ∧ C x=0} -
        Nat.card {x : α // Q x=0} := by
  have h := card_linear_incidence Q C
  have h' : (Nat.card {z : α × K // z.2*Q z.1+C z.1=0} : ℝ) +
      Nat.card {x : α // Q x=0} =
      Fintype.card α + (Fintype.card K : ℝ)*Nat.card {x : α // Q x=0 ∧ C x=0} := by
    exact_mod_cast h
  linarith

theorem abs_linear_incidence_error_le (Q C : α → K) :
    |(Nat.card {z : α × K // z.2*Q z.1+C z.1=0} : ℝ) - Fintype.card α| ≤
      (Fintype.card K : ℝ)*Nat.card {x : α // Q x=0 ∧ C x=0} +
        Nat.card {x : α // Q x=0} := by
  rw [linear_incidence_error]
  exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)])

/-- Transport to the literal affine zero count along any displayed
coordinate bijection. The equation is an equality of actual evaluations. -/
theorem affineZeroCount_of_coordinates {n m : ℕ}
    (F : MvPolynomial (Fin n) K) (Q C : MvPolynomial (Fin m) K)
    (e : (Fin n → K) ≃ ((Fin m → K) × K))
    (he : ∀ x, eval x F = (e x).2*eval (e x).1 Q + eval (e x).1 C) :
    Literature.affineZeroCount F + Nat.card {x : Fin m → K // eval x Q=0} =
      Fintype.card K ^ m + Fintype.card K *
        Nat.card {x : Fin m → K // eval x Q=0 ∧ eval x C=0} := by
  have hcard : Literature.affineZeroCount F =
      Nat.card {z : (Fin m → K) × K // z.2*eval z.1 Q + eval z.1 C=0} := by
    exact Nat.card_congr (e.subtypeEquiv (fun x => by rw [he x]))
  rw [hcard]
  simpa only [Fintype.card_fun,Fintype.card_fin] using
    card_linear_incidence (fun x => eval x Q) (fun x => eval x C)

/-- A nonzero quadratic coefficient contributes at most 2 q^(m-1).
The sole remaining bound is the actual common-zero count of Q and C. -/
theorem abs_projection_error_le {n m : ℕ} (hm : 2 ≤ m)
    (F : MvPolynomial (Fin n) K) (Q C : MvPolynomial (Fin m) K)
    (hQ : Q ≠ 0) (hdeg : Q.totalDegree ≤ 2)
    (e : (Fin n → K) ≃ ((Fin m → K) × K))
    (he : ∀ x, eval x F = (e x).2*eval (e x).1 Q + eval (e x).1 C)
    (A : ℝ) (hI : (Nat.card {x : Fin m → K // eval x Q=0 ∧ eval x C=0} : ℝ) ≤
      A*(Fintype.card K : ℝ)^(m-2)) :
    |(Literature.affineZeroCount F : ℝ) - (Fintype.card K : ℝ)^m| ≤
      (A+2)*(Fintype.card K : ℝ)^(m-1) := by
  have h := affineZeroCount_of_coordinates F Q C e he
  have hreal : (Literature.affineZeroCount F : ℝ) +
      Nat.card {x : Fin m → K // eval x Q=0} =
      (Fintype.card K : ℝ)^m + (Fintype.card K : ℝ) *
        Nat.card {x : Fin m → K // eval x Q=0 ∧ eval x C=0} := by
    exact_mod_cast h
  have hquad : (Nat.card {x : Fin m → K // eval x Q=0} : ℝ) ≤
      2*(Fintype.card K : ℝ)^(m-1) := by
    have hh := FiniteFieldPolynomialZeros.card_zeros_le_degree_mul Q hQ 2 hdeg
    rw [← FiniteFieldPolynomialZeros.natCard_zeros] at hh
    simpa only [Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow] using
      (show (Nat.card {x : Fin m → K // eval x Q=0} : ℝ) ≤
        (2 * Fintype.card K^(Fintype.card (Fin m)-1) : ℕ) by exact_mod_cast hh)
  have herr : (Literature.affineZeroCount F : ℝ) - (Fintype.card K : ℝ)^m =
      (Fintype.card K : ℝ)*Nat.card {x : Fin m → K // eval x Q=0 ∧ eval x C=0} -
        Nat.card {x : Fin m → K // eval x Q=0} := by linarith
  rw [herr]
  calc
    _ ≤ (Fintype.card K : ℝ)*Nat.card {x : Fin m → K // eval x Q=0 ∧ eval x C=0} +
        Nat.card {x : Fin m → K // eval x Q=0} :=
      (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)])
    _ ≤ (Fintype.card K : ℝ)*(A*(Fintype.card K : ℝ)^(m-2)) +
        2*(Fintype.card K : ℝ)^(m-1) :=
      add_le_add (mul_le_mul_of_nonneg_left hI (by positivity)) hquad
    _ = _ := by
      have hpow : (Fintype.card K : ℝ)*(Fintype.card K : ℝ)^(m-2) =
          (Fintype.card K : ℝ)^(m-1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [mul_left_comm _ A,hpow]
      ring

end CubicTenVariables.SingularCubicFiberCount
