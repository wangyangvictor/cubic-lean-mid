import TranslatedDepthSeven.BoundedEvaluationRelation
import TranslatedDepthSeven.StarEquationBounds
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex

/-!
# A bounded equation through all bounded points of a hypersurface

The input homogeneous equation may have arbitrarily large coefficients.
Its nonzero coefficient vector is a relation between the monomial
evaluation vectors. Cramer's rule supplies another nonzero relation of
the same degree whose coefficients are bounded solely by the point box,
the number of variables and the degree.

For an integral hypersurface, the resulting form is either a proper
auxiliary cut or a scalar multiple of its defining equation. This is the
elementary height alternative used in Salberger 2007, Lemma 6.3, here
with an explicit dimension-uniform bound.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial
open scoped BigOperators

/-- Two nonzero forms of the same degree can be divisible only by a scalar. -/
theorem eq_scalar_mul_of_homogeneous_dvd_same_degree
    {N e : ℕ} {F G : MvPolynomial (Fin N) ℚ}
    (hF : F ≠ 0) (hG : G ≠ 0)
    (hFhom : F.IsHomogeneous e) (hGhom : G.IsHomogeneous e)
    (hdiv : G ∣ F) :
    ∃ c : ℚ, c ≠ 0 ∧ F = MvPolynomial.C c * G := by
  obtain ⟨Q, hQ⟩ := hdiv
  have hQne : Q ≠ 0 := by
    intro hz
    apply hF
    simp [hQ, hz]
  have hdegree : Q.totalDegree = 0 := by
    have hd := MvPolynomial.totalDegree_mul_of_isDomain hG hQne
    rw [← hQ, hFhom.totalDegree hF, hGhom.totalDegree hG] at hd
    omega
  have hconstant := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdegree
  refine ⟨Q.coeff 0, ?_, ?_⟩
  · intro hz
    apply hQne
    exact hconstant.trans (by rw [hz]; simp)
  · exact hQ.trans ((congrArg (G * ·) hconstant).trans (mul_comm _ _))

theorem exists_bounded_homogeneous_equation_on_bounded_zeros
    {N e R : ℕ} (G : MvPolynomial (Fin N) ℤ)
    (hG : G ≠ 0) (hhom : G.IsHomogeneous e)
    (Z : Finset (IntVector N))
    (hzero : ∀ z ∈ Z, MvPolynomial.eval z G = 0)
    (hcoord : ∀ z ∈ Z, ∀ i, (z i).natAbs ≤ R) :
    ∃ F : MvPolynomial (Fin N) ℤ,
      F ≠ 0 ∧ F.IsHomogeneous e ∧
      (∀ z ∈ Z, MvPolynomial.eval z F = 0) ∧
      ∀ m, (F.coeff m).natAbs ≤
        (e + 1) ^ N * ((e + 1) ^ N).factorial *
          max 1 R ^ (e * (e + 1) ^ N) := by
  classical
  let s := G.support.card
  let E : Fin s ≃ G.support := G.support.equivFin.symm
  let exponent : Fin s → (Fin N →₀ ℕ) := fun i ↦ (E i).1
  let mon : Fin s → MvPolynomial (Fin N) ℤ :=
    fun i ↦ MvPolynomial.monomial (exponent i) 1
  let g : Fin s → ℚ := fun i ↦ ((G.coeff (exponent i) : ℤ) : ℚ)
  have hexponent : Function.Injective exponent :=
    Subtype.val_injective.comp E.injective
  have hmon : LinearIndependent ℚ
      (fun i ↦ (mon i).map (Int.castRingHom ℚ)) := by
    simpa [mon, MvPolynomial.coe_basisMonomials] using
      (MvPolynomial.basisMonomials (Fin N) ℚ).linearIndependent.comp exponent hexponent
  have hmonhom : ∀ i, (mon i).IsHomogeneous e := by
    intro i
    apply MvPolynomial.isHomogeneous_monomial
    rw [Finsupp.degree_eq_weight_one]
    exact hhom (MvPolynomial.mem_support_iff.mp (E i).2)
  have hmoncoeff : ∀ i m, ((mon i).coeff m).natAbs ≤ 1 := by
    intro i m
    simp only [mon, MvPolynomial.coeff_monomial]
    split_ifs <;> simp
  have hmonsupport : ∀ i, (mon i).support.card ≤ 1 := by
    intro i
    simpa using Finset.card_le_card
      (MvPolynomial.support_monomial_subset (s := exponent i) (a := (1 : ℤ)))
  have hg : g ≠ 0 := by
    intro hz
    obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.mpr hG
    let i : Fin s := E.symm ⟨m, hm⟩
    have hi := congrFun hz i
    have hc : G.coeff m = 0 := by
      have hcQ : ((G.coeff m : ℤ) : ℚ) = 0 := by
        simpa [g, exponent, i] using hi
      exact_mod_cast hcQ
    exact (MvPolynomial.mem_support_iff.mp hm) hc
  have hrelation : ∀ z ∈ Z,
      ∑ i, g i * (MvPolynomial.eval z (mon i) : ℚ) = 0 := by
    intro z hz
    have hsum :
        (∑ i, G.coeff (exponent i) * MvPolynomial.eval z (mon i)) =
          MvPolynomial.eval z G := by
      calc
        _ = ∑ m : G.support,
            G.coeff m.1 * m.1.prod (fun j k ↦ z j ^ k) := by
          simpa [mon, exponent, MvPolynomial.eval_monomial] using
            (Equiv.sum_comp E
              (fun m : G.support ↦
                G.coeff m.1 * m.1.prod (fun j k ↦ z j ^ k)))
        _ = ∑ m ∈ G.support,
            G.coeff m * m.prod (fun j k ↦ z j ^ k) := by
          exact Finset.sum_coe_sort G.support
            (fun m ↦ G.coeff m * m.prod (fun j k ↦ z j ^ k))
        _ = _ := by
          exact (MvPolynomial.eval_eq z G).symm
    rw [hzero z hz] at hsum
    simpa only [g, Int.cast_sum, Int.cast_mul, Int.cast_zero] using
      congrArg (fun n : ℤ ↦ (n : ℚ)) hsum
  obtain ⟨F, hF, hFhom, hFzero, hFcoeff⟩ :=
    exists_bounded_integral_polynomial_relation mon hmon hmonhom
      hmoncoeff hmonsupport Z hcoord g hg hrelation
  refine ⟨F, hF, hFhom, hFzero, ?_⟩
  intro m
  let D := (e + 1) ^ N
  have hs : s ≤ D := by
    simpa [s, D] using support_card_le_pow_succ_of_isHomogeneous G e hhom
  have hs' : s - 1 ≤ D := (Nat.sub_le s 1).trans hs
  have hone : 1 ≤ max 1 R ^ e := one_le_pow₀ (Nat.le_max_left 1 R)
  have hraw : (F.coeff m).natAbs ≤
      s * (s - 1).factorial * max 1 R ^ (e * (s - 1)) := by
    simpa only [one_mul, mul_one, max_eq_right hone, ← pow_mul, mul_assoc] using
      hFcoeff m
  apply hraw.trans
  exact Nat.mul_le_mul
    (Nat.mul_le_mul hs (Nat.factorial_le hs'))
    (Nat.pow_le_pow_right (Nat.le_max_left 1 R) (Nat.mul_le_mul_left e hs'))

end

end TranslatedDepthSeven
