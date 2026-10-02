import TranslatedDepthSeven.FieldPolynomialKrullDimension
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.KrullDimension.PID

/-!
# Heights of maximal ideals in polynomial algebras over a field

For a Noetherian Jacobson ring, a maximal ideal of `R[X]` contracts to a
maximal ideal of `R`.  Flatness gives the height-addition formula.  The
fibre is a polynomial ring over a field, where maximal ideals have height
one.  Induction gives height `n` for every maximal ideal of `k[X₁,…,Xₙ]`.

This is a component of the affine dimension formula, not a claim that
the general height-plus-quotient-dimension formula has already been proved.
-/

namespace TranslatedDepthSeven

noncomputable section

open Polynomial
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

theorem polynomial_maximal_height_eq_contraction_height_add_one
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsJacobsonRing R]
    (M : Ideal (Polynomial R)) [M.IsMaximal] :
    M.height = (M.comap (Polynomial.C : R →+* Polynomial R)).height + 1 := by
  classical
  let p : Ideal R := M.comap Polynomial.C
  letI : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing M
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  letI : M.LiesOver p := ⟨rfl⟩
  let J : Ideal (Polynomial R) := p.map Polynomial.C
  have hJM : J ≤ M := Ideal.map_le_iff_le_comap.mpr le_rfl
  let Q : Ideal (Polynomial R ⧸ J) := M.map (Ideal.Quotient.mk J)
  letI : Q.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le
    Ideal.Quotient.mk_surjective (by simpa only [Ideal.mk_ker] using hJM)
  let e : Polynomial (R ⧸ p) ≃+* (Polynomial R ⧸ J) :=
    p.polynomialQuotientEquivQuotientPolynomial
  let Q' : Ideal (Polynomial (R ⧸ p)) := Q.comap e
  letI : Q'.IsMaximal := by dsimp only [Q']; infer_instance
  have hQ' : Q'.height = 1 :=
    IsPrincipalIdealRing.height_eq_one_of_isMaximal Q' (Polynomial.not_isField (R ⧸ p))
  have hQ : Q.height = 1 := by
    rw [← e.height_comap Q]
    exact hQ'
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p M
  change M.height = p.height + Q.height at h
  simpa only [hQ] using h

/-- All maximal ideals, not just a chosen coordinate maximal ideal, have
the full expected height in a finite polynomial algebra over a field. -/
theorem mvPolynomial_maximal_height_eq
    (K : Type*) [Field K] [CharZero K] (n : ℕ)
    (M : Ideal (MvPolynomial (Fin n) K)) [M.IsMaximal] :
    M.height = (n : ℕ∞) := by
  induction n with
  | zero =>
      apply le_antisymm
      · have h := Ideal.height_le_ringKrullDim_of_ne_top
          (Ideal.IsPrime.ne_top' (I := M))
        rw [ringKrullDim_mvPolynomial_fin_eq_of_field K 0] at h
        exact_mod_cast h
      · exact bot_le
  | succ n ih =>
      let e := MvPolynomial.finSuccEquiv K n
      let M' : Ideal (Polynomial (MvPolynomial (Fin n) K)) := M.map e
      letI : M'.IsMaximal := by dsimp only [M']; infer_instance
      have hheight : M'.height = M.height := e.toRingEquiv.height_map M
      rw [← hheight, polynomial_maximal_height_eq_contraction_height_add_one]
      let p := M'.comap (Polynomial.C : MvPolynomial (Fin n) K →+* _)
      letI : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing M'
      have hp : p.height = (n : ℕ∞) := ih p
      change p.height + 1 = _
      rw [hp]
      simp

end
end TranslatedDepthSeven
