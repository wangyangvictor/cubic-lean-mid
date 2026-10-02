import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Elimination of one rational coordinate

For an irreducible rational polynomial `F` which depends on the selected
coordinate, and a polynomial `D` not divisible by `F`, we construct a nonzero
polynomial in the remaining coordinates in the ideal `(F,D)`.

The proof uses the actual chosen-coordinate polynomial-ring equivalence,
Gauss's lemma over its coefficient fraction field, and the Sylvester
resultant identity. All the algebra is proved; this module has no literature
input or additional hypothesis beyond the displayed polynomial conditions.
-/

noncomputable section

namespace CubicTenVariables.RationalElimination

open MvPolynomial

/-- Regard the selected coordinate as the univariate polynomial variable. -/
def coordinatePolynomialEquiv {m : ℕ} (i : Fin (m + 1)) :
    MvPolynomial (Fin (m + 1)) ℚ ≃ₐ[ℚ] Polynomial (MvPolynomial (Fin m) ℚ) :=
  (renameEquiv ℚ (finSuccEquiv' i)).trans (optionEquivLeft ℚ (Fin m))

@[simp] theorem coordinatePolynomialEquiv_rename {m : ℕ} (i : Fin (m + 1))
    (R : MvPolynomial (Fin m) ℚ) :
    coordinatePolynomialEquiv i (rename i.succAbove R) = Polynomial.C R := by
  induction R using MvPolynomial.induction_on with
  | C a => simp [coordinatePolynomialEquiv, optionEquivLeft_C]
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    simp [coordinatePolynomialEquiv, optionEquivLeft_X_some] at hp ⊢
    exact hp

@[simp] theorem coordinatePolynomialEquiv_symm_C {m : ℕ} (i : Fin (m + 1))
    (R : MvPolynomial (Fin m) ℚ) :
    (coordinatePolynomialEquiv i).symm (Polynomial.C R) = rename i.succAbove R := by
  apply (coordinatePolynomialEquiv i).injective
  simp

@[simp] theorem pderiv_rename_succAbove {m : ℕ} (i : Fin (m + 1))
    (R : MvPolynomial (Fin m) ℚ) : pderiv i (rename i.succAbove R) = 0 := by
  induction R using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp => simp [hp, Fin.succAbove_ne]

theorem coordinatePolynomialEquiv_natDegree_ne_zero {m : ℕ} (i : Fin (m + 1))
    (F : MvPolynomial (Fin (m + 1)) ℚ) (hi : pderiv i F ≠ 0) :
    (coordinatePolynomialEquiv i F).natDegree ≠ 0 := by
  intro h
  have he := Polynomial.eq_C_of_natDegree_eq_zero h
  have hF := congrArg (coordinatePolynomialEquiv i).symm he
  simp only [AlgEquiv.symm_apply_apply, coordinatePolynomialEquiv_symm_C] at hF
  apply hi
  rw [hF, pderiv_rename_succAbove]

/-- An irreducible nonconstant univariate polynomial and a polynomial not
divisible by it generate a nonzero constant over their original GCD domain.
The primitive part and its content keep denominator clearing explicit. -/
theorem exists_constant_in_span
    {R : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]
    (f g : Polynomial R) (hf : Irreducible f) (hfdeg : f.natDegree ≠ 0)
    (hfg : ¬ f ∣ g) :
    ∃ a b : Polynomial R, ∃ r : R, r ≠ 0 ∧ a * f + b * g = Polynomial.C r := by
  let K := FractionRing R
  let φ := algebraMap R K
  have hφ : Function.Injective φ := IsFractionRing.injective R K
  have hfp : f.IsPrimitive := hf.isPrimitive hfdeg
  have hgp : g.primPart.IsPrimitive := Polynomial.isPrimitive_primPart g
  have hfi : Irreducible (f.map φ) :=
    hfp.irreducible_iff_irreducible_map_fraction_map.mp hf
  have hnot : ¬ f.map φ ∣ g.primPart.map φ := by
    intro h
    exact hfg ((hfp.dvd_of_fraction_map_dvd_fraction_map hgp h).trans g.primPart_dvd)
  have hcop : IsCoprime (f.map φ) (g.primPart.map φ) :=
    (hfi.isCoprime_or_dvd _).resolve_right hnot
  have hres : f.resultant g.primPart ≠ 0 := by
    intro h
    have hn := Polynomial.resultant_ne_zero (f.map φ) (g.primPart.map φ) hcop
    apply hn
    rw [Polynomial.natDegree_map_eq_of_injective hφ,
      Polynomial.natDegree_map_eq_of_injective hφ,
      Polynomial.resultant_map_map, h, map_zero]
  have hg : g ≠ 0 := by rintro rfl; exact hfg (dvd_zero _)
  have hc : g.content ≠ 0 := fun h => hg (Polynomial.content_eq_zero_iff.mp h)
  obtain ⟨a, b, _, _, hab⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
    f g.primPart le_rfl le_rfl (Or.inl hfdeg)
  refine ⟨Polynomial.C g.content * a, b, g.content * f.resultant g.primPart,
    mul_ne_zero hc hres, ?_⟩
  calc
    Polynomial.C g.content * a * f + b * g =
        Polynomial.C g.content * (f * a + g.primPart * b) := by
      conv_lhs => arg 2; arg 2; rw [g.eq_C_content_mul_primPart]
      ring
    _ = Polynomial.C (g.content * f.resultant g.primPart) := by rw [hab, map_mul]

/-- A literal elimination identity after deleting any chosen coordinate.
The right hand side is a nonzero rational polynomial in the remaining
coordinates, embedded by `Fin.succAbove`. -/
theorem exists_elimination_identity {m : ℕ} (i : Fin (m + 1))
    (F D : MvPolynomial (Fin (m + 1)) ℚ) (hF : Irreducible F)
    (hFD : ¬ F ∣ D) (hi : pderiv i F ≠ 0) :
    ∃ A B : MvPolynomial (Fin (m + 1)) ℚ,
      ∃ R : MvPolynomial (Fin m) ℚ,
        R ≠ 0 ∧ A * F + B * D = rename i.succAbove R := by
  classical
  let e := coordinatePolynomialEquiv i
  letI : NormalizedGCDMonoid (MvPolynomial (Fin m) ℚ) := Classical.choice inferInstance
  have hf : Irreducible (e F) := (MulEquiv.irreducible_iff e).mpr hF
  have hdeg : (e F).natDegree ≠ 0 := coordinatePolynomialEquiv_natDegree_ne_zero i F hi
  have hnot : ¬ e F ∣ e D := by
    intro h
    exact hFD ((map_dvd_iff e).mp h)
  obtain ⟨a, b, r, hr, hab⟩ := exists_constant_in_span (e F) (e D) hf hdeg hnot
  refine ⟨e.symm a, e.symm b, r, hr, ?_⟩
  have h := congrArg e.symm hab
  simpa [e] using h

end CubicTenVariables.RationalElimination
