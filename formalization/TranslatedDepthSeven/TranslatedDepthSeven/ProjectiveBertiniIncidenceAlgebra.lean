import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic

/-!
# The algebra of a generic linear incidence equation

The local algebra needed for integral hyperplane sections: if `a` is nonzero
in a domain and `b` is regular modulo `a`, the equation `a X + b` generates
a prime ideal. The proof saturates by `a` and then eliminates `X` after
inverting `a`. No geometric integrality assertion is used as an input.
-/

namespace TranslatedDepthSeven

noncomputable section
open Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]

/-- A regular pair makes the linear incidence equation saturated with respect
to its first coefficient. -/
theorem bertini_linear_dvd_of_C_mul_dvd
    (a b : R) (ha : a ≠ 0)
    (hb : IsRegular (Ideal.Quotient.mk (Ideal.span ({a} : Set R)) b))
    (p : R[X]) (hp : C a * X + C b ∣ C a * p) :
    C a * X + C b ∣ p := by
  let q := Ideal.Quotient.mk (Ideal.span ({a} : Set R))
  have hqa : q a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  obtain ⟨g, hg⟩ := hp
  have hgcoeff : ∀ i, a ∣ g.coeff i := by
    intro i
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply hb.left.mul_left_eq_zero_iff.mp
    have h := congrArg (fun f : R[X] ↦ (f.map q).coeff i) hg
    simpa only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C,
      Polynomial.map_X, hqa, C_0, zero_mul, zero_add, coeff_zero,
      coeff_C_mul, coeff_map] using h.symm
  obtain ⟨g', hg'⟩ := (C_dvd_iff_dvd_coeff a g).mpr hgcoeff
  refine ⟨g', ?_⟩
  apply mul_left_cancel₀ (show C a ≠ (0 : R[X]) by simpa using ha)
  rw [hg, hg']
  ring

theorem bertini_linear_dvd_of_C_pow_mul_dvd
    (a b : R) (ha : a ≠ 0)
    (hb : IsRegular (Ideal.Quotient.mk (Ideal.span ({a} : Set R)) b))
    (n : ℕ) (p : R[X]) (hp : C a * X + C b ∣ C (a ^ n) * p) :
    C a * X + C b ∣ p := by
  induction n with
  | zero => simpa using hp
  | succ n ih =>
      apply ih
      apply bertini_linear_dvd_of_C_mul_dvd a b ha hb
      simpa only [pow_succ, map_mul, mul_assoc, mul_left_comm (C a)] using hp

omit [IsDomain R] in
/-- Clearing a single localization denominator for all coefficients of a
polynomial. The denominator remains a power of the chosen element. -/
theorem bertini_polynomial_away_clear_denominator
    (a : R) (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization.Away a S] (p : S[X]) :
    ∃ (n : ℕ) (q : R[X]), q.map (algebraMap R S) = C ((algebraMap R S) a ^ n) * p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨n, p', hp'⟩ := hp
      obtain ⟨m, q', hq'⟩ := hq
      refine ⟨n + m, C (a ^ m) * p' + C (a ^ n) * q', ?_⟩
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
        map_pow, hp', hq', pow_add, map_mul]
      ring
  | monomial i c =>
      obtain ⟨n, d, hd⟩ := IsLocalization.Away.surj a c
      refine ⟨n, monomial i d, ?_⟩
      simp only [map_monomial, C_mul_monomial]
      congr 1
      exact hd.symm.trans (mul_comm _ _)

/-- A primitive linear polynomial supplied by a regular pair generates a
prime ideal. This applies without a factoriality or normality hypothesis. -/
theorem bertini_linear_span_isPrime_of_regular_pair
    (a b : R) (ha : a ≠ 0)
    (hb : IsRegular (Ideal.Quotient.mk (Ideal.span ({a} : Set R)) b)) :
    (Ideal.span ({C a * X + C b} : Set R[X])).IsPrime := by
  let S := Localization.Away a
  letI : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S
    (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  let f : R →+* S := algebraMap R S
  let v : S := IsLocalization.Away.invSelf a
  have hv : f a * v = 1 := IsLocalization.Away.mul_invSelf a
  let t : S := -(f b) * v
  let e : R[X] →+* S := Polynomial.eval₂RingHom f t
  let L : R[X] := C a * X + C b
  have hL : e L = 0 := by
    simp only [e, L, Polynomial.coe_eval₂RingHom, eval₂_add, eval₂_mul, eval₂_C, eval₂_X]
    change f a * (-(f b) * v) + f b = 0
    calc
      _ = -(f b) * (f a * v) + f b := by ring
      _ = 0 := by rw [hv]; ring
  have hlin : L.map f * C v = X - C t := by
    calc
      _ = C (f a * v) * X + C (f b * v) := by
        simp only [L, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
          Polynomial.map_X, map_mul]
        ring
      _ = X - C t := by
        rw [hv]
        have ht : t = -(f b * v) := by dsimp only [t]; ring
        rw [ht, map_neg]
        simp only [C_1, one_mul, sub_neg_eq_add]
  have hker : Ideal.span ({L} : Set R[X]) = RingHom.ker e := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      intro p hp
      rcases hp with rfl
      exact hL
    · intro p hp
      have hroot : (p.map f).IsRoot t := by
        simpa only [Polynomial.IsRoot, Polynomial.eval_map] using hp
      obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
      have hq' : p.map f = L.map f * (C v * q) := by
        rw [hq, ← hlin, mul_assoc]
      obtain ⟨n, q', hq'clear⟩ :=
        bertini_polynomial_away_clear_denominator a S (C v * q)
      have hprod : C (a ^ n) * p = L * q' := by
        apply Polynomial.map_injective f
          (IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors ha))
        simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, map_pow]
        rw [hq'clear, hq']
        change C ((algebraMap R S) a) ^ n * _ = _
        rw [← map_pow]
        ring
      apply Ideal.mem_span_singleton.mpr
      exact bertini_linear_dvd_of_C_pow_mul_dvd a b ha hb n p ⟨q', hprod⟩
  rw [hker]
  exact RingHom.ker_isPrime e

/-- A linear polynomial whose leading coefficient is regular is itself
regular, even when its coefficient ring has zero divisors. -/
theorem bertini_linear_polynomial_isRegular
    {A : Type*} [CommRing A] (b c : A) (hb : IsRegular b) :
    IsRegular (C b * X + C c : A[X]) := by
  have hleft : IsLeftRegular (C b * X + C c : A[X]) := by
    apply isLeftRegular_of_non_zero_divisor
    intro p hp
    have hc := congrArg (fun f : A[X] ↦ f.coeff (p.natDegree + 1)) hp
    have htop : p.coeff (p.natDegree + 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by omega)
    have hz : b * p.leadingCoeff = 0 := by
      simpa only [add_mul, mul_assoc, coeff_add, coeff_C_mul, coeff_X_mul,
        htop, mul_zero, add_zero, coeff_zero, coeff_natDegree] using hc
    exact leadingCoeff_eq_zero.mp (hb.left.mul_left_eq_zero_iff.mp hz)
  exact ⟨hleft, hleft.right_of_commute (fun _ ↦ Commute.all _ _)⟩

omit [IsDomain R] in
/-- Reduction of coefficients detects regularity modulo the constant
polynomial `C a`. -/
theorem bertini_polynomial_quotient_isRegular_of_map
    (a : R) (p : R[X])
    (hp : IsRegular (p.map (Ideal.Quotient.mk (Ideal.span ({a} : Set R))))) :
    IsRegular (Ideal.Quotient.mk (Ideal.span ({C a} : Set R[X])) p) := by
  let q := Ideal.Quotient.mk (Ideal.span ({a} : Set R))
  let I : Ideal R[X] := Ideal.span {C a}
  have hqa : q a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hleft : IsLeftRegular (Ideal.Quotient.mk I p) := by
    apply isLeftRegular_of_non_zero_divisor
    intro x hx
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hpg : C a ∣ p * g := by
      apply Ideal.mem_span_singleton.mp
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [map_mul] using hx
    have hmap : (p * g).map q = 0 := by
      obtain ⟨h, hh⟩ := hpg
      rw [hh, Polynomial.map_mul, Polynomial.map_C, hqa, C_0, zero_mul]
    rw [Polynomial.map_mul] at hmap
    have hg : g.map q = 0 := hp.left.mul_left_eq_zero_iff.mp hmap
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.mem_span_singleton.mpr
    apply (C_dvd_iff_dvd_coeff a g).mpr
    intro i
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have h := congrArg (fun f ↦ Polynomial.coeff f i) hg
    simpa only [coeff_map, coeff_zero] using h
  exact ⟨hleft, hleft.right_of_commute (fun _ ↦ Commute.all _ _)⟩

/-- The two-parameter affine incidence equation is prime whenever the two
coordinate differences form a regular pair. Other coefficient variables
may already be included in the domain `R`. -/
theorem bertini_bilinear_incidence_span_isPrime
    (a b c : R) (ha : a ≠ 0)
    (hb : IsRegular (Ideal.Quotient.mk (Ideal.span ({a} : Set R)) b)) :
    (Ideal.span ({C (C a) * X + C (C b * X + C c)} : Set R[X][X])).IsPrime := by
  apply bertini_linear_span_isPrime_of_regular_pair (C a) (C b * X + C c)
    (by simpa using ha)
  apply bertini_polynomial_quotient_isRegular_of_map
  simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
    using bertini_linear_polynomial_isRegular
      (Ideal.Quotient.mk (Ideal.span ({a} : Set R)) b)
      (Ideal.Quotient.mk (Ideal.span ({a} : Set R)) c) hb

omit [IsDomain R] in
/-- A regular pair of coefficients remains a regular pair after adjoining
any family of independent polynomial variables. -/
theorem bertini_mvPolynomial_regular_pair
    (σ : Type*) (a b : R)
    (hb : IsRegular (Ideal.Quotient.mk (Ideal.span ({a} : Set R)) b)) :
    IsRegular (Ideal.Quotient.mk
      (Ideal.span ({MvPolynomial.C a} : Set (MvPolynomial σ R))) (MvPolynomial.C b)) := by
  let I : Ideal (MvPolynomial σ R) := Ideal.span {MvPolynomial.C a}
  let q := Ideal.Quotient.mk (Ideal.span ({a} : Set R))
  have hleft : IsLeftRegular (Ideal.Quotient.mk I (MvPolynomial.C b)) := by
    apply isLeftRegular_of_non_zero_divisor
    intro x hx
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hprod : MvPolynomial.C a ∣ MvPolynomial.C b * g := by
      apply Ideal.mem_span_singleton.mp
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [map_mul] using hx
    have hcoeff := (MvPolynomial.C_dvd_iff_dvd_coeff a _).mp hprod
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.mem_span_singleton.mpr
    apply (MvPolynomial.C_dvd_iff_dvd_coeff a g).mpr
    intro i
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply hb.left.mul_left_eq_zero_iff.mp
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr (hcoeff i))
    simpa only [MvPolynomial.coeff_C_mul, map_mul] using h
  exact ⟨hleft, hleft.right_of_commute (fun _ ↦ Commute.all _ _)⟩

/-- A literal incidence equation with two regular coordinate coefficients
and arbitrarily many other polynomial coefficients has a prime ideal. -/
theorem bertini_polynomial_incidence_span_isPrime
    (σ : Type*) (a b : R) (c : MvPolynomial σ R) (ha : a ≠ 0)
    (hb : IsRegular (Ideal.Quotient.mk (Ideal.span ({a} : Set R)) b)) :
    (Ideal.span ({C (C (MvPolynomial.C a)) * X +
      C (C (MvPolynomial.C b) * X + C c)} : Set (MvPolynomial σ R)[X][X])).IsPrime := by
  exact bertini_bilinear_incidence_span_isPrime
    (MvPolynomial.C a) (MvPolynomial.C b) c (by simpa using ha)
    (bertini_mvPolynomial_regular_pair σ a b hb)

/-- Constants embed into the linear-incidence quotient as soon as the
coefficient of its distinguished variable is nonzero. -/
theorem bertini_linear_quotient_C_ne_zero
    (a b c : R) (ha : a ≠ 0) (hc : c ≠ 0) :
    Ideal.Quotient.mk (Ideal.span ({C a * X + C b} : Set R[X])) (C c) ≠ 0 := by
  let f := algebraMap R (FractionRing R)
  have hf : Function.Injective f := IsFractionRing.injective R (FractionRing R)
  have hfa : f a ≠ 0 := fun h ↦ ha (hf (h.trans (map_zero f).symm))
  let t : FractionRing R := -(f b) / f a
  let e := Polynomial.eval₂RingHom f t
  have hL : C a * X + C b ∈ RingHom.ker e := by
    change e (C a * X + C b) = 0
    simp only [e, Polynomial.coe_eval₂RingHom, eval₂_add, eval₂_mul, eval₂_C, eval₂_X]
    dsimp only [t]
    field_simp
    ring
  have hle : Ideal.span ({C a * X + C b} : Set R[X]) ≤ RingHom.ker e :=
    Ideal.span_le.mpr (by intro p hp; rcases hp with rfl; exact hL)
  intro hz
  have h := hle (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have he : f c = 0 := by
    simpa only [RingHom.mem_ker, e, Polynomial.coe_eval₂RingHom, eval₂_C] using h
  exact hc (hf (he.trans (map_zero f).symm))

end
end TranslatedDepthSeven
