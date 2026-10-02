import CubicTenVariables.CubicAffineFactorization
import Mathlib.Data.Finsupp.Weight

/-! Finite coefficient equations for normalized affine cubic factors.
The coefficients of a linear and a quadratic polynomial are the variables
of the chart. One normalization equation and the coefficients through
degree three of F-LQ are its finite defining equations. The coefficient
ring may itself be a parameter-polynomial ring. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CubicTenVariables.CubicFactorCharts
open MvPolynomial
open scoped BigOperators

/-- The finite exponent vectors of bounded total degree. -/
abbrev Monomial (n d : ℕ) := {m : Fin n →₀ ℕ // m.degree ≤ d}

noncomputable instance monomialFintype (n d : ℕ) : Fintype (Monomial n d) :=
  (Finsupp.finite_of_degree_le (σ := Fin n) d).fintype

/-- Recover a bounded polynomial from its literal coefficient table. -/
def polynomial {n d : ℕ} {R : Type*} [CommRing R]
    (a : Monomial n d → R) : MvPolynomial (Fin n) R :=
  ∑ m, MvPolynomial.monomial m.val (a m)

@[simp] theorem coeff_polynomial {n d : ℕ} {R : Type*} [CommRing R]
    (a : Monomial n d → R) (m : Monomial n d) :
    coeff m.val (polynomial a) = a m := by
  classical
  simp only [polynomial, coeff_sum, coeff_monomial]
  rw [Finset.sum_eq_single m]
  · simp
  · intro k _ hkm
    simp [show k.val ≠ m.val from fun h => hkm (Subtype.ext h)]
  · simp

theorem coeff_polynomial_eq_zero {n d : ℕ} {R : Type*} [CommRing R]
    (a : Monomial n d → R) (m : Fin n →₀ ℕ) (hm : ¬ m.degree ≤ d) :
    coeff m (polynomial a) = 0 := by
  classical
  simp only [polynomial, coeff_sum, coeff_monomial]
  apply Finset.sum_eq_zero
  intro k _
  have hk : k.val ≠ m := fun h => hm (h ▸ k.property)
  simp [hk]

theorem polynomial_totalDegree_le {n d : ℕ} {R : Type*} [CommRing R]
    (a : Monomial n d → R) : (polynomial a).totalDegree ≤ d := by
  apply totalDegree_finsetSum_le
  intro m _
  exact (totalDegree_monomial_le m.val (a m)).trans m.property

theorem polynomial_coefficients {n d : ℕ} {R : Type*} [CommRing R]
    (F : MvPolynomial (Fin n) R) (hF : F.totalDegree ≤ d) :
    polynomial (fun m : Monomial n d => coeff m.val F) = F := by
  classical
  ext m
  by_cases hm : m.degree ≤ d
  · exact coeff_polynomial _ ⟨m, hm⟩
  · rw [coeff_polynomial_eq_zero _ m hm,
      coeff_eq_zero_of_totalDegree_lt (lt_of_le_of_lt hF (Nat.lt_of_not_ge hm))]

theorem map_polynomial {n d : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (ρ : R →+* S) (a : Monomial n d → R) :
    map ρ (polynomial a) = polynomial (fun m => ρ (a m)) := by
  classical
  simp [polynomial]

/-- Distinct coefficient slots for the two factors. -/
abbrev FactorVar (n : ℕ) := Monomial n 1 ⊕ Monomial n 2

/-- The normalization equation and the bounded coefficient equations. -/
abbrev EquationIndex (n : ℕ) := Option (Monomial n 3)

def linear {n : ℕ} {R : Type*} [CommRing R] (x : FactorVar n → R) :
    MvPolynomial (Fin n) R := polynomial (fun m => x (.inl m))

def quadratic {n : ℕ} {R : Type*} [CommRing R] (x : FactorVar n → R) :
    MvPolynomial (Fin n) R := polynomial (fun m => x (.inr m))

def linearExponent {n : ℕ} (i : Fin n) : Monomial n 1 :=
  ⟨Finsupp.single i 1, by simp⟩

def universalLinear (n : ℕ) (R : Type*) [CommRing R] :
    MvPolynomial (Fin n) (MvPolynomial (FactorVar n) R) := linear X

def universalQuadratic (n : ℕ) (R : Type*) [CommRing R] :
    MvPolynomial (Fin n) (MvPolynomial (FactorVar n) R) := quadratic X

def equations {n : ℕ} {R : Type*} [CommRing R]
    (F : MvPolynomial (Fin n) R) (i : Fin n) :
    EquationIndex n → MvPolynomial (FactorVar n) R
  | none => X (.inl (linearExponent i)) - 1
  | some m => coeff m.val
      (map C F - universalLinear n R * universalQuadratic n R)

@[simp] theorem specialize_linear {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (ρ : R →+* S) (x : FactorVar n → S) :
    map (eval₂Hom ρ x) (universalLinear n R) = linear x := by
  simp [universalLinear, linear, map_polynomial]

@[simp] theorem specialize_quadratic {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (ρ : R →+* S) (x : FactorVar n → S) :
    map (eval₂Hom ρ x) (universalQuadratic n R) = quadratic x := by
  simp [universalQuadratic, quadratic, map_polynomial]

/-- Specialization of each coefficient equation is the literal coefficient
of the difference between the specialized cubic and the two factors. -/
theorem eval_equations_some {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (ρ : R →+* S) (F : MvPolynomial (Fin n) R) (i : Fin n)
    (x : FactorVar n → S) (m : Monomial n 3) :
    eval₂Hom ρ x (equations F i (.some m)) =
      coeff m.val (map ρ F) - coeff m.val (linear x * quadratic x) := by
  have hc : (eval₂Hom ρ x).comp (C : R →+* MvPolynomial (FactorVar n) R) = ρ := by
    ext a
    simp
  change eval₂Hom ρ x (coeff m.val _) = _
  rw [← coeff_map, map_sub, map_mul, specialize_linear, specialize_quadratic,
    MvPolynomial.map_map, hc, coeff_sub]

/-- The finite chart equations express exactly normalized factorization,
whenever the specialized target has total degree at most three. -/
theorem vanishing_iff {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (ρ : R →+* S) (F : MvPolynomial (Fin n) R) (i : Fin n)
    (x : FactorVar n → S) (hF : (map ρ F).totalDegree ≤ 3) :
    (∀ e, eval₂Hom ρ x (equations F i e) = 0) ↔
      coeff (Finsupp.single i 1) (linear x) = 1 ∧
      map ρ F = linear x * quadratic x := by
  have hlinear : coeff (Finsupp.single i 1) (linear x) = x (.inl (linearExponent i)) :=
    coeff_polynomial _ (linearExponent i)
  have hprod : (linear x * quadratic x).totalDegree ≤ 3 :=
    (totalDegree_mul _ _).trans (add_le_add
      (polynomial_totalDegree_le (fun m : Monomial n 1 => x (.inl m)))
      (polynomial_totalDegree_le (fun m : Monomial n 2 => x (.inr m))))
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have hh := h none
      simpa [equations, ← hlinear, sub_eq_zero] using hh
    · ext m
      by_cases hm : m.degree ≤ 3
      · exact sub_eq_zero.mp (by simpa only [eval_equations_some] using h (some ⟨m, hm⟩))
      · rw [coeff_eq_zero_of_totalDegree_lt (lt_of_le_of_lt hF (Nat.lt_of_not_ge hm)),
          coeff_eq_zero_of_totalDegree_lt (lt_of_le_of_lt hprod (Nat.lt_of_not_ge hm))]
  · rintro ⟨hi, heq⟩ e
    cases e with
    | none => simpa [equations, ← hlinear, sub_eq_zero] using hi
    | some m => rw [eval_equations_some, heq, sub_self]

@[simp] theorem map_universalLinear {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (ρ : R →+* S) :
    map (MvPolynomial.map ρ) (universalLinear n R) = universalLinear n S := by
  simp [universalLinear, linear, map_polynomial]

@[simp] theorem map_universalQuadratic {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (ρ : R →+* S) :
    map (MvPolynomial.map ρ) (universalQuadratic n R) = universalQuadratic n S := by
  simp [universalQuadratic, quadratic, map_polynomial]

/-- The actual chart equations commute with arbitrary change of the
coefficient ring, including specialization of coefficient parameters. -/
theorem map_equations {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (ρ : R →+* S) (F : MvPolynomial (Fin n) R) (i : Fin n) (e : EquationIndex n) :
    map ρ (equations F i e) = equations (map ρ F) i e := by
  cases e with
  | none => simp [equations]
  | some m =>
    have hc : (MvPolynomial.map ρ).comp (C : R →+* MvPolynomial (FactorVar n) R) =
        (C : S →+* MvPolynomial (FactorVar n) S).comp ρ := by
      ext a
      simp
    change map ρ (coeff m.val _) = coeff m.val _
    rw [← coeff_map, map_sub, map_mul, map_universalLinear, map_universalQuadratic,
      MvPolynomial.map_map, MvPolynomial.map_map, hc]

/-- Every normalized degree-one times degree-two factorization is recovered
by its own coefficient table; every chart solution yields such factors. -/
theorem exists_solution_iff {n : ℕ} {R K : Type*} [CommRing R] [Field K]
    (ρ : R →+* K) (F : MvPolynomial (Fin n) R) (i : Fin n)
    (hF : (map ρ F).totalDegree = 3) :
    (∃ x : FactorVar n → K, ∀ e, eval₂Hom ρ x (equations F i e) = 0) ↔
      ∃ L Q : MvPolynomial (Fin n) K,
        coeff (Finsupp.single i 1) L = 1 ∧
        L.totalDegree = 1 ∧ Q.totalDegree = 2 ∧ map ρ F = L * Q := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨hi, heq⟩ := (vanishing_iff ρ F i x hF.le).mp hx
    have hF0 : map ρ F ≠ 0 := by intro h; simp [h] at hF
    have hL0 : linear x ≠ 0 := by intro h; simp [h] at heq; exact hF0 heq
    have hQ0 : quadratic x ≠ 0 := by intro h; simp [h] at heq; exact hF0 heq
    have hd : (linear x).totalDegree + (quadratic x).totalDegree = 3 := by
      rw [← totalDegree_mul_of_isDomain hL0 hQ0, ← heq, hF]
    have hL := polynomial_totalDegree_le (fun m : Monomial n 1 => x (.inl m))
    have hQ := polynomial_totalDegree_le (fun m : Monomial n 2 => x (.inr m))
    change (linear x).totalDegree ≤ 1 at hL
    change (quadratic x).totalDegree ≤ 2 at hQ
    exact ⟨linear x, quadratic x, hi, by omega, by omega, heq⟩
  · rintro ⟨L, Q, hi, hL, hQ, heq⟩
    let x : FactorVar n → K := Sum.elim
      (fun m : Monomial n 1 => coeff m.val L)
      (fun m : Monomial n 2 => coeff m.val Q)
    have hLx : linear x = L := polynomial_coefficients L hL.le
    have hQx : quadratic x = Q := polynomial_coefficients Q hQ.le
    refine ⟨x, (vanishing_iff ρ F i x hF.le).mpr ?_⟩
    rw [hLx, hQx]
    exact ⟨hi, heq⟩

/-- Reducibility of the specialized cubic is exactly the existence of a
solution in one of the finite normalized factor charts. -/
theorem not_irreducible_iff_exists_solution
    {n : ℕ} {R K : Type*} [CommRing R] [Field K]
    (ρ : R →+* K) (F : MvPolynomial (Fin n) R)
    (hF : (map ρ F).totalDegree = 3) :
    (¬ Irreducible (map ρ F)) ↔
      ∃ (i : Fin n) (x : FactorVar n → K),
        ∀ e, eval₂Hom ρ x (equations F i e) = 0 := by
  rw [CubicAffineFactorization.not_irreducible_iff_normalized_factor (map ρ F) hF]
  constructor
  · rintro ⟨i, L, Q, hL, hdL, hdQ, heq⟩
    obtain ⟨x, hx⟩ := (exists_solution_iff ρ F i hF).mpr ⟨L, Q, hL, hdL, hdQ, heq⟩
    exact ⟨i, x, hx⟩
  · rintro ⟨i, x, hx⟩
    exact ⟨i, (exists_solution_iff ρ F i hF).mp ⟨x, hx⟩⟩

/-- The actual specialized quotient is a domain precisely when every
normalized factor chart has empty field-valued zero locus. -/
theorem isDomain_iff_no_solution
    {n : ℕ} {R K : Type*} [CommRing R] [Field K]
    (ρ : R →+* K) (F : MvPolynomial (Fin n) R)
    (hF : (map ρ F).totalDegree = 3) :
    IsDomain (MvPolynomial (Fin n) K ⧸ Ideal.span {map ρ F}) ↔
      ¬ ∃ (i : Fin n) (x : FactorVar n → K),
        ∀ e, eval₂Hom ρ x (equations F i e) = 0 := by
  rw [← not_irreducible_iff_exists_solution ρ F hF, not_not]
  have hF0 : map ρ F ≠ 0 := by intro h; simp [h] at hF
  rw [Ideal.Quotient.isDomain_iff_prime, Ideal.span_singleton_prime hF0]
  exact ⟨fun h => h.irreducible, fun h => h.prime⟩

end CubicTenVariables.CubicFactorCharts
