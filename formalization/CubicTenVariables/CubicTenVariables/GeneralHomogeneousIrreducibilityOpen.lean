import CubicTenVariables.GeneralHomogeneousFactorMinors
import CubicTenVariables.GeneralHomogeneousFactorization
import CubicTenVariables.HomogeneousOriginOpenFinite

/-!
# An elementary fixed-degree irreducibility open

Reducibility of a degree-`d` homogeneous form is detected by the finitely
many maximal-minor systems for factor degrees `1, ..., d-1`.  Applying the
proved homogeneous-origin certificate to each system gives one literal
coefficient-ring element whose nonvanishing preserves irreducibility over
every algebraically closed target field.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
noncomputable section
open scoped BigOperators Classical

namespace CubicTenVariables.GeneralHomogeneousIrreducibilityOpen

open MvPolynomial CubicFactorCharts GeneralHomogeneousFactorMinors
open GeneralHomogeneousFactorization

variable {R : Type*} [CommRing R] {n d e : ℕ}

theorem exists_coefficients_iff (he : e ≤ d)
    (a : Monomial n e → R) (F : MvPolynomial (Fin n) R)
    (hF : F.totalDegree ≤ d) :
    (∃ c : Monomial n (d - e) → R,
      (multiplicationMatrix d e a).mulVec c =
        fun row : Monomial n d ↦ coeff row.val F) ↔
      ∃ Q : MvPolynomial (Fin n) R,
        Q.totalDegree ≤ d - e ∧ F = polynomial a * Q := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨polynomial c, polynomial_totalDegree_le c, ?_⟩
    have h := congrArg polynomial hc
    rw [polynomial_multiplicationMatrix_mulVec he,
      polynomial_coefficients F hF] at h
    exact h.symm
  · rintro ⟨Q, hQ, heq⟩
    refine ⟨fun m ↦ coeff m.val Q, ?_⟩
    rw [multiplicationMatrix_mulVec he, polynomial_coefficients Q hQ, ← heq]

theorem not_irreducible_iff_projective_solution {K : Type*} [Field K]
    (F : MvPolynomial (Fin n) K) (hd : 1 ≤ d)
    (hF : F.IsHomogeneous d) (hF0 : F ≠ 0) :
    (¬ Irreducible F) ↔
      ∃ e : ℕ, 1 ≤ e ∧ e < d ∧
        ∃ a : Monomial n e → K, a ≠ 0 ∧
          ∀ i : EquationIndex n d e, eval a (equations d e F i) = 0 := by
  constructor
  · intro hred
    obtain ⟨e, he1, hed, A, B, hA, hB, hA0, _hB0, hprod⟩ :=
      exists_homogeneous_factorization_of_not_irreducible F hd hF hF0 hred
    let a : Monomial n e → K := fun m ↦ coeff m.val A
    have hpa : polynomial a = A := polynomial_coefficients A hA.totalDegree_le
    have ha : a ≠ 0 := by
      intro hz
      apply hA0
      rw [← hpa, hz]
      simp [polynomial]
    have hmatrix : ∃ c : Monomial n (d - e) → K,
        (multiplicationMatrix d e a).mulVec c =
          fun row : Monomial n d ↦ coeff row.val F := by
      apply (exists_coefficients_iff hed.le a F hF.totalDegree_le).mpr
      exact ⟨B, hB.totalDegree_le, by rwa [hpa]⟩
    refine ⟨e, he1, hed, a, ha,
      (vanishing_iff_solution hed.le F a ha).mpr hmatrix⟩
  · rintro ⟨e, he1, hed, a, ha, hzero⟩ hirr
    have hmatrix := (vanishing_iff_solution hed.le F a ha).mp hzero
    obtain ⟨Q, hQ, hprod⟩ :=
      (exists_coefficients_iff hed.le a F hF.totalDegree_le).mp hmatrix
    have hpa0 : polynomial a ≠ 0 := by
      intro hz
      apply ha
      ext m
      simpa only [coeff_polynomial, coeff_zero] using congrArg (coeff m.val) hz
    have hQ0 : Q ≠ 0 := by
      intro hz
      apply hF0
      rw [hprod, hz, mul_zero]
    have hsum : (polynomial a).totalDegree + Q.totalDegree = d := by
      rw [← totalDegree_mul_of_isDomain hpa0 hQ0, ← hprod,
        hF.totalDegree hF0]
    have hpa_le := polynomial_totalDegree_le a
    have hpa_deg : (polynomial a).totalDegree = e := by omega
    have hQ_deg : Q.totalDegree = d - e := by omega
    rcases hirr.isUnit_or_isUnit hprod with hunit | hunit
    · have hz := (isUnit_iff_totalDegree_of_isReduced.mp hunit).2
      omega
    · have hz := (isUnit_iff_totalDegree_of_isReduced.mp hunit).2
      omega

/-- For one fixed possible factor degree, the absence of that factor type
persists on a literal principal open through an arbitrary algebraically
closed specialization. -/
theorem exists_factor_degree_open
    {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    (rho : R →+* Omega) (F : MvPolynomial (Fin n) R)
    (hd : 1 ≤ d) (hF : F.IsHomogeneous d)
    (hirr : Irreducible (map rho F))
    (he1 : 1 ≤ e) (hed : e < d) :
    ∃ s : R, rho s ≠ 0 ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (tau : R →+* K), tau s ≠ 0 →
        ¬ ∃ a : Monomial n e → K, a ≠ 0 ∧
          ∀ i : EquationIndex n d e,
            eval a (equations d e (map tau F) i) = 0 := by
  let f : EquationIndex n d e → MvPolynomial (Monomial n e) R :=
    fun i ↦ equations d e F i
  let degree : EquationIndex n d e → ℕ := fun i ↦ degrees (e := e) i
  have hhom : ∀ i, (f i).IsHomogeneous (degree i) := by
    intro i
    exact equations_homogeneous F i
  have horigin : ∀ a : Monomial n e → Omega,
      (∀ i, eval a (map rho (f i)) = 0) → a = 0 := by
    intro a ha
    by_contra hane
    have hzero : ∀ i : EquationIndex n d e,
        eval a (equations d e (map rho F) i) = 0 := by
      intro i
      rw [← GeneralHomogeneousFactorMinors.map_equations rho F i]
      exact ha i
    have hF0 : map rho F ≠ 0 := hirr.ne_zero
    have hred : ¬ Irreducible (map rho F) :=
      (not_irreducible_iff_projective_solution (map rho F) hd
        (hF.map rho) hF0).mpr ⟨e, he1, hed, a, hane, hzero⟩
    exact hred hirr
  obtain ⟨s, hs, hgood⟩ :=
    HomogeneousOriginOpenFinite.exists_principal_open rho f degree hhom horigin
  refine ⟨s, hs, ?_⟩
  intro K _ _ tau htau
  rintro ⟨a, ha, hzero⟩
  apply ha
  apply hgood K tau htau a
  intro i
  rw [GeneralHomogeneousFactorMinors.map_equations tau F i]
  exact hzero i

/-- Irreducibility of a positive-degree homogeneous equation persists on
one explicit principal open.  This is proved from finite factor matrices
and homogeneous Nullstellensatz certificates, without an AG spreading
input. -/
theorem exists_principal_open
    {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    (rho : R →+* Omega) (F : MvPolynomial (Fin n) R)
    (hd : 1 ≤ d) (hF : F.IsHomogeneous d)
    (hirr : Irreducible (map rho F)) :
    ∃ s : R, rho s ≠ 0 ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (tau : R →+* K), tau s ≠ 0 →
        Irreducible (map tau F) := by
  classical
  let S := Finset.Icc 1 (d - 1)
  let E := ↑S
  letI : Fintype E := Finset.fintypeCoeSort S
  have hcert : ∀ e : E, ∃ s : R, rho s ≠ 0 ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (tau : R →+* K), tau s ≠ 0 →
        ¬ ∃ a : Monomial n e.1 → K, a ≠ 0 ∧
          ∀ i : EquationIndex n d e.1,
            eval a (equations d e.1 (map tau F) i) = 0 := by
    intro e
    have he := Finset.mem_Icc.mp e.2
    apply exists_factor_degree_open rho F hd hF hirr he.1
    omega
  choose s hs hgood using hcert
  obtain ⟨u, hu⟩ : ∃ u, rho (coeff u F) ≠ 0 := by
    by_contra! h
    apply hirr.ne_zero
    ext u
    simpa only [coeff_map, coeff_zero] using h u
  refine ⟨coeff u F * ∏ e : E, s e, ?_, ?_⟩
  · simp only [map_mul, map_prod]
    exact mul_ne_zero hu (Finset.prod_ne_zero_iff.mpr (fun e _ ↦ hs e))
  · intro K _ _ tau htau
    have htau' : tau (coeff u F) ≠ 0 ∧ tau (∏ e : E, s e) ≠ 0 :=
      mul_ne_zero_iff.mp (by simpa only [map_mul] using htau)
    have hprod : ∏ e : E, tau (s e) ≠ 0 := by
      simpa only [map_prod] using htau'.2
    have hF0 : map tau F ≠ 0 := by
      intro hz
      exact htau'.1 (by
        simpa only [coeff_map, coeff_zero] using congrArg (coeff u) hz)
    by_contra hred
    obtain ⟨e, he1, hed, a, ha, hzero⟩ :=
      (not_irreducible_iff_projective_solution (map tau F) hd
        (hF.map tau) hF0).mp hred
    have heMem : e ∈ Finset.Icc 1 (d - 1) := Finset.mem_Icc.mpr ⟨he1, by omega⟩
    let ee : E := ⟨e, heMem⟩
    have hse : tau (s ee) ≠ 0 :=
      Finset.prod_ne_zero_iff.mp hprod ee (Finset.mem_univ ee)
    exact (hgood ee K tau hse) ⟨a, ha, hzero⟩

end CubicTenVariables.GeneralHomogeneousIrreducibilityOpen
