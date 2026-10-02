import CubicTenVariables.UniformPrimeFieldIdealCount
import TranslatedDepthSeven.UniversalBoundedDegreePolynomialFamily
import TranslatedDepthSeven.PerfectFieldPolynomialKrullDimension
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! Uniform prime-field counts for two relatively prime bounded-degree
polynomials.  Relative primality means absence of a common nonunit divisor,
not the stronger assertion that the two polynomials generate the unit ideal.
Two non-zero-divisor dimension drops and the proved uniform ideal count give
the bound.  The coefficient family is fixed before the prime and equations.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.CoprimeCommonZeroCount
open MvPolynomial TranslatedDepthSeven
open scoped BigOperators Classical nonZeroDivisors

/-- Relative primality gives the second regular element, even when the
first hypersurface is reducible or nonreduced. -/
theorem quotient_mk_mem_nonZeroDivisors
    {R : Type*} [CommRing R] [IsDomain R] [DecompositionMonoid R]
    (Q C : R) (hcop : IsRelPrime Q C) :
    Ideal.Quotient.mk (Ideal.span {Q}) C ∈ (R ⧸ Ideal.span {Q})⁰ := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul,Ideal.Quotient.eq_zero_iff_mem,Ideal.mem_span_singleton] at hx
  rw [Ideal.Quotient.eq_zero_iff_mem,Ideal.mem_span_singleton]
  exact hcop.dvd_of_dvd_mul_right hx

private theorem dimension_drop_two {D : WithBot ℕ∞} {m : ℕ}
    (hm : 2 ≤ m) (h : D + 1 + 1 ≤ (m : WithBot ℕ∞)) :
    D ≤ ((m-2 : ℕ) : WithBot ℕ∞) := by
  cases D with
  | bot => exact bot_le
  | coe d =>
    have he : d + 2 ≤ (m : ℕ∞) := by
      have he : d + 1 + 1 ≤ (m : ℕ∞) := by exact_mod_cast h
      simpa only [add_assoc,one_add_one_eq_two] using he
    have he' : d + 2 ≤ ((m-2 : ℕ) : ℕ∞) + 2 := by
      have hc : ((m-2 : ℕ) : ℕ∞) + 2 = (m : ℕ∞) := by
        norm_cast
        omega
      rw [hc]
      exact he
    exact WithBot.coe_le_coe.mpr
      ((ENat.add_le_add_iff_right (by simp : (2 : ℕ∞) ≠ ⊤)).mp he')

/-- The actual two-equation quotient has codimension at least two.
No degree bound, reducedness, or geometric-primality hypothesis is needed. -/
theorem quotient_dimension_le
    {K : Type*} [Field K] [PerfectField K] {m : ℕ} (hm : 2 ≤ m)
    (Q C : MvPolynomial (Fin m) K) (hQ : Q ≠ 0) (hcop : IsRelPrime Q C) :
    ringKrullDim (MvPolynomial (Fin m) K ⧸ Ideal.span {Q,C}) ≤
      ((m-2 : ℕ) : WithBot ℕ∞) := by
  let R := MvPolynomial (Fin m) K
  let I : Ideal R := Ideal.span {Q}
  let J : Ideal R := Ideal.span {Q,C}
  have hIJ : I ≤ J := Ideal.span_mono (by simp)
  let f : (R ⧸ I) →+* (R ⧸ J) := Ideal.Quotient.factor hIJ
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective hIJ
  have hC : Ideal.Quotient.mk I C ∈ (R ⧸ I)⁰ :=
    quotient_mk_mem_nonZeroDivisors Q C hcop
  have hzero : f (Ideal.Quotient.mk I C) = 0 := by
    change Ideal.Quotient.mk J C = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hsecond := ringKrullDim_succ_le_of_surjective f hf hC hzero
  have hfirst := ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    (mem_nonZeroDivisors_iff_ne_zero.mpr hQ)
  have hdim : ringKrullDim (R ⧸ J) + 1 + 1 ≤ (m : WithBot ℕ∞) := by
    calc
      _ ≤ ringKrullDim (R ⧸ I) + 1 := by simpa only [add_comm] using add_le_add_right hsecond 1
      _ ≤ ringKrullDim R := hfirst
      _ = _ := ringKrullDim_mvPolynomial_fin_eq_of_perfectField K m
  exact dimension_drop_two hm hdim

private abbrev CoeffIndex (m D : ℕ) := Fin 2 × BoundedDegreeMonomial m D

private def universal (m D : ℕ) (i : Fin 2) :
    MvPolynomial (Fin m) (MvPolynomial (CoeffIndex m D) ℤ) :=
  ∑ s : BoundedDegreeMonomial m D, monomial s.1 (X (i,s))

private theorem specialize_universal {m D : ℕ} {K : Type*} [CommRing K]
    (f : Fin 2 → MvPolynomial (Fin m) K) (hdeg : ∀ i, (f i).totalDegree ≤ D)
    (i : Fin 2) :
    map (eval₂Hom (Int.castRingHom K) (fun t : CoeffIndex m D => (f t.1).coeff t.2.1))
      (universal m D i) = f i := by
  classical
  simp only [universal,map_sum,map_monomial]
  ext s
  simp only [coeff_sum,coeff_monomial]
  by_cases hs : Finsupp.degree s ≤ D
  · let b : BoundedDegreeMonomial m D := ⟨s,hs⟩
    rw [Finset.sum_eq_single b]
    · simp [b]
    · intro t _ htb
      have hne : t.1 ≠ s := fun he => htb (Subtype.ext he)
      simp [hne]
    · simp
  · have hz : (f i).coeff s = 0 := by
      apply notMem_support_iff.mp
      intro hmem
      apply hs
      simpa [Finsupp.degree_eq_sum,Finsupp.sum_fintype] using
        (le_totalDegree hmem).trans (hdeg i)
    rw [hz]
    apply Finset.sum_eq_zero
    intro t _
    have hne : t.1 ≠ s := fun he => hs (he ▸ t.2)
    simp [hne]

/-- One constant precedes every prime and every relatively prime pair of
polynomials of the displayed bounded degrees.  All primes are included. -/
theorem exists_prime_bound (m D : ℕ) (hm : 2 ≤ m) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (p : ℕ) [Fact p.Prime]
      (Q C : MvPolynomial (Fin m) (ZMod p)),
      Q ≠ 0 → Q.totalDegree ≤ D → C.totalDegree ≤ D → IsRelPrime Q C →
      Nat.card {x : Fin m → ZMod p // eval x Q=0 ∧ eval x C=0} ≤ A*p^(m-2) := by
  classical
  let I := Ideal.span ({universal m D 0,universal m D 1} :
    Set (MvPolynomial (Fin m) (MvPolynomial (CoeffIndex m D) ℤ)))
  obtain ⟨A,hA,hcount⟩ := UniformPrimeFieldIdealCount.exists_bound I
  refine ⟨A,hA,?_⟩
  intro p hp Q C hQ hQD hCD hcop
  let f : Fin 2 → MvPolynomial (Fin m) (ZMod p) := ![Q,C]
  let ρ : MvPolynomial (CoeffIndex m D) ℤ →+* ZMod p :=
    eval₂Hom (Int.castRingHom (ZMod p)) (fun t => (f t.1).coeff t.2.1)
  have hdeg : ∀ i, (f i).totalDegree ≤ D := by
    intro i
    fin_cases i
    · exact hQD
    · exact hCD
  have hs0 : map ρ (universal m D 0) = Q := specialize_universal f hdeg 0
  have hs1 : map ρ (universal m D 1) = C := specialize_universal f hdeg 1
  have hmap : I.map (map ρ) = Ideal.span {Q,C} := by
    simp only [I,Ideal.map_span,Set.image_insert_eq,Set.image_singleton,hs0,hs1]
  have hdim : ringKrullDim (MvPolynomial (Fin m) (ZMod p) ⧸ I.map (map ρ)) ≤
      ((m-2 : ℕ) : WithBot ℕ∞) := by
    rw [hmap]
    exact quotient_dimension_le hm Q C hQ hcop
  have hz (x : Fin m → ZMod p) :
      (∀ P ∈ I, eval₂Hom ρ x P=0) ↔ eval x Q=0 ∧ eval x C=0 := by
    have h0 : eval₂Hom ρ x (universal m D 0) = eval x Q := by
      rw [← hs0,eval_map]; rfl
    have h1 : eval₂Hom ρ x (universal m D 1) = eval x C := by
      rw [← hs1,eval_map]; rfl
    constructor
    · intro hx
      exact ⟨h0 ▸ hx _ (Ideal.subset_span (by simp)),
        h1 ▸ hx _ (Ideal.subset_span (by simp))⟩
    · rintro ⟨hq,hc⟩ P hP
      have hle : I ≤ RingHom.ker (eval₂Hom ρ x) := by
        apply Ideal.span_le.mpr
        intro V hV
        rcases hV with rfl | hV
        · exact h0.trans hq
        · rw [Set.mem_singleton_iff] at hV
          subst V
          exact h1.trans hc
      exact hle hP
  rw [← Nat.card_congr (Equiv.subtypeEquivRight hz)]
  exact hcount p ρ (m-2) hdim

/-- The quadratic/cubic intersection estimate used after projection from
a rational double point. -/
theorem exists_quadratic_cubic_prime_bound (m : ℕ) (hm : 2 ≤ m) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (p : ℕ) [Fact p.Prime]
      (Q C : MvPolynomial (Fin m) (ZMod p)),
      Q ≠ 0 → Q.totalDegree ≤ 2 → C.totalDegree ≤ 3 → IsRelPrime Q C →
      Nat.card {x : Fin m → ZMod p // eval x Q=0 ∧ eval x C=0} ≤ A*p^(m-2) := by
  obtain ⟨A,hA,h⟩ := exists_prime_bound m 3 hm
  exact ⟨A,hA,fun p _ Q C hQ hQD hCD hcop =>
    h p Q C hQ (hQD.trans (by decide)) hCD hcop⟩

end CubicTenVariables.CoprimeCommonZeroCount
