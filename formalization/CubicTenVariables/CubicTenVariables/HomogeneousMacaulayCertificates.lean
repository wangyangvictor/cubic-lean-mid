import CubicTenVariables.HomogeneousPowerCertificates
import CubicTenVariables.HomogeneousSpanCertificates
import CubicTenVariables.TotalDegreePowerSpan
import Mathlib.Data.Finsupp.Weight

/-! Coordinate-power identities imply certificates for every monomial in
one common degree. These finite homogeneous identities are the algebraic
input for a determinant certificate that persists in a parameter family.
No openness or specialization theorem is asserted in this module. -/

noncomputable section
namespace CubicTenVariables.HomogeneousMacaulayCertificates
open MvPolynomial
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ} {R : Type*} [CommRing R]

/-- One degree, strictly above the sum of the coordinate-power exponents. -/
def commonDegree (d : Fin n → ℕ) : ℕ := (∑ i, d i) + 1

theorem commonDegree_pos (d : Fin n → ℕ) : 0 < commonDegree d := Nat.succ_pos _

/-- A high-degree monomial has a factor among the given coordinate powers. -/
theorem monomial_mem_of_coordinate_powers
    (I : Ideal (MvPolynomial (Fin n) R)) (d : Fin n → ℕ)
    (hpow : ∀ i, X i ^ d i ∈ I) (s : Fin n →₀ ℕ)
    (hs : commonDegree d ≤ s.degree) (a : R) : monomial s a ∈ I := by
  classical
  have hi : ∃ i, d i ≤ s i := by
    by_contra h
    push_neg at h
    have hsum : (∑ i, s i) ≤ ∑ i, d i :=
      Finset.sum_le_sum (fun i _ => (h i).le)
    rw [← Finsupp.degree_eq_sum] at hsum
    simp only [commonDegree] at hs
    omega
  obtain ⟨i,hi⟩ := hi
  let s' := s - Finsupp.single i (d i)
  have hsplit : s' + Finsupp.single i (d i) = s :=
    tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hi)
  have hfactor : (monomial s a : MvPolynomial (Fin n) R) =
      monomial s' a * X i ^ d i := by
    rw [X_pow_eq_monomial, monomial_mul, mul_one, hsplit]
  rw [hfactor]
  exact I.mul_mem_left _ (hpow i)

/-- All homogeneous forms of sufficiently large degree lie in the ideal. -/
theorem homogeneous_mem_of_coordinate_powers
    (I : Ideal (MvPolynomial (Fin n) R)) (d : Fin n → ℕ)
    (hpow : ∀ i, X i ^ d i ∈ I) (N : ℕ) (hN : commonDegree d ≤ N)
    (P : MvPolynomial (Fin n) R) (hP : P.IsHomogeneous N) : P ∈ I := by
  classical
  rw [P.as_sum]
  apply I.sum_mem
  intro s hs
  have heq : s.degree = N := by
    by_contra hne
    exact (mem_support_iff.mp hs) (hP.coeff_eq_zero hne)
  exact monomial_mem_of_coordinate_powers I d hpow s (heq ▸ hN) _

/-- Monomials in a fixed degree form an actual finite index type. -/
def monomialIndices (n N : ℕ) := {s : Fin n →₀ ℕ // s.degree = N}

instance monomialIndices_finite (n N : ℕ) : Finite (monomialIndices n N) := by
  apply Set.finite_coe_iff.mpr
  exact (Finsupp.finite_of_degree_le N).subset (fun _ hs => hs.le)

/-- Each degree-N monomial has a literal homogeneous membership identity,
with coefficients of the correct degree and zero coefficients above N. -/
theorem common_degree_certificates {ι : Type*} [Fintype ι]
    (f : ι → MvPolynomial (Fin n) R) (e : ι → ℕ)
    (hhom : ∀ j, (f j).IsHomogeneous (e j)) (d : Fin n → ℕ)
    (hpow : ∀ i, X i ^ d i ∈ Ideal.span (Set.range f)) :
    ∃ c : monomialIndices n (commonDegree d) → ι → MvPolynomial (Fin n) R,
      (∀ s, monomial s.val 1 = ∑ j, c s j * f j) ∧
      (∀ s j, (c s j).IsHomogeneous (commonDegree d - e j)) ∧
      ∀ s j, commonDegree d < e j → c s j = 0 := by
  classical
  have h (s : monomialIndices n (commonDegree d)) :=
    HomogeneousSpanCertificates.exists_homogeneous_coefficients f e hhom
      (monomial s.val 1) (commonDegree d)
      (isHomogeneous_monomial 1 s.property)
      (monomial_mem_of_coordinate_powers _ d hpow s.val s.property.ge 1)
  choose c hc hh hz using h
  exact ⟨c,hc,hh,hz⟩

/-- Every finite-dimensional homogeneous quotient supplies the common-degree
certificates; positive coordinate powers are constructed, not assumed. -/
theorem exists_common_degree_certificates {K : Type*} [Field K]
    {ι : Type*} [Fintype ι] (f : ι → MvPolynomial (Fin n) K) (e : ι → ℕ)
    (hhom : ∀ j, (f j).IsHomogeneous (e j))
    [Module.Finite K (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range f))] :
    ∃ N : ℕ, 0 < N ∧
      ∃ c : monomialIndices n N → ι → MvPolynomial (Fin n) K,
        (∀ s, monomial s.val 1 = ∑ j, c s j * f j) ∧
        (∀ s j, (c s j).IsHomogeneous (N - e j)) ∧
        ∀ s j, N < e j → c s j = 0 := by
  classical
  let I := Ideal.span (Set.range f)
  have hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) K) := by
    apply Ideal.homogeneous_span
    rintro _ ⟨j,rfl⟩
    exact ⟨e j,hhom j⟩
  have h := HomogeneousPowerCertificates.exists_coordinate_power_mem I hI
  choose d hd hpow using h
  exact ⟨commonDegree d,commonDegree_pos d,
    common_degree_certificates f e hhom d hpow⟩

/-- Common-degree identities recover each actual coordinate power. -/
theorem coordinate_powers_mem_of_certificates {ι : Type*} [Fintype ι]
    (f : ι → MvPolynomial (Fin n) R) (N : ℕ)
    (c : monomialIndices n N → ι → MvPolynomial (Fin n) R)
    (hcert : ∀ s, monomial s.val 1 = ∑ j, c s j * f j) :
    ∀ i, X i ^ N ∈ Ideal.span (Set.range f) := by
  classical
  intro i
  let s : monomialIndices n N := ⟨Finsupp.single i N, Finsupp.degree_single i N⟩
  rw [X_pow_eq_monomial]
  change monomial s.val 1 ∈ Ideal.span (Set.range f)
  rw [hcert]
  exact Ideal.sum_mem _ (fun j _ =>
    Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j,rfl⟩))

/-- Over any coefficient ring, a positive common degree proves that the
literal equation quotient is a finite module. -/
theorem finite_quotient_of_certificates {ι : Type*} [Fintype ι]
    (f : ι → MvPolynomial (Fin n) R) (N : ℕ) (hN : 0 < N)
    (c : monomialIndices n N → ι → MvPolynomial (Fin n) R)
    (hcert : ∀ s, monomial s.val 1 = ∑ j, c s j * f j) :
    Module.Finite R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)) := by
  apply TotalDegreePowerSpan.finite_quotient _ (fun _ => N) (fun _ => 0)
  · simpa only [sub_zero] using coordinate_powers_mem_of_certificates f N c hcert
  · intro i
    simpa only [totalDegree_zero] using hN

/-- A field-valued common zero of the actual equations is the origin.
No homogeneity hypothesis is needed once the literal identities are given. -/
theorem zero_of_certificates {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    (f : ι → MvPolynomial (Fin n) K) (N : ℕ)
    (c : monomialIndices n N → ι → MvPolynomial (Fin n) K)
    (hcert : ∀ s, monomial s.val 1 = ∑ j, c s j * f j)
    (x : Fin n → K) (hx : ∀ j, eval x (f j) = 0) : x = 0 := by
  have hle : Ideal.span (Set.range f) ≤ RingHom.ker (eval x) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact hx j
  ext i
  have hz := hle (coordinate_powers_mem_of_certificates f N c hcert i)
  change eval x (X i ^ N) = 0 at hz
  simp only [map_pow, eval_X] at hz
  exact eq_zero_of_pow_eq_zero hz

end CubicTenVariables.HomogeneousMacaulayCertificates
