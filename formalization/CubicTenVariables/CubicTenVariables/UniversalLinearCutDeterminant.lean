import CubicTenVariables.FiniteLinearCutCertificates
import CubicTenVariables.UniversalHomogeneousCombinations

/-! Universal homogeneous linear cuts. Small dimension of an actual specialized
homogeneous equation quotient is equivalent to nonvanishing of one square
universal determinant, with both the cut and combination coefficients chosen
inside the target infinite field. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.UniversalLinearCutDeterminant
open MvPolynomial HomogeneousMacaulayCertificates UniversalHomogeneousCombinations
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

variable {n t : ℕ} {ι : Type*} [Fintype ι]
local instance (n d : ℕ) : Fintype (monomialIndices n d) := Fintype.ofFinite _
local instance (n d : ℕ) : DecidableEq (monomialIndices n d) := Classical.decEq _

/-- Universal coefficients of `t` homogeneous linear forms. -/
abbrev CutVariable (n t : ℕ) := Fin t × monomialIndices n 1

def linearForm (R : Type*) [CommRing R] (j : Fin t) :
    MvPolynomial (Fin n) (MvPolynomial (CutVariable n t) R) :=
  ∑ u : monomialIndices n 1, monomial u.val (X (j,u))

theorem linearForm_homogeneous (R : Type*) [CommRing R] (j : Fin t) :
    (linearForm R j : MvPolynomial (Fin n) _).IsHomogeneous 1 := by
  classical
  exact (homogeneousSubmodule _ _ 1).sum_mem
    (fun u _ => isHomogeneous_monomial _ u.property)

/-- All literal linear cuts are evaluations of the universal ones. -/
theorem linearForm_realizes {R K : Type*} [CommRing R] [CommRing K]
    (ρ : R →+* K) (L : Fin t → MvPolynomial (Fin n) K)
    (hL : ∀ j, (L j).IsHomogeneous 1) :
    ∃ b : CutVariable n t → K,
      ∀ j, map (eval₂Hom ρ b) (linearForm R j) = L j := by
  classical
  refine ⟨fun v => coeff v.2.val (L v.1), ?_⟩
  intro j
  simpa [linearForm] using sum_monomial_coeff_of_homogeneous (L j) (hL j)

/-- The actual original equations together with universal linear cuts. -/
def cutEquations {R : Type*} [CommRing R]
    (f : ι → MvPolynomial (Fin n) R) (t : ℕ) :
    (ι ⊕ Fin t) → MvPolynomial (Fin n) (MvPolynomial (CutVariable n t) R) :=
  Sum.elim (fun j => map C (f j)) (linearForm R)

def cutDegrees (e : ι → ℕ) (t : ℕ) : (ι ⊕ Fin t) → ℕ :=
  Sum.elim e (fun _ => 1)

omit [Fintype ι] in
theorem cutEquations_homogeneous {R : Type*} [CommRing R]
    (f : ι → MvPolynomial (Fin n) R) (e : ι → ℕ)
    (hf : ∀ j, (f j).IsHomogeneous (e j)) :
    ∀ j, (cutEquations f t j).IsHomogeneous (cutDegrees e t j) := by
  intro j
  cases j with
  | inl j => exact (hf j).map C
  | inr j => exact linearForm_homogeneous R j

omit [Fintype ι] in
/-- Specialization retains the literal original equation ideal and cuts. -/
theorem span_cutEquations_map {R K : Type*} [CommRing R] [CommRing K]
    (ρ : R →+* K) (f : ι → MvPolynomial (Fin n) R)
    (b : CutVariable n t → K) :
    Ideal.span (Set.range (fun j => map (eval₂Hom ρ b) (cutEquations f t j))) =
      Ideal.span (Set.range (fun j => map ρ (f j))) ⊔
        Ideal.span (Set.range (fun j => map (eval₂Hom ρ b) (linearForm R j))) := by
  have hcomp : (eval₂Hom ρ b).comp (C : R →+* MvPolynomial (CutVariable n t) R) = ρ := by
    ext r
    simp
  have heq : (fun j => map (eval₂Hom ρ b) (cutEquations f t j)) =
      Sum.elim (fun j => map ρ (f j))
        (fun j => map (eval₂Hom ρ b) (linearForm R j)) := by
    funext j
    cases j with
    | inl j => simp [cutEquations, map_map, hcomp]
    | inr j => rfl
  rw [heq, Set.Sum.elim_range, Ideal.span_union]

/-- The determinant has combination variables outside cut variables; its
iterated coefficients therefore lie in the original coefficient ring. -/
def cutDeterminant {R : Type*} [CommRing R]
    (f : ι → MvPolynomial (Fin n) R) (e : ι → ℕ) (t N : ℕ) :
    MvPolynomial (CoefficientVariable n N (cutDegrees e t))
      (MvPolynomial (CutVariable n t) R) :=
  determinant (cutEquations f t) (cutDegrees e t) N

/-- Nonzero determinant implies the original fiber quotient has dimension
at most the number of universal cuts. This direction works over every field. -/
theorem dimension_le_of_determinant_ne_zero {R K : Type*} [CommRing R] [Field K]
    (ρ : R →+* K) (f : ι → MvPolynomial (Fin n) R) (e : ι → ℕ)
    (hf : ∀ j, (f j).IsHomogeneous (e j)) {N : ℕ} (hN : 0 < N)
    (b : CutVariable n t → K)
    (a : CoefficientVariable n N (cutDegrees e t) → K)
    (hdet : eval₂Hom (eval₂Hom ρ b) a (cutDeterminant f e t N) ≠ 0) :
    ringKrullDim (MvPolynomial (Fin n) K ⧸
      Ideal.span (Set.range (fun j => map ρ (f j)))) ≤ (t : WithBot ℕ∞) := by
  have hfinite := finite_quotient_of_determinant_ne_zero (eval₂Hom ρ b)
    (cutEquations f t) (cutDegrees e t) (cutEquations_homogeneous f e hf) hN a hdet
  rw [span_cutEquations_map] at hfinite
  letI := hfinite
  exact FiniteLinearCutCertificates.equation_dimension_le_of_finite_linear_cuts
    (fun j => map ρ (f j)) e (fun j => (hf j).map ρ)
    (fun j => map (eval₂Hom ρ b) (linearForm R j))
    (fun j => (linearForm_homogeneous R j).map (eval₂Hom ρ b))

/-- A small homogeneous fiber supplies actual cut and combination coefficients
for which a positive-degree universal determinant evaluates to one. -/
theorem exists_determinant_eq_one_of_dimension_le
    {R K : Type*} [CommRing R] [Field K] [Infinite K]
    (ρ : R →+* K) (f : ι → MvPolynomial (Fin n) R) (e : ι → ℕ)
    (hf : ∀ j, (f j).IsHomogeneous (e j))
    (hdim : ringKrullDim (MvPolynomial (Fin n) K ⧸
      Ideal.span (Set.range (fun j => map ρ (f j)))) ≤ (t : WithBot ℕ∞)) :
    ∃ N : ℕ, 0 < N ∧ ∃ b : CutVariable n t → K,
      ∃ a : CoefficientVariable n N (cutDegrees e t) → K,
        eval₂Hom (eval₂Hom ρ b) a (cutDeterminant f e t N) = 1 := by
  have hI : (Ideal.span (Set.range (fun j => map ρ (f j)))).IsHomogeneous
      (homogeneousSubmodule (Fin n) K) := by
    apply Ideal.homogeneous_span
    rintro _ ⟨j, rfl⟩
    exact ⟨e j, (hf j).map ρ⟩
  obtain ⟨L, hL, hfinite⟩ := FiniteLinearCutCertificates.exists_finite_linear_cuts _ hI hdim
  obtain ⟨b, hb⟩ := linearForm_realizes ρ L hL
  have hfin : Module.Finite K (MvPolynomial (Fin n) K ⧸
      Ideal.span (Set.range (fun j => map (eval₂Hom ρ b) (cutEquations f t j)))) := by
    rw [span_cutEquations_map]
    have hlin : (fun j : Fin t => map (eval₂Hom ρ b) (linearForm R j)) = L := funext hb
    rw [hlin]
    exact hfinite
  letI := hfin
  obtain ⟨N, hN, a, ha⟩ := exists_determinant_of_finite_quotient (eval₂Hom ρ b)
    (cutEquations f t) (cutDegrees e t) (cutEquations_homogeneous f e hf)
  exact ⟨N, hN, b, a, ha⟩

/-- Exact uniform determinant criterion for the dimension of the actual
specialized equation quotient. No genericity or reducedness is required. -/
theorem dimension_le_iff_exists_determinant
    {R K : Type*} [CommRing R] [Field K] [Infinite K]
    (ρ : R →+* K) (f : ι → MvPolynomial (Fin n) R) (e : ι → ℕ)
    (hf : ∀ j, (f j).IsHomogeneous (e j)) :
    ringKrullDim (MvPolynomial (Fin n) K ⧸
      Ideal.span (Set.range (fun j => map ρ (f j)))) ≤ (t : WithBot ℕ∞) ↔
      ∃ N : ℕ, 0 < N ∧ ∃ b : CutVariable n t → K,
        ∃ a : CoefficientVariable n N (cutDegrees e t) → K,
          eval₂Hom (eval₂Hom ρ b) a (cutDeterminant f e t N) ≠ 0 := by
  constructor
  · intro hdim
    obtain ⟨N, hN, b, a, ha⟩ := exists_determinant_eq_one_of_dimension_le ρ f e hf hdim
    exact ⟨N, hN, b, a, ha.trans_ne one_ne_zero⟩
  · rintro ⟨N, hN, b, a, ha⟩
    exact dimension_le_of_determinant_ne_zero ρ f e hf hN b a ha

end CubicTenVariables.UniversalLinearCutDeterminant
