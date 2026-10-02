import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Ideal.Operations

/-!
# Homogeneous certificates for membership in a finitely generated ideal

Projecting an actual ideal-membership expression onto the degree of its
homogeneous target gives coefficients of exactly the required degree.
Generators of larger degree have zero coefficients. These are identities
in the polynomial ring itself; neither reducedness nor a field is needed.
-/

noncomputable section
namespace CubicTenVariables.HomogeneousSpanCertificates
open MvPolynomial

universe u v w
variable {R : Type u} [CommRing R] {σ : Type v} {ι : Type w}

local instance : GradedAlgebra (MvPolynomial.homogeneousSubmodule σ R) :=
  MvPolynomial.gradedAlgebra

/-- The degree-`e` component of a product with a homogeneous right factor. -/
theorem homogeneousComponent_mul_right (g f : MvPolynomial σ R) {d : ℕ}
    (hf : f.IsHomogeneous d) (e : ℕ) :
    homogeneousComponent e (g * f) =
      if d ≤ e then homogeneousComponent (e - d) g * f else 0 := by
  have h := DirectSum.coe_decompose_mul_of_right_mem
    (MvPolynomial.homogeneousSubmodule σ R) (a := g) e hf
  change (MvPolynomial.decomposition.decompose' (g * f) e : MvPolynomial σ R) =
    if d ≤ e then
      (MvPolynomial.decomposition.decompose' g (e - d) : MvPolynomial σ R) * f
    else 0 at h
  simpa only [MvPolynomial.decomposition.decompose'_apply] using h

/-- Homogeneous ideal membership has homogeneous coefficients with the
exact degree difference; coefficients of generators above the target
degree vanish, including when subtraction in `ℕ` would otherwise truncate. -/
theorem exists_homogeneous_coefficients [Fintype ι]
    (f : ι → MvPolynomial σ R) (d : ι → ℕ)
    (hf : ∀ i, (f i).IsHomogeneous (d i))
    (p : MvPolynomial σ R) (e : ℕ) (hp : p.IsHomogeneous e)
    (hmem : p ∈ Ideal.span (Set.range f)) :
    ∃ c : ι → MvPolynomial σ R,
      p = ∑ i, c i * f i ∧
      (∀ i, (c i).IsHomogeneous (e - d i)) ∧
      ∀ i, e < d i → c i = 0 := by
  classical
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  let c : ι → MvPolynomial σ R := fun i ↦
    if d i ≤ e then homogeneousComponent (e - d i) (a i) else 0
  refine ⟨c, ?_, ?_, ?_⟩
  · have heq := congrArg (homogeneousComponent e) ha
    rw [map_sum, homogeneousComponent_of_mem hp, if_pos rfl] at heq
    rw [← heq]
    apply Finset.sum_congr rfl
    intro i hi
    rw [homogeneousComponent_mul_right (a i) (f i) (hf i) e]
    simp only [c, ite_mul, zero_mul]
  · intro i
    by_cases h : d i ≤ e
    · simpa only [c, if_pos h] using
        homogeneousComponent_isHomogeneous (e - d i) (a i)
    · simp only [c, if_neg h]
      exact isHomogeneous_zero σ R (e - d i)
  · intro i hi
    simp only [c, if_neg (Nat.not_le.mpr hi)]

/-- Simultaneous homogeneous membership certificates for coordinate
powers, with no finiteness assumption on the coordinate type. -/
theorem exists_coordinate_power_coefficients [Fintype ι]
    (f : ι → MvPolynomial σ R) (d : ι → ℕ)
    (hf : ∀ j, (f j).IsHomogeneous (d j)) (E : σ → ℕ)
    (hmem : ∀ i, X i ^ E i ∈ Ideal.span (Set.range f)) :
    ∃ c : σ → ι → MvPolynomial σ R,
      (∀ i, X i ^ E i = ∑ j, c i j * f j) ∧
      (∀ i j, (c i j).IsHomogeneous (E i - d j)) ∧
      ∀ i j, E i < d j → c i j = 0 := by
  classical
  have h := fun i ↦ exists_homogeneous_coefficients f d hf
    (X i ^ E i) (E i) (isHomogeneous_X_pow i (E i)) (hmem i)
  choose c hc hhom hzero using h
  exact ⟨c, hc, hhom, hzero⟩

end CubicTenVariables.HomogeneousSpanCertificates
