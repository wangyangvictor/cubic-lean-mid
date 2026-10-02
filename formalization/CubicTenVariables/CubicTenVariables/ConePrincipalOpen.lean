import TranslatedDepthSeven.HomogeneousIrrelevantDimensionFieldInternal
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-! Elementary principal-open bookkeeping for an integral affine cone.
The exceptional locus is the actual closed subscheme cut out by adjoining
one equation. It may be empty: `g ∉ I` does not imply `I + (g) ≠ ⊤`.
No homogeneity, geometric integrality, or literature input is needed for
the dimension drop once the defining ideal is prime. -/

set_option autoImplicit false
noncomputable section

namespace CubicTenVariables.ConePrincipalOpen

open MvPolynomial
open scoped nonZeroDivisors

variable {R : Type*} [CommRing R]

/-- The actual ideal of the closed residual locus of the principal open. -/
def residualIdeal (I : Ideal R) (g : R) : Ideal R := I ⊔ Ideal.span {g}

theorem mem_residualIdeal (I : Ideal R) (g : R) : g ∈ residualIdeal I g :=
  Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton g))

theorem lt_residualIdeal (I : Ideal R) (g : R) (hg : g ∉ I) :
    I < residualIdeal I g := by
  refine lt_of_le_of_ne le_sup_left ?_
  intro heq
  exact hg (heq ▸ mem_residualIdeal I g)

/-- Properness is as a closed subset of `V(I)`, not nonemptiness of that
subset or properness of its defining ideal. -/
theorem residual_zeroLocus_ssubset (I : Ideal R) (hI : I.IsPrime)
    (g : R) (hg : g ∉ I) :
    PrimeSpectrum.zeroLocus (residualIdeal I g : Set R) ⊂
      PrimeSpectrum.zeroLocus (I : Set R) := by
  refine ⟨PrimeSpectrum.zeroLocus_anti_mono_ideal le_sup_left, ?_⟩
  intro h
  have hpoint : (⟨I, hI⟩ : PrimeSpectrum R) ∈
      PrimeSpectrum.zeroLocus (I : Set R) := fun _ hx => hx
  exact hg ((h hpoint) (mem_residualIdeal I g))

/-- A nonzero equation on an integral affine scheme lowers dimension by
at least one; the statement also includes the empty residual scheme. -/
theorem residual_dimension_succ_le (I : Ideal R) (hI : I.IsPrime)
    (g : R) (hg : g ∉ I) :
    ringKrullDim (R ⧸ residualIdeal I g) + 1 ≤ ringKrullDim (R ⧸ I) := by
  letI : I.IsPrime := hI
  apply ringKrullDim_succ_le_of_surjective
    (Ideal.Quotient.factor (show I ≤ residualIdeal I g from le_sup_left))
    (Ideal.Quotient.factor_surjective _) (r := Ideal.Quotient.mk I g)
  · exact mem_nonZeroDivisors_of_ne_zero
      (fun h => hg (Ideal.Quotient.eq_zero_iff_mem.mp h))
  · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact mem_residualIdeal I g

theorem residual_dimension_le (I : Ideal R) (hI : I.IsPrime)
    (g : R) (hg : g ∉ I) (r : ℕ)
    (hdim : ringKrullDim (R ⧸ I) = (r : WithBot ℕ∞) + 1) :
    ringKrullDim (R ⧸ residualIdeal I g) ≤ (r : WithBot ℕ∞) := by
  have h := residual_dimension_succ_le I hI g hg
  rw [hdim] at h
  generalize ringKrullDim (R ⧸ residualIdeal I g) = a at h ⊢
  cases a with
  | bot => exact bot_le
  | coe a =>
    have h' : (a + 1 : ℕ∞) ≤ (r : ℕ∞) + 1 := by exact_mod_cast h
    exact_mod_cast (ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp h'

/-- A positive-dimensional affine prime cone has a coordinate which is
nonzero in its coordinate ring. The stronger cone hypotheses used in the
application are unnecessary for this elementary consequence. -/
theorem exists_coordinate_not_mem {K : Type*} [Field K] (N r : ℕ)
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) (hI : I.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin (N + 1)) K ⧸ I) =
      (r : WithBot ℕ∞) + 1) :
    ∃ i : Fin (N + 1), X i ∉ I := by
  classical
  by_contra h
  push_neg at h
  have hirr : TranslatedDepthSeven.Published.projectiveIrrelevantIdeal K N ≤ I := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact h i
  have hz := TranslatedDepthSeven.ringKrullDim_quotient_eq_zero_of_irrelevant_le_over_field
    N I hI hirr
  rw [hz] at hdim
  have hp : (0 : WithBot ℕ∞) < (r : WithBot ℕ∞) + 1 := by
    exact_mod_cast Nat.succ_pos r
  exact (ne_of_gt hp) hdim.symm

end CubicTenVariables.ConePrincipalOpen
