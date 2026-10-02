import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.RingTheory.Trace.Basic

/-!
# An explicit finite Galois subspace descent formula
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped BigOperators

universe u v w

variable {K : Type u} {L : Type v} {ι : Type w}
  [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

local instance : DecidableEq (L ≃ₐ[K] L) := Classical.decEq _

/-- The rational coefficient vectors of `w`, computed using the trace-dual
of the normal basis. -/
def galoisDescentCoefficient
    (w : ι → L) (σ : L ≃ₐ[K] L) : ι → K := by
  classical
  exact fun i ↦ Algebra.trace K L
    (w i * (IsGalois.normalBasis K L).traceDual σ)

/-- The trace-dual coefficient vector is an `L`-linear combination of the
Galois conjugates of `w`. -/
theorem algebraMap_galoisDescentCoefficient_eq_sum_conjugates
    (w : ι → L) (σ : L ≃ₐ[K] L) :
    (fun i ↦ algebraMap K L (galoisDescentCoefficient w σ i)) =
      ∑ τ : L ≃ₐ[K] L,
        τ ((IsGalois.normalBasis K L).traceDual σ) •
          (fun i ↦ τ (w i)) := by
  classical
  funext i
  rw [galoisDescentCoefficient, trace_eq_sum_automorphisms]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro τ _
  rw [map_mul, mul_comm]

/-- Every trace-dual coefficient vector belongs to a Galois-stable
`L`-subspace containing `w`. -/
theorem algebraMap_galoisDescentCoefficient_mem
    (W : Submodule L (ι → L)) (w : ι → L) (hw : w ∈ W)
    (hstable : ∀ (τ : L ≃ₐ[K] L) {v : ι → L}, v ∈ W →
      (fun i ↦ τ (v i)) ∈ W)
    (σ : L ≃ₐ[K] L) :
    (fun i ↦ algebraMap K L (galoisDescentCoefficient w σ i)) ∈ W := by
  classical
  rw [algebraMap_galoisDescentCoefficient_eq_sum_conjugates]
  apply Submodule.sum_mem
  intro τ _
  exact W.smul_mem _ (hstable τ hw)

/-- Explicit reconstruction from the rational trace-dual coefficient
vectors.  Together with the preceding membership theorem this is finite
Galois descent for a stable subspace of `L^ι`. -/
theorem sum_normalBasis_smul_galoisDescentCoefficient
    (w : ι → L) :
    ∑ σ : L ≃ₐ[K] L,
        (IsGalois.normalBasis K L σ) •
          (fun i ↦ algebraMap K L (galoisDescentCoefficient w σ i)) = w := by
  classical
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    galoisDescentCoefficient]
  have hrepr (σ : L ≃ₐ[K] L) :
      (IsGalois.normalBasis K L).repr (w i) σ =
        Algebra.trace K L
          (w i * (IsGalois.normalBasis K L).traceDual σ) := by
    simpa [Algebra.traceForm_apply] using
      (Module.Basis.traceDual_repr_apply
        (b := (IsGalois.normalBasis K L).traceDual) (w i) σ)
  simpa only [hrepr, Algebra.smul_def, mul_comm] using
    (IsGalois.normalBasis K L).sum_repr (w i)

/-- Static finite-Galois descent statement: every vector of a stable
subspace is an `L`-linear combination of vectors in that subspace whose
coordinates come from the base field. -/
theorem exists_baseFieldVectors_spanning_of_galoisStable
    (W : Submodule L (ι → L)) (w : ι → L) (hw : w ∈ W)
    (hstable : ∀ (τ : L ≃ₐ[K] L) {v : ι → L}, v ∈ W →
      (fun i ↦ τ (v i)) ∈ W) :
    ∃ q : (L ≃ₐ[K] L) → ι → K,
      (∀ σ, (fun i ↦ algebraMap K L (q σ i)) ∈ W) ∧
      (∑ σ : L ≃ₐ[K] L,
        (IsGalois.normalBasis K L σ) •
          (fun i ↦ algebraMap K L (q σ i))) = w := by
  classical
  refine ⟨galoisDescentCoefficient w, ?_, ?_⟩
  · intro σ
    exact algebraMap_galoisDescentCoefficient_mem W w hw hstable σ
  · exact sum_normalBasis_smul_galoisDescentCoefficient w

end

end TranslatedDepthSeven
