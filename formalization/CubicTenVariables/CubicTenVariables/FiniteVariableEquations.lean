import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-! Reindexing a fixed equation family preserves its actual solution
cardinality and quotient dimension. This transports Fin-indexed finite
normalization to the native paired-coordinate Hessian incidence. -/

noncomputable section
namespace CubicTenVariables.FiniteVariableEquations
open MvPolynomial

/-- Renaming every equation transports its generated ideal exactly. -/
theorem span_rename {σ τ ι R : Type*} [CommRing R]
    (e : σ ≃ τ) (f : ι → MvPolynomial σ R) :
    Ideal.span (Set.range fun i => rename e (f i)) =
      (Ideal.span (Set.range f)).map (renameEquiv R e).toRingHom := by
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

/-- A proper equation ideal stays proper after a bijection of variables. -/
theorem span_rename_ne_top {σ τ ι R : Type*} [CommRing R]
    (e : σ ≃ τ) (f : ι → MvPolynomial σ R)
    (hf : Ideal.span (Set.range f) ≠ ⊤) :
    Ideal.span (Set.range fun i => rename e (f i)) ≠ ⊤ := by
  rw [span_rename, RingEquiv.toRingHom_eq_coe,
    Ideal.map_comap_of_equiv (renameEquiv R e).toRingEquiv]
  exact fun h => hf (Ideal.comap_eq_top_iff.mp h)

/-- The actual quotient rings before and after renaming are isomorphic,
so their Krull dimensions are equal even for nonradical equation ideals. -/
theorem quotient_dimension_rename {σ τ ι R : Type*} [CommRing R]
    (e : σ ≃ τ) (f : ι → MvPolynomial σ R) :
    ringKrullDim (MvPolynomial τ R ⧸ Ideal.span (Set.range fun i => rename e (f i))) =
      ringKrullDim (MvPolynomial σ R ⧸ Ideal.span (Set.range f)) := by
  let E := Ideal.quotientEquiv
    (Ideal.span (Set.range f))
    (Ideal.span (Set.range fun i => rename e (f i)))
    (renameEquiv R e).toRingEquiv (span_rename e f)
  exact E.ringKrullDim.symm

/-- The literal common-zero sets are equivalent under the inverse
coordinate bijection. No finiteness or field assumption is required. -/
def zeroEquiv {σ τ ι R K : Type*} [CommRing R] [CommRing K]
    (e : σ ≃ τ) (f : ι → MvPolynomial σ R) (c : R →+* K) :
    {x : σ → K // ∀ i, eval₂ c x (f i) = 0} ≃
      {y : τ → K // ∀ i, eval₂ c y (rename e (f i)) = 0} where
  toFun x := ⟨fun j => x.1 (e.symm j), by
    intro i
    simpa only [eval₂_rename, Function.comp_def, e.symm_apply_apply] using x.2 i⟩
  invFun y := ⟨fun i => y.1 (e i), by
    intro j
    simpa only [eval₂_rename, Function.comp_def] using y.2 j⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact congrArg x.1 (e.symm_apply_apply i)
  right_inv y := by
    apply Subtype.ext
    funext j
    exact congrArg y.1 (e.apply_symm_apply j)

/-- Cardinality is preserved for the original equations, with the
coefficient map and every evaluated equation displayed. -/
theorem natCard_zeros_rename {σ τ ι R K : Type*} [CommRing R] [CommRing K]
    (e : σ ≃ τ) (f : ι → MvPolynomial σ R) (c : R →+* K) :
    Nat.card {x : σ → K // ∀ i, eval₂ c x (f i) = 0} =
      Nat.card {y : τ → K // ∀ i, eval₂ c y (rename e (f i)) = 0} :=
  Nat.card_congr (zeroEquiv e f c)

end CubicTenVariables.FiniteVariableEquations
