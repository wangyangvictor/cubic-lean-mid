import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Etale.Basic

/-!
# Stability of the relative charts under scalar extension

Finite coefficient-field extensions do not change the algebraic shape of the
relative construction.  Monic triangular equations remain monic with the
same degree, while smoothness, standard smoothness with its relative
dimension, and etaleness are stable under base change.

These are direct applications of Mathlib's base-change theorems.  Integral
descent of a chosen nonvanishing denominator is a separate norm/conjugation
step.
-/

namespace TranslatedDepthSeven

noncomputable section

open Polynomial TensorProduct

universe u v w z

/-- Every equation in a monic triangular list remains monic, with unchanged
degree, after applying any coefficient homomorphism to a nontrivial target. -/
theorem monic_triangular_equations_stable_under_scalar_extension
    {R : Type u} {T : Type v} [CommRing R] [CommRing T] [Nontrivial T]
    {ι : Type w} (φ : R →+* T) (f : ι → R[X])
    (hmonic : ∀ i, (f i).Monic) :
    ∀ i, ((f i).map φ).Monic ∧
      ((f i).map φ).natDegree = (f i).natDegree := by
  intro i
  exact ⟨(hmonic i).map φ, (hmonic i).natDegree_map φ⟩

/-- Standard smoothness and its stated relative dimension survive arbitrary
scalar extension. -/
theorem standardSmooth_relativeDimension_stable_under_baseChange
    {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] {n : ℕ}
    [Algebra.IsStandardSmoothOfRelativeDimension n R S] :
    Algebra.IsStandardSmoothOfRelativeDimension n T (T ⊗[R] S) := by
  infer_instance

/-- Smoothness survives arbitrary scalar extension. -/
theorem smooth_stable_under_baseChange
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.Smooth R A] :
    Algebra.Smooth B (B ⊗[R] A) := by
  infer_instance

/-- Etaleness survives arbitrary scalar extension. -/
theorem etale_stable_under_baseChange
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.Etale R A] :
    Algebra.Etale B (B ⊗[R] A) := by
  infer_instance

end

end TranslatedDepthSeven
