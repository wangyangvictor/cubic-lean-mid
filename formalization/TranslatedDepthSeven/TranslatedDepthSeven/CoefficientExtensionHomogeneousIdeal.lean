import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-!
# Homogeneous ideals under coefficient extension

Coefficientwise mapping carries a homogeneous multivariable-polynomial
ideal to a homogeneous ideal.  The proof uses an actual homogeneous
generating set, so it requires neither flatness nor a dimension theorem.
-/

namespace TranslatedDepthSeven

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Coefficientwise mapping preserves homogeneity of ideals in the standard
total-degree grading. -/
theorem isHomogeneous_map_mvPolynomialMap
    {K L σ : Type*} [Field K] [Field L]
    (f : K →+* L) (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ K)) :
    (I.map (MvPolynomial.map f)).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ L) := by
  rw [Ideal.IsHomogeneous.iff_exists] at hI ⊢
  obtain ⟨S, hS⟩ := hI
  let g : SetLike.homogeneousSubmonoid
        (MvPolynomial.homogeneousSubmodule σ K) →
      SetLike.homogeneousSubmonoid
        (MvPolynomial.homogeneousSubmodule σ L) := fun p ↦
    ⟨MvPolynomial.map f p.1, by
      obtain ⟨d, hd⟩ := p.2
      exact ⟨d, hd.map f⟩⟩
  refine ⟨g '' S, ?_⟩
  rw [hS, Ideal.map_span]
  apply congrArg Ideal.span
  ext p
  constructor
  · rintro ⟨q, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨g s, ⟨s, hs, rfl⟩, rfl⟩
  · rintro ⟨t, ⟨s, hs, hst⟩, rfl⟩
    subst t
    exact ⟨s.1, ⟨s, hs, rfl⟩, rfl⟩

end

end TranslatedDepthSeven
