import TranslatedDepthSeven.HomogeneousLinearElimination
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# Adding one linear primitive coordinate to a finite normalization

The projective fourfold projection used in the proper-piece argument starts
with five homogeneous linear normalization coordinates and appends one more
linear coordinate which is primitive on the generic function field.  This
file proves the ring-theoretic part of that construction: appending an
arbitrary coordinate to a finite normalization still gives a finite map.

No projective degree, generic-projection, or fibre estimate is assumed.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

universe u v

/-- The coordinate list obtained by putting one additional coordinate in
front of the displayed normalization coordinates. -/
def augmentedLinearNormalizationCoordinate
    {K : Type u} [Field K] {tau : Type v}
    {I : Ideal (MvPolynomial tau K)}
    (D : HomogeneousLinearNormalizationData I)
    (u : MvPolynomial tau K ⧸ I) :
    Fin (D.parameterCount + 1) → MvPolynomial tau K ⧸ I :=
  Fin.cases u (fun i => D.hom (X i))

/-- The polynomial-algebra map defined by the augmented coordinate list. -/
def augmentedLinearNormalizationHom
    {K : Type u} [Field K] {tau : Type v}
    {I : Ideal (MvPolynomial tau K)}
    (D : HomogeneousLinearNormalizationData I)
    (u : MvPolynomial tau K ⧸ I) :
    MvPolynomial (Fin (D.parameterCount + 1)) K →ₐ[K]
      (MvPolynomial tau K ⧸ I) :=
  MvPolynomial.aeval (augmentedLinearNormalizationCoordinate D u)

@[simp]
theorem augmentedLinearNormalizationHom_X_zero
    {K : Type u} [Field K] {tau : Type v}
    {I : Ideal (MvPolynomial tau K)}
    (D : HomogeneousLinearNormalizationData I)
    (u : MvPolynomial tau K ⧸ I) :
    augmentedLinearNormalizationHom D u (X 0) = u := by
  simp [augmentedLinearNormalizationHom,
    augmentedLinearNormalizationCoordinate]

@[simp]
theorem augmentedLinearNormalizationHom_X_succ
    {K : Type u} [Field K] {tau : Type v}
    {I : Ideal (MvPolynomial tau K)}
    (D : HomogeneousLinearNormalizationData I)
    (u : MvPolynomial tau K ⧸ I)
    (i : Fin D.parameterCount) :
    augmentedLinearNormalizationHom D u (X i.succ) = D.hom (X i) := by
  simp [augmentedLinearNormalizationHom,
    augmentedLinearNormalizationCoordinate]

/-- Inclusion of the old normalization variables as the final variables of
the augmented polynomial algebra. -/
def mvPolynomialSuccInclusion (K : Type u) [CommSemiring K] (n : ℕ) :
    MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin (n + 1)) K :=
  MvPolynomial.rename (fun i => i.succ)

@[simp]
theorem mvPolynomialSuccInclusion_X
    (K : Type u) [CommSemiring K] (n : ℕ) (i : Fin n) :
    mvPolynomialSuccInclusion K n (X i) = X i.succ := by
  simp [mvPolynomialSuccInclusion]

/-- The original normalization map factors through the augmented map. -/
theorem augmentedLinearNormalizationHom_comp_succInclusion
    {K : Type u} [Field K] {tau : Type v}
    {I : Ideal (MvPolynomial tau K)}
    (D : HomogeneousLinearNormalizationData I)
    (u : MvPolynomial tau K ⧸ I) :
    (augmentedLinearNormalizationHom D u).comp
        (mvPolynomialSuccInclusion K D.parameterCount) = D.hom := by
  apply MvPolynomial.algHom_ext
  intro i
  simp

/-- Appending one arbitrary coordinate to a finite linear normalization
preserves finiteness.  This is the exact finite-map step in the
normalization-plus-primitive-element construction. -/
theorem augmentedLinearNormalizationHom_finite
    {K : Type u} [Field K] {tau : Type v}
    {I : Ideal (MvPolynomial tau K)}
    (D : HomogeneousLinearNormalizationData I)
    (u : MvPolynomial tau K ⧸ I) :
    (augmentedLinearNormalizationHom D u).Finite := by
  exact AlgHom.Finite.of_comp_finite (R := K)
    (by
      rw [augmentedLinearNormalizationHom_comp_succInclusion]
      exact D.hom_finite)

end

end TranslatedDepthSeven
