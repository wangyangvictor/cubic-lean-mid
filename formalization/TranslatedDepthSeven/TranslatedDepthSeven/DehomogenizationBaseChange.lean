import TranslatedDepthSeven.MultivariateHomogenization
import Mathlib.RingTheory.Ideal.Maps

/-!
# Dehomogenization commutes with coefficient extension

Setting the distinguished homogeneous coordinate equal to one commutes
exactly with every coefficient homomorphism.  Consequently coefficient
extension and affine-chart dehomogenization commute on ideals.

These are literal ring-homomorphism and ideal equalities.  They provide the
base-change square needed to identify an affine chart in a reduced
projective model without introducing a separate fibre object.
-/

namespace TranslatedDepthSeven

noncomputable section

universe u v w

/-- Coefficient extension commutes with the distinguished affine-chart
dehomogenization. -/
theorem multivariateDehomogenization_comp_map
    {S : Type u} {T : Type v} {σ : Type w}
    [CommRing S] [CommRing T] (φ : S →+* T) :
    (multivariateDehomogenization (R := T) (σ := σ)).toRingHom.comp
        (MvPolynomial.map φ :
          MvPolynomial (Option σ) S →+* MvPolynomial (Option σ) T) =
      (MvPolynomial.map φ : MvPolynomial σ S →+* MvPolynomial σ T).comp
        (multivariateDehomogenization (R := S) (σ := σ)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro s
    simp [multivariateDehomogenization]
  · intro j
    cases j with
    | none => simp [multivariateDehomogenization]
    | some i => simp [multivariateDehomogenization]

/-- Ideal-theoretic form: first extending coefficients and then taking the
affine chart is the same as first taking the affine chart and then extending
coefficients. -/
theorem map_dehomogenization_map_eq_map_map_dehomogenization
    {S : Type u} {T : Type v} {σ : Type w}
    [CommRing S] [CommRing T] (φ : S →+* T)
    (I : Ideal (MvPolynomial (Option σ) S)) :
    Ideal.map
        (multivariateDehomogenization (R := T) (σ := σ)).toRingHom
        (Ideal.map (MvPolynomial.map φ) I) =
      Ideal.map (MvPolynomial.map φ)
        (Ideal.map
          (multivariateDehomogenization (R := S) (σ := σ)).toRingHom I) := by
  rw [Ideal.map_map, Ideal.map_map,
    multivariateDehomogenization_comp_map]

end

end TranslatedDepthSeven
