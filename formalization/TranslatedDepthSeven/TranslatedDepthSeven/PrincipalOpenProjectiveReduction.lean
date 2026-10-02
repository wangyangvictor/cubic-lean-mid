import TranslatedDepthSeven.DehomogenizationBaseChange
import TranslatedDepthSeven.PrincipalOpenReduction

/-!
# The affine chart of a reduced principal-open projective model

For a homogeneous integral ideal, three operations are relevant:

1. extend coefficients to `ℤ[1/Δ]`;
2. reduce modulo a prime `p ∤ Δ`; and
3. set the distinguished homogeneous coordinate equal to one.

Their composite is exactly direct dehomogenization over `ℤ` followed by
coefficientwise reduction modulo `p`.  The theorem below is a literal ideal
equality and hence identifies the affine special-fibre equations required by
the smooth-point specialization of Salberger's result.
-/

namespace TranslatedDepthSeven

noncomputable section

universe u

/-- The dehomogenized mod-`p` fibre of a principal-open integral projective
model is the direct mod-`p` reduction of the integral affine chart. -/
theorem dehomogenized_principalOpen_specialFibreIdeal_eq
    {σ : Type u}
    (Δ : ℤ) (p : ℕ) (hp : p.Prime) (hpΔ : ¬ p ∣ Δ.natAbs)
    (I : Ideal (MvPolynomial (Option σ) ℤ)) :
    Ideal.map
        (multivariateDehomogenization
          (R := ZMod p) (σ := σ)).toRingHom
        (Ideal.map (MvPolynomial.map (awayIntToZMod Δ p hp hpΔ))
          (Ideal.map
            (MvPolynomial.map (algebraMap ℤ (Localization.Away Δ))) I)) =
      Ideal.map (MvPolynomial.map (Int.castRingHom (ZMod p)))
        (Ideal.map
          (multivariateDehomogenization
            (R := ℤ) (σ := σ)).toRingHom I) := by
  rw [map_localized_mvPolynomialIdeal_to_ZMod]
  exact
    map_dehomogenization_map_eq_map_map_dehomogenization
      (Int.castRingHom (ZMod p)) I

end

end TranslatedDepthSeven
