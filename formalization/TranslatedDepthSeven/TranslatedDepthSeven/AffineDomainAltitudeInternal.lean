import TranslatedDepthSeven.ParameterLocalizationAltitude

/-!
# The altitude formula for affine domains

Normalize the prime quotient, lift its polynomial parameters to the source,
and invert the nonzero parameters.  The localized prime is maximal, with
unchanged height.  Its height is the dimension of the localized affine
domain over the parameter fraction field.  Transcendence-degree addition
therefore proves the prime altitude formula; no catenarity or dimension
formula is assumed.
-/

namespace TranslatedDepthSeven

noncomputable section

universe u

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

/-- The height and quotient dimension of every prime in an affine domain
are finite natural numbers whose sum is the dimension of the source. -/
theorem affineDomain_prime_height_add_quotient_dimension
    (K A : Type u) [Field K] [CharZero K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A]
    (P : Ideal A) [P.IsPrime] :
    ∃ h r a : ℕ, P.height = (h : ℕ∞) ∧
      ringKrullDim (A ⧸ P) = (r : WithBot ℕ∞) ∧
      ringKrullDim A = (a : WithBot ℕ∞) ∧ h + r = a := by
  classical
  obtain ⟨a, hAdim, hAtrdeg⟩ := affineDomain_exists_dimension_trdeg K A
  obtain ⟨r, g, hginj, hgint⟩ := exists_integral_inj_algHom_of_fg K (A ⧸ P)
  have hquotDim : ringKrullDim (A ⧸ P) = (r : WithBot ℕ∞) := by
    letI : Algebra (MvPolynomial (Fin r) K) (A ⧸ P) := g.toRingHom.toAlgebra
    letI : Algebra.IsIntegral (MvPolynomial (Fin r) K) (A ⧸ P) := ⟨hgint⟩
    exact (ringKrullDim_eq_of_isIntegral_injective hginj).trans
      (ringKrullDim_mvPolynomial_fin_eq_of_field K r)
  choose x hx using fun i : Fin r ↦
    Ideal.Quotient.mk_surjective (g (MvPolynomial.X i))
  let B := MvPolynomial (Fin r) K
  let f : B →ₐ[K] A := MvPolynomial.aeval x
  have hcomp : (Ideal.Quotient.mkₐ K P).comp f = g := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa only [AlgHom.comp_apply, f, MvPolynomial.aeval_X] using hx i
  letI : Algebra B A := f.toRingHom.toAlgebra
  letI : IsScalarTower K B A :=
    IsScalarTower.of_algebraMap_eq fun z ↦ by
      simp [RingHom.algebraMap_toAlgebra]
  have hmap : algebraMap B (A ⧸ P) = g.toRingHom := by
    apply RingHom.ext
    intro b
    exact AlgHom.congr_fun hcomp b
  letI : Algebra.IsIntegral B (A ⧸ P) := by
    constructor
    change (algebraMap B (A ⧸ P)).IsIntegral
    rw [hmap]
    exact hgint
  have hPzero : P.comap (algebraMap B A) = ⊥ := by
    apply le_antisymm _ bot_le
    intro b hb
    change b = 0
    apply hginj
    rw [map_zero]
    have hzero : algebraMap B (A ⧸ P) b = 0 := by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hb
    simpa only [hmap] using hzero
  letI : Algebra.FiniteType B A :=
    Algebra.FiniteType.of_restrictScalars_finiteType K B A
  have hBtrdeg : Algebra.trdeg K B = (r : Cardinal) := by
    simp [B, Cardinal.mk_fin]
  obtain ⟨h, hheight, hsum⟩ :=
    prime_height_add_parameter_trdeg_eq K B A P hPzero hBtrdeg hAtrdeg
  exact ⟨h, r, a, hheight, hquotDim, hAdim, by omega⟩

/-- The usual altitude formula, with Krull dimensions in mathlib's
extended natural-number convention. -/
theorem affineDomain_height_add_quotient_ringKrullDim
    (K A : Type u) [Field K] [CharZero K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A]
    (P : Ideal A) [P.IsPrime] :
    (P.height : WithBot ℕ∞) + ringKrullDim (A ⧸ P) = ringKrullDim A := by
  obtain ⟨h, r, a, hheight, hquotDim, hAdim, hsum⟩ :=
    affineDomain_prime_height_add_quotient_dimension K A P
  rw [hheight, hquotDim, hAdim, ← hsum]
  norm_cast

end
end TranslatedDepthSeven
