import TranslatedDepthSeven.AffineDomainAltitudeInternal
import TranslatedDepthSeven.LinearSectionRelativeHeightInternal

/-!
# Lower dimensions of minimal components after adjoining equations

Krull's height theorem in the source coordinate ring and the internally
proved affine altitude formula give the dimension inequality for every
minimal component.  Zero and dependent equations are allowed.  The
quotient by a component is identified with the corresponding double
quotient by the third isomorphism theorem.
-/

namespace TranslatedDepthSeven

noncomputable section

universe u

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

/-- Adjoining a finite equation family to an affine prime source decreases
the dimension of each minimal component by at most the number of equations. -/
theorem finiteEquation_minimalComponent_dimension_lower
    (K R : Type u) [Field K] [CharZero K] [CommRing R]
    [Algebra K R] [Algebra.FiniteType K R]
    (I P : Ideal R) [I.IsPrime] (family : Finset R)
    (hP : P ∈ (I ⊔ Ideal.span (family : Set R)).minimalPrimes)
    {n : ℕ} (hIdim : ringKrullDim (R ⧸ I) = (n : WithBot ℕ∞)) :
    ∃ r : ℕ, ringKrullDim (R ⧸ P) = (r : WithBot ℕ∞) ∧
      n ≤ r + family.card := by
  classical
  letI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing K R
  letI : P.IsPrime := hP.1.1
  have hIP : I ≤ P := le_trans le_sup_left hP.1.2
  let Q := P.map (Ideal.Quotient.mk I)
  letI : Q.IsPrime := Ideal.map_isPrime_of_surjective
    (Ideal.Quotient.mk_surjective (I := I)) (by simpa using hIP)
  obtain ⟨h, r, a, hheight, hQdim, hAdim, hsum⟩ :=
    affineDomain_prime_height_add_quotient_dimension K (R ⧸ I) Q
  have han : a = n := by exact_mod_cast hAdim.symm.trans hIdim
  have hhle : h ≤ family.card := by
    have hh := quotient_component_height_le_equation_count I P family hP
    change Q.height ≤ _ at hh
    rw [hheight] at hh
    exact_mod_cast hh
  refine ⟨r, ?_, by omega⟩
  have he := ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIP)
  exact he.symm.trans hQdim

/-- The direct numerical form used for the translated projective cone:
a seven-dimensional affine domain cut by four equations has all minimal
components of affine dimension at least three. -/
theorem fourEquation_minimalComponent_of_dimension_seven
    (K R : Type u) [Field K] [CharZero K] [CommRing R]
    [Algebra K R] [Algebra.FiniteType K R]
    (I P : Ideal R) [I.IsPrime] (family : Finset R)
    (hP : P ∈ (I ⊔ Ideal.span (family : Set R)).minimalPrimes)
    (hIdim : ringKrullDim (R ⧸ I) = (7 : WithBot ℕ∞))
    (hcard : family.card ≤ 4) :
    ∃ r : ℕ, 3 ≤ r ∧ ringKrullDim (R ⧸ P) = (r : WithBot ℕ∞) := by
  obtain ⟨r, hr, hle⟩ :=
    finiteEquation_minimalComponent_dimension_lower K R I P family hP (n := 7) hIdim
  exact ⟨r, by omega, hr⟩

end
end TranslatedDepthSeven
