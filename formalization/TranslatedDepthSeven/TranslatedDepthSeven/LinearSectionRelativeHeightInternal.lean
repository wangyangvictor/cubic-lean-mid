import TranslatedDepthSeven.RankSevenSourceSectionComponents
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Relative heights of components of a linear section

Krull's height theorem applies in the coordinate ring of the original
variety, not in the ambient polynomial ring. The first lemma makes that
quotient explicit and retains minimality after quotienting. Its matrix
specialization allows zero, repeated, or dependent row equations.

This proves the height part of the four-hyperplane argument. It does not
by itself assert a component-dimension lower bound or a degree-sum bound:
those require the relevant dimension formula and Bezout argument as well.
-/

namespace TranslatedDepthSeven

noncomputable section

set_option maxHeartbeats 1200000

/-- A minimal component after adjoining a finite equation family has
relative height at most the size of that family in the original quotient. -/
theorem quotient_component_height_le_equation_count
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I P : Ideal R) (family : Finset R)
    (hP : P ∈ (I ⊔ Ideal.span (family : Set R)).minimalPrimes) :
    (P.map (Ideal.Quotient.mk I)).height ≤ family.card := by
  classical
  let f : R →+* R ⧸ I := Ideal.Quotient.mk I
  have hmap : P.map f ∈ ((Ideal.span (family : Set R)).map f).minimalPrimes := by
    rw [Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective]
    apply Set.mem_image_of_mem
    simpa only [f, Ideal.mk_ker, sup_comm] using hP
  have hspan : (Ideal.span (family : Set R)).map f =
      Ideal.span ((family.image f : Finset (R ⧸ I)) : Set (R ⧸ I)) := by
    rw [Ideal.map_span, Finset.coe_image]
  rw [hspan] at hmap
  exact (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmap).trans
    (by exact_mod_cast Finset.card_image_le (s := family) (f := f))

/-- At most `c` row equations give relative component height at most `c`.
No rank or independence hypothesis on the matrix is needed. -/
theorem rationalRowLinearSection_componentRelativeHeight_le
    {N c : ℕ} (I P : Ideal (MvPolynomial (Fin N) ℚ))
    (A : Matrix (Fin c) (Fin N) ℚ)
    (hP : P ∈ finiteMinimalPrimes
      (I ⊔ finiteEquationIdeal (rationalMatrixRowLinearEquationFamily A))) :
    (P.map (Ideal.Quotient.mk I)).height ≤ c := by
  classical
  have h := quotient_component_height_le_equation_count I P
    (rationalMatrixRowLinearEquationFamily A)
    ((mem_finiteMinimalPrimes_iff _ _).mp hP)
  apply h.trans
  have hcard : (rationalMatrixRowLinearEquationFamily A).card ≤ c := by
    dsimp only [rationalMatrixRowLinearEquationFamily]
    exact (Finset.card_image_le).trans (by simp)
  exact_mod_cast hcard

/-- The literal four-hyperplane section used by the translated estimate
satisfies the relative-height bound in the translated-cone coordinate ring. -/
theorem rankSevenSourceSection_componentRelativeHeight_le_four
    (x₀ : IntVector 13) (m : ℕ) (hm : 0 < m)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (A : Matrix (Fin 4) (Fin 14) ℚ)
    (P : Ideal (MvPolynomial (Fin 14) ℚ))
    (hP : P ∈ finiteMinimalPrimes
      (rankSevenSourceSectionIdeal x₀ m hm equations A)) :
    let hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    let I := finiteEquationIdeal
      ((translatedProjectiveConeLiftEquationFamily
        (fun i ↦ (x₀ i : ℚ)) (m : ℚ) hmQ equations).image
          (MvPolynomial.rename (finSuccEquiv 13).symm))
    (P.map (Ideal.Quotient.mk I)).height ≤ 4 := by
  classical
  apply rationalRowLinearSection_componentRelativeHeight_le _ P A
  simpa only [rankSevenSourceSectionIdeal, rankSevenSourceSectionEquationFinset,
    finiteEquationIdeal_union_rowLinearEquationFamily] using hP

end

end TranslatedDepthSeven
