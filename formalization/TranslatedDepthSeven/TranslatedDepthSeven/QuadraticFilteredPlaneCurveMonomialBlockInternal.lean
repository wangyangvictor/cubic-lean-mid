import TranslatedDepthSeven.PlaneCurveAffineDegreeInternal

/-!
# A uniform half-power block for every nonlinear plane curve

Choose a quadratic monomial dividing the leading monomial of the actual
affine equation. Avoiding this smaller monomial gives `2k+1` independent
homogeneous columns with total affine weight `k(k+1)`, regardless of the
curve degree. This deliberately uses only the half-power exponent needed
by the bounded-degree branch of the surface argument.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial
open scoped BigOperators

theorem exists_quadratic_submonomial
    (m : Fin 2 →₀ ℕ) (hm : 2 ≤ m.degree) :
    ∃ a b : ℕ, a + b = 2 ∧ a ≤ m 0 ∧ b ≤ m 1 := by
  have hsum : 2 ≤ m 0 + m 1 := by
    simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hm
  by_cases htwo : 2 ≤ m 0
  · exact ⟨2, 0, by omega, htwo, Nat.zero_le _⟩
  by_cases hone : m 0 = 1
  · exact ⟨1, 1, by omega, by omega, by omega⟩
  · exact ⟨0, 2, by omega, Nat.zero_le _, by omega⟩

/-- Literal integer columns, with no dependence of the column count or
total weight on coefficients or curve degree. -/
theorem exists_quadraticFilteredPlaneCurveMonomialBlock_internal
    {δ k : ℕ} (hδ : 2 ≤ δ) (hk : 2 ≤ k)
    (P : MvPolynomial (Fin 3) ℤ) (hP : P.IsHomogeneous δ)
    (hirr : Irreducible (P.map (Int.castRingHom ℚ))) :
    ∃ (F : Fin (2 * k + 1) → MvPolynomial (Fin 3) ℤ)
      (w : Fin (2 * k + 1) → ℕ),
      LinearIndependent ℚ (fun i =>
        Ideal.Quotient.mk (Ideal.span ({P.map (Int.castRingHom ℚ)} : Set _))
          ((F i).map (Int.castRingHom ℚ))) ∧
      (∀ i, (F i).IsHomogeneous k) ∧
      (∑ i, w i) = k * (k + 1) ∧
      ∀ (R : ℕ) (x : Fin 3 → ℤ), x 0 = 1 →
        (x 1).natAbs ≤ R → (x 2).natAbs ≤ R →
        ∀ i, (eval x (F i)).natAbs ≤ R ^ w i := by
  classical
  let Pq := P.map (Int.castRingHom ℚ)
  obtain ⟨hfnz, hdegree⟩ := affinePlaneDehomogenization_degree_of_irreducible
    hδ Pq (hP.map _) hirr
  let m := MonomialOrder.degLex.degree (affinePlaneDehomogenization ℚ Pq)
  have hm : 2 ≤ m.degree := by
    dsimp only [m]
    rw [degree_degLexDegree, hdegree]
    exact hδ
  obtain ⟨a, b, hab, ha, hb⟩ := exists_quadratic_submonomial m hm
  let T := FilteredAffinePlaneCurveMonomialIndex a b k
  let e : Fin (2 * k + 1) ≃ T := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, card_filteredAffinePlaneCurveMonomialIndex_quadratic a b k hab hk])
  let F : Fin (2 * k + 1) → MvPolynomial (Fin 3) ℤ :=
    fun i => affinePlaneHomogeneousMonomial ℤ k (e i).1
  let w : Fin (2 * k + 1) → ℕ :=
    fun i => affinePlaneMonomialIndexWeight (e i).1
  refine ⟨F, w, ?_, ?_, ?_, ?_⟩
  · have hli := linearIndependent_filteredAffinePlaneCurveMonomials_of_leadingDivisor
      Pq hfnz k a b ha hb
    have hc := hli.comp e e.injective
    simpa only [F, affinePlaneHomogeneousMonomial, map_monomial,
      Int.cast_one, Function.comp_apply, Pq] using hc
  · intro i
    exact affinePlaneHomogeneousMonomial_isHomogeneous ℤ k (e i).1
  · change (∑ i, affinePlaneMonomialIndexWeight (e i).1) = k * (k + 1)
    rw [Equiv.sum_comp e (fun u : T => affinePlaneMonomialIndexWeight u.1)]
    exact sum_filteredAffinePlaneCurveMonomialWeight_quadratic a b k hab hk
  · intro R x hx0 hx1 hx2 i
    exact eval_filteredAffinePlaneCurveMonomial_natAbs_le a b k R (e i) x hx0 hx1 hx2

end
end TranslatedDepthSeven
