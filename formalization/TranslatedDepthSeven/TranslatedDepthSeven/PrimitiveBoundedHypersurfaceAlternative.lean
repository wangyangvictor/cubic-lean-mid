import TranslatedDepthSeven.BoundedHypersurfaceEquation
import TranslatedDepthSeven.PrimitiveIntegralPolynomialNormalization
import TranslatedDepthSeven.HomogeneousCone

/-!
# The primitive small-equation alternative for an actual hypersurface

The original rationally irreducible integral equation may have arbitrarily
large coefficients. The finite set of bounded points is fixed before any
modulus. The resulting primitive equation either cuts the hypersurface
properly or defines exactly its integral schematic closure.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

theorem exists_bounded_primitive_hypersurface_equation_or_proper_cut
    {N e R : ℕ} (G : MvPolynomial (Fin (N + 1)) ℤ)
    (hG : G ≠ 0) (hhom : G.IsHomogeneous e)
    (hirreducible : Irreducible (G.map (Int.castRingHom ℚ)))
    (Z : Finset (IntVector (N + 1)))
    (hzero : ∀ z ∈ Z, MvPolynomial.eval z G = 0)
    (hcoord : ∀ z ∈ Z, ∀ i, (z i).natAbs ≤ R) :
    ∃ P : MvPolynomial (Fin (N + 1)) ℤ,
      P ≠ 0 ∧ IsPrimitiveIntegralMvPolynomial P ∧ P.IsHomogeneous e ∧
      (∀ z ∈ Z, MvPolynomial.eval z P = 0) ∧
      (∀ m, (P.coeff m).natAbs ≤
        (e + 1) ^ (N + 1) * ((e + 1) ^ (N + 1)).factorial *
          max 1 R ^ (e * (e + 1) ^ (N + 1))) ∧
      (P.map (Int.castRingHom ℚ) ∉
          Ideal.span {G.map (Int.castRingHom ℚ)} ∨
        ((∃ c : ℚ, c ≠ 0 ∧
            P.map (Int.castRingHom ℚ) =
              MvPolynomial.C c * G.map (Int.castRingHom ℚ)) ∧
          projectiveIntegralClosureIdeal
              (Ideal.span {G.map (Int.castRingHom ℚ)}) =
            Ideal.span {P})) := by
  classical
  obtain ⟨F, hF, hFhom, hFzero, hFbound⟩ :=
    exists_bounded_homogeneous_equation_on_bounded_zeros
      G hG hhom Z hzero hcoord
  obtain ⟨P, r, hP, hprimitive, _hr, hmap, hbound⟩ :=
    exists_primitive_integral_polynomial_of_ne_zero F hF
  have hPhom : P.IsHomogeneous e := by
    apply MvPolynomial.IsHomogeneous.of_map
      (f := Int.castRingHom ℚ) Int.cast_injective
    rw [hmap]
    exact (hFhom.map (Int.castRingHom ℚ)).C_mul r
  have hPzero : ∀ z ∈ Z, MvPolynomial.eval z P = 0 := by
    intro z hz
    have heval : ((MvPolynomial.eval z P : ℤ) : ℚ) = 0 := by
      rw [← eval_map_intCast P z, hmap, map_mul, MvPolynomial.eval_C,
        eval_map_intCast F z, hFzero z hz, Int.cast_zero, mul_zero]
    exact_mod_cast heval
  refine ⟨P, hP, hprimitive, hPhom, hPzero,
    (fun m ↦ (hbound m).trans (hFbound m)), ?_⟩
  by_cases hmem : P.map (Int.castRingHom ℚ) ∈
      Ideal.span {G.map (Int.castRingHom ℚ)}
  · right
    have hPmap : P.map (Int.castRingHom ℚ) ≠ 0 := by
      intro hz
      apply hP
      apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
      simpa using hz
    obtain ⟨c, hc, hscalar⟩ :=
      eq_scalar_mul_of_homogeneous_dvd_same_degree
        hPmap hirreducible.ne_zero
        (hPhom.map (Int.castRingHom ℚ)) (hhom.map (Int.castRingHom ℚ))
        (Ideal.mem_span_singleton.mp hmem)
    have hunit : IsUnit (MvPolynomial.C c : MvPolynomial (Fin (N + 1)) ℚ) :=
      (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
    have hPirred : Irreducible (P.map (Int.castRingHom ℚ)) := by
      rw [hscalar]
      exact (irreducible_isUnit_mul hunit).mpr hirreducible
    refine ⟨⟨c, hc, hscalar⟩, ?_⟩
    have hspan : Ideal.span {P.map (Int.castRingHom ℚ)} =
        Ideal.span {G.map (Int.castRingHom ℚ)} := by
      rw [hscalar]
      exact Ideal.span_singleton_mul_left_unit hunit _
    rw [← hspan]
    exact projectiveIntegralClosureIdeal_span_primitive P hprimitive hPirred
  · exact Or.inl hmem

/-- A homogeneous equation with the displayed coefficient bound has a
degree-only polynomial bound for every evaluated partial derivative.
The loose exponent `e` avoids endpoint cases at degree zero. -/
theorem bounded_homogeneous_partial_derivative
    {N e C R : ℕ} (P : MvPolynomial (Fin N) ℤ)
    (hhom : P.IsHomogeneous e)
    (hcoeff : ∀ m, (P.coeff m).natAbs ≤ C)
    (y : IntVector N) (hy : ∀ i, (y i).natAbs ≤ R) (j : Fin N) :
    (MvPolynomial.eval y (MvPolynomial.pderiv j P)).natAbs ≤
      (e + 1) ^ N * e * C * max 1 R ^ e := by
  have hs : P.support.card ≤ (e + 1) ^ N := by
    simpa using support_card_le_pow_succ_of_isHomogeneous P e hhom
  exact (eval_pderiv_natAbs_le_support_mul_degree_mul_coeff_mul_pow
    P y j (fun m _hm ↦ hcoeff m) hhom.totalDegree_le hy).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right C (Nat.mul_le_mul_right e hs)))

end

end TranslatedDepthSeven
