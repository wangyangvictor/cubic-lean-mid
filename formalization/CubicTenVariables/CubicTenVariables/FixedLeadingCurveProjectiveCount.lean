import CubicTenVariables.Literature.HeathBrownTernaryPrimitiveCount
import CubicTenVariables.CubicGradientScaling
import TranslatedDepthSeven.PublishedCountingTheorems

/-!
# The fixed leading curve: primitive vectors to actual projective points

The LCM/GCD primitive integral representative of a projective point is
injective as a function of the point. Its coordinate sup norm is exactly
the height used by `Published.rationalProjectivePoints`. Homogeneity makes
it a zero of the actual integral equation. Thus the projective count is
bounded by the literal primitive-vector count, without any height or
point-realization premise. The only external numerical input in the final
theorems is the displayed fixed-form consequence of Heath-Brown's theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace CubicTenVariables.FixedLeadingCurveProjectiveCount

open MvPolynomial TranslatedDepthSeven Published Literature

/-- The existing concrete primitive normalization distinguishes different
rational projective points; no sign convention is needed for this injection. -/
theorem primitiveRepresentative_injective {N : ℕ} :
    Function.Injective (fun P : Projectivization ℚ (Fin (N + 1) → ℚ) ↦
      primitiveRationalVectorCoordinate P.rep) := by
  intro P Q h
  rw [← Projectivization.mk_rep P, ← Projectivization.mk_rep Q]
  apply (Projectivization.mk_eq_mk_iff' ℚ _ _ _ _).mpr
  refine ⟨primitiveRationalVectorScale Q.rep / primitiveRationalVectorScale P.rep, ?_⟩
  ext i
  have hi : primitiveRationalVectorScale P.rep * P.rep i =
      primitiveRationalVectorScale Q.rep * Q.rep i := by
    rw [← primitiveRationalVectorCoordinate_cast P.rep P.rep_nonzero i,
      ← primitiveRationalVectorCoordinate_cast Q.rep Q.rep_nonzero i]
    exact congrArg (fun z : ℤ ↦ (z : ℚ)) (congrFun h i)
  change (primitiveRationalVectorScale Q.rep / primitiveRationalVectorScale P.rep) *
    Q.rep i = P.rep i
  calc
    _ = (primitiveRationalVectorScale Q.rep * Q.rep i) /
        primitiveRationalVectorScale P.rep := by ring
    _ = (primitiveRationalVectorScale P.rep * P.rep i) /
        primitiveRationalVectorScale P.rep := by rw [hi]
    _ = _ := by
      rw [mul_comm, mul_div_cancel_right₀ _
        (primitiveRationalVectorScale_ne_zero P.rep P.rep_nonzero)]

/-- A bounded projective zero gives the literal primitive integral zero
in the same closed cube; the height cutoff does not grow. -/
theorem primitiveRepresentative_mem_primitiveTernaryZeros
    {d R : ℕ} (k : MvPolynomial (Fin 3) ℤ) (hk : k.IsHomogeneous d)
    (P : Projectivization ℚ (Fin 3 → ℚ))
    (hP : P ∈ rationalProjectivePoints (Ideal.span {map (Int.castRingHom ℚ) k})
      (R : ℝ)) :
    primitiveRationalVectorCoordinate P.rep ∈ primitiveTernaryZeros k R := by
  classical
  obtain ⟨hzero, hheight⟩ := hP
  have hheightNat : primitiveRationalVectorHeight P.rep ≤ R := by
    exact_mod_cast hheight
  have hz : eval P.rep (map (Int.castRingHom ℚ) k) = 0 :=
    hzero _ (Ideal.subset_span (Set.mem_singleton _))
  have hvec : (fun i ↦ (primitiveRationalVectorCoordinate P.rep i : ℚ)) =
      primitiveRationalVectorScale P.rep • P.rep := by
    ext i
    exact primitiveRationalVectorCoordinate_cast P.rep P.rep_nonzero i
  have hnormalized : eval (primitiveRationalVectorCoordinate P.rep) k = 0 := by
    have hcast : (Int.castRingHom ℚ)
        (eval (primitiveRationalVectorCoordinate P.rep) k) = 0 := by
      rw [MvPolynomial.map_eval]
      change eval (fun i ↦ (primitiveRationalVectorCoordinate P.rep i : ℚ))
        (map (Int.castRingHom ℚ) k) = 0
      rw [hvec]
      simpa only [eval₂_id, hz, mul_zero] using
        CubicGradientScaling.homogeneous_eval₂_smul
          (map (Int.castRingHom ℚ) k) (hk.map _) (RingHom.id ℚ)
          P.rep (primitiveRationalVectorScale P.rep)
    change ((eval (primitiveRationalVectorCoordinate P.rep) k : ℤ) : ℚ) = 0 at hcast
    exact_mod_cast hcast
  apply Finset.mem_filter.mpr
  refine ⟨?_, primitiveRationalVectorCoordinate_isPrimitive P.rep P.rep_nonzero,
    hnormalized⟩
  apply (mem_integerSupNormBox_iff _).mpr
  intro i
  exact (Finset.le_sup (f := fun j ↦
    (primitiveRationalVectorCoordinate P.rep j).natAbs) (Finset.mem_univ i)).trans hheightNat

/-- The projective point set is finite and no larger than the literal
primitive integer-vector count, for the actual primitive height. -/
theorem projectivePoints_finite_and_ncard_le_primitiveTernaryZeros
    {d : ℕ} (k : MvPolynomial (Fin 3) ℤ) (hk : k.IsHomogeneous d) (R : ℕ) :
    (rationalProjectivePoints (Ideal.span {map (Int.castRingHom ℚ) k}) (R : ℝ)).Finite ∧
    (rationalProjectivePoints (Ideal.span {map (Int.castRingHom ℚ) k}) (R : ℝ)).ncard ≤
      (primitiveTernaryZeros k R).card := by
  classical
  let f := fun P : Projectivization ℚ (Fin 3 → ℚ) ↦
    primitiveRationalVectorCoordinate P.rep
  have hmaps : Set.MapsTo f
      (rationalProjectivePoints (Ideal.span {map (Int.castRingHom ℚ) k}) (R : ℝ))
      (primitiveTernaryZeros k R : Set (Fin 3 → ℤ)) :=
    fun P hP ↦ primitiveRepresentative_mem_primitiveTernaryZeros k hk P hP
  have hinj : Function.Injective f := primitiveRepresentative_injective
  refine ⟨Set.Finite.of_injOn hmaps hinj.injOn (Finset.finite_toSet _), ?_⟩
  simpa only [Finset.coe_sort_coe, Set.ncard_coe_finset] using
    Set.ncard_le_ncard_of_injOn f hmaps hinj.injOn (Finset.finite_toSet _)

/-- The fixed projective leading curve has the required height bound,
conditional only on the explicit primitive-vector literature estimate. -/
theorem exists_fixed_projective_curve_bound
    (lit : HeathBrown2002FixedTernaryPrimitiveCount)
    {d : ℕ} (hd : 2 ≤ d) (k : MvPolynomial (Fin 3) ℤ) (hk : k.IsHomogeneous d)
    (hirr : IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) k))
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ, 1 ≤ R →
      (rationalProjectivePoints (Ideal.span {map (Int.castRingHom ℚ) k}) (R : ℝ)).Finite ∧
      ((rationalProjectivePoints (Ideal.span {map (Int.castRingHom ℚ) k})
        (R : ℝ)).ncard : ℝ) ≤ C * (R : ℝ) ^ (1 + η) := by
  obtain ⟨C, hC, hcount⟩ := lit d hd k hk hirr η hη
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨hfinite, hcard⟩ := projectivePoints_finite_and_ncard_le_primitiveTernaryZeros k hk R
  exact ⟨hfinite, (Nat.cast_le.mpr hcard).trans (hcount R hR)⟩

/-- The exponent used by the line-family summation theorem. The constant
is chosen from k and ε before any varying surface, lines, or box radius. -/
theorem exists_fixed_projective_curve_half_epsilon_bound
    (lit : HeathBrown2002FixedTernaryPrimitiveCount)
    {d : ℕ} (hd : 2 ≤ d) (k : MvPolynomial (Fin 3) ℤ) (hk : k.IsHomogeneous d)
    (hirr : IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) k))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ, 1 ≤ R →
      (rationalProjectivePoints (Ideal.span {map (Int.castRingHom ℚ) k}) (R : ℝ)).Finite ∧
      ((rationalProjectivePoints (Ideal.span {map (Int.castRingHom ℚ) k})
        (R : ℝ)).ncard : ℝ) ≤ C * (R : ℝ) ^ (1 + ε / 2) :=
  exists_fixed_projective_curve_bound lit hd k hk hirr (ε / 2) (half_pos hε)

end CubicTenVariables.FixedLeadingCurveProjectiveCount
