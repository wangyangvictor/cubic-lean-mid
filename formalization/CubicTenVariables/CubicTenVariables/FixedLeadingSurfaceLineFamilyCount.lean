import CubicTenVariables.FixedLeadingSurfaceDirectionMultiplicity
import CubicTenVariables.FixedLeadingSurfaceDirectionDependenceCoordinates
import CubicTenVariables.FixedLeadingSurfaceLineDirectionIncidence
import CubicTenVariables.FixedLeadingSurfaceLineFamilySum
import CubicTenVariables.FixedLeadingSurfaceSingularCount

/-!
# Actual line families on a fixed-leading surface

The surface equation and actual contained lines supply direction incidence
and the degree-only multiplicity bound d². The remaining numerical premise
is solely a rational-point estimate on the fixed projective leading curve.
Singleton line occurrences are charged separately by the family size.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace CubicTenVariables.FixedLeadingSurfaceLineFamilyCount

open MvPolynomial TranslatedDepthSeven Published
open FixedLeadingSurfaceParallelLineTransport FixedLeadingSurfaceDirectionMultiplicity
open FixedLeadingSurfaceLineDirectionSumNumerical FixedLeadingSurfaceLineFamilySum
open FixedLeadingSurfaceLineDirectionIncidence FixedLeadingSurfaceDirectionDependence
open scoped BigOperators

/-- All geometric direction hypotheses of the line-sum theorem are proved
for the actual fixed-leading family. The constant is independent of lower
coefficients, the nonzero scalar, and the number and position of lines. -/
theorem line_points_sum_le_of_fixed_leading_form
    {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} (hd : 2 ≤ d)
    (g k : MvPolynomial (Fin 3) ℤ) (hk : k.IsHomogeneous d)
    (hirr : IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) k))
    {c : ℚ} (hc : c ≠ 0) (hdegree : g.totalDegree ≤ d)
    (htop : map (Int.castRingHom ℚ) (homogeneousComponent d g) =
      C c * map (Int.castRingHom ℚ) k)
    (points : ι → Finset (IntVector 3)) (base v : ι → IntVector 3)
    (hp : ∀ l, PrimitiveDirection (v l))
    (hdistinct : Function.Injective (fun l =>
      affineLine (rationalVector (base l)) (rationalVector (v l))))
    (hcontained : ∀ l, linePolynomial g (base l) (v l) = 0)
    (B : ℕ) (C ε : ℝ) (hB : 1 ≤ B) (hC : 0 ≤ C) (hε : 0 < ε)
    (hline : ∀ l, ∀ x ∈ points l, ∃ a : ℚ, ∀ i,
      ((x i - base l i : ℤ) : ℚ) = a * (v l i : ℚ))
    (hbox : ∀ l, ∀ x ∈ points l, ∀ i, |x i| ≤ (B : ℤ))
    (hcurve : ∀ R : ℕ, 1 ≤ R →
      (rationalProjectivePoints (Ideal.span {map (Int.castRingHom ℚ) k}) (R : ℝ)).Finite ∧
      ((rationalProjectivePoints (Ideal.span {map (Int.castRingHom ℚ) k})
        (R : ℝ)).ncard : ℝ) ≤ C * (R : ℝ) ^ (1 + ε / 2)) :
    (∑ l, ((points l).card : ℝ)) ≤ (Fintype.card ι : ℝ) +
      (4 * (d ^ 2 : ℕ) * C * (1 + pSeriesConstant (ε / 2)) * (2 : ℝ) ^ ε) *
        (B : ℝ) ^ (1 + ε) := by
  have hdegreeQ : (map (Int.castRingHom ℚ) g).totalDegree ≤ d :=
    (Finset.sup_mono (support_map_subset _ _)).trans hdegree
  have htopQ : homogeneousComponent d (map (Int.castRingHom ℚ) g) =
      MvPolynomial.C c * map (Int.castRingHom ℚ) k := by
    convert htop using 1
    ext μ
    simp [coeff_homogeneousComponent, coeff_map]
  have hgeom : IsAbsolutelyIrreducible
      (homogeneousComponent d (map (Int.castRingHom ℚ) g)) := by
    rw [htopQ]
    exact hirr.const_mul c hc
  have hg : Irreducible (map (Int.castRingHom ℚ) g) :=
    IrreducibleFromTopHomogeneousPart.irreducible_of_irreducible_homogeneousComponent
      _ hdegreeQ (FixedLeadingSurfaceSingularCount.irreducible_actual_top k g c hirr hc htop)
  apply line_points_sum_le_card_add_curve_bound points base v hp
    (Ideal.span {map (Int.castRingHom ℚ) k}) (d ^ 2) B C ε hB hC hε hline hbox
  · exact family_direction_incidence_of_contained_lines
      g k hk base v hp hdegreeQ hc htopQ hcontained
  · intro P
    apply projective_direction_fibre_card_le (by omega : 1 ≤ d)
      (map (Int.castRingHom ℚ) g) hdegreeQ hg
      (fun e => degreeOf_zero_pos_restrict_coordinateMatrix hd e _ hgeom)
      base v hp hdistinct _ P
    intro l t
    have he := (eval_map_linePolynomial_at_rat g (base l) (v l) t).symm
    simpa only [hcontained l, Polynomial.map_zero, Polynomial.eval_zero,
      rationalVector, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using he
  · exact hcurve

end CubicTenVariables.FixedLeadingSurfaceLineFamilyCount
