import TranslatedDepthSeven.BoundedPointSpanDichotomy
import TranslatedDepthSeven.DepthSevenOccupiedTangentPackets
import TranslatedDepthSeven.StrictRankAtMostSixLowDegree

/-!
# Proper hyperplanes through the counted points of a low-span fourfold

The two equations are obtained from the bounded integral points, not from
equations defining their component. If both vanish on the entire fourfold,
the concrete exceptional locus excludes every counted point. Otherwise a
proper hyperplane contains all the counted points. The latter alternative
is intended for the coefficient-uniform Pila estimate in one lower
dimension. No effective component-height assertion is used here.
-/

namespace TranslatedDepthSeven

noncomputable section

open Matrix MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 5000000

/-- One deliberately generous, absolute exceptional exponent for the
two equations obtained by Cramer's rule from points in thirteen variables. -/
theorem twoRowPointSpanHeight_le_exceptionalCutoff (p : Parameters) :
    Nat.factorial 2 *
      (Nat.factorial 11 * (max 1 ⌈p.B + p.L⌉₊) ^ 11) ^ 2 ≤
        ⌈p.H ^ 128⌉₊ := by
  let Y := max 1 ⌈p.B + p.L⌉₊
  have hY : (Y : ℝ) ≤ p.H := by
    have hceil := Nat.ceil_lt_add_one
      (show 0 ≤ p.B + p.L by linarith [p.hB, p.hL])
    have hceilH : (⌈p.B + p.L⌉₊ : ℝ) ≤ p.H := by
      unfold Parameters.H
      linarith [p.one_le_natCast_m]
    simpa only [Y, Nat.cast_max, Nat.cast_one] using
      (max_le (by linarith [p.five_le_H] : (1 : ℝ) ≤ p.H) hceilH)
  have hconstant : ((Nat.factorial 2 * Nat.factorial 11 ^ 2 : ℕ) : ℝ)
      ≤ p.H ^ 106 := by
    calc
      _ ≤ (2 : ℝ) ^ 106 := by norm_num
      _ ≤ p.H ^ 106 :=
        pow_le_pow_left₀ (by norm_num) (by linarith [p.five_le_H]) 106
  have hraw :
      ((Nat.factorial 2 * (Nat.factorial 11 * Y ^ 11) ^ 2 : ℕ) : ℝ)
        ≤ p.H ^ 128 := by
    calc
      _ = ((Nat.factorial 2 * Nat.factorial 11 ^ 2 : ℕ) : ℝ) *
          (Y : ℝ) ^ 22 := by push_cast; ring
      _ ≤ p.H ^ 106 * p.H ^ 22 := by gcongr
      _ = p.H ^ 128 := by rw [← pow_add]
  exact_mod_cast hraw.trans (Nat.le_ceil (p.H ^ 128))

/-- A nonempty finite subset of the literal normalized count on a
geometrically integral fourfold with two linear equations is contained in
a proper rational hyperplane section of that fourfold. The selected form
may depend on the finite point set; its coefficients need no height bound
when the next step is the uniform Pila estimate. -/
theorem normalizedPointSubset_empty_or_proper_hyperplane
    (p : Parameters) (x0 : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    {CF originalDegree d : ℕ} (hCF : 128 ≤ CF)
    (hOriginal : HasProjectiveDimensionDegree
      (rationalDepthSevenEquationIdeal equations) 5 originalDegree)
    (hOriginalGeometricallyPrime : GeometricallyPrimeMvPolynomialIdeal
      (rationalDepthSevenEquationIdeal equations))
    (Q : Ideal (MvPolynomial (Fin 13) ℚ))
    (hQhomogeneous : Q.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ))
    (hQbar : (qbarCoefficientExtensionIdeal Q).IsPrime)
    (hQprojective : HasProjectiveDimensionDegree Q 4 d)
    (hIQ : rationalDepthSevenEquationIdeal equations ≤ Q)
    (hlinear : 2 ≤ Module.finrank ℚ (rationalLinearFormsInIdeal Q))
    (Z : Finset (IntVector 13))
    (hZ : Z ⊆ depthSevenNormalizedDisplacementFinset p x0 equations CF)
    (hzero : ∀ z ∈ Z,
      (fun i ↦ (integralAffineMap x0 z p.m i : ℚ)) ∈
        affineIdealZeroLocus Q) :
    Z = ∅ ∨ ∃ f : MvPolynomial (Fin 13) ℚ,
      f.IsHomogeneous 1 ∧ f ∉ Q ∧
        ∀ z ∈ Z, MvPolynomial.eval
          (fun i ↦ (integralAffineMap x0 z p.m i : ℚ)) f = 0 := by
  classical
  let X := Z.image (fun z ↦ integralAffineMap x0 z p.m)
  have hXzero : ∀ x ∈ X, (fun i ↦ (x i : ℚ)) ∈
      affineIdealZeroLocus Q := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    exact hzero z hz
  have hXcoord : ∀ x ∈ X, ∀ i, (x i).natAbs ≤ ⌈p.B + p.L⌉₊ := by
    intro x hx i
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    exact depthSevenNormalized_affineImage_coordinate_le
      p x0 equations CF (hZ hz) i
  rcases bounded_containing_twoRowSection_or_proper_hyperplane
      Q hlinear X hXzero hXcoord with ⟨A, hArank, hAQ, hAheightRaw⟩ | hproper
  · left
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hAheight : rationalProjectiveLinearHeight A ≤ ⌈p.H ^ CF⌉₊ :=
      hAheightRaw.trans ((twoRowPointSpanHeight_le_exceptionalCutoff p).trans
        (Nat.ceil_mono (pow_le_pow_right₀
          (by linarith [p.five_le_H] : (1 : ℝ) ≤ p.H) hCF)))
    let R := qbarCoefficientExtensionIdeal Q
    have hsectionR : finiteEquationIdeal
        (geometricLinearSectionEquationFinset equations A) ≤ R := by
      apply geometricLinearSectionIdeal_le_of_rational_containment
        equations A Q R
      · simpa only [rationalDepthSevenEquationIdeal] using hIQ
      · exact hAQ
      · exact le_rfl
    have hRprojective : HasGeometricProjectiveDimensionDegree R 4 d :=
      qbarHasProjectiveDimensionDegree_of_rational Q hQprojective hQbar
    have hzdata := (Finset.mem_filter.mp (hZ hz)).2
    dsimp only at hzdata
    obtain ⟨_hzbox, _hzzero, hxne, _hnonlinear, hnotExceptional⟩ := hzdata
    have hxR : ProjectivePointVanishesOnGeometricIdeal R
        (integralProjectiveClass (integralAffineMap x0 z p.m) hxne) :=
      projectivePointVanishesOn_qbarCoefficientExtension Q hQhomogeneous
        (integralAffineMap x0 z p.m) hxne (hzero z hz)
    apply hnotExceptional
    exact memDepthSevenExceptionalLocus_of_codimensionTwo_fourfold_section
      equations ⌈p.H ^ CF⌉₊ A hArank hAheight
      (by simpa only [rationalDepthSevenEquationIdeal] using hOriginal)
      (by simpa only [rationalDepthSevenEquationIdeal] using
        hOriginalGeometricallyPrime)
      R hQbar hsectionR hRprojective
      (integralProjectiveClass (integralAffineMap x0 z p.m) hxne) hxR
  · right
    obtain ⟨f, hfhom, hfQ, hfzero⟩ := hproper
    refine ⟨f, hfhom, hfQ, ?_⟩
    intro z hz
    exact hfzero _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)

end

end TranslatedDepthSeven
