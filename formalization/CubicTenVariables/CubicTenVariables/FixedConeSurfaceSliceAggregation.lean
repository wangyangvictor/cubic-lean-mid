import CubicTenVariables.ResidueBoxCount
import TranslatedDepthSeven.RationalLinearProjectionBoxCount

/-!
# Aggregating fixed-cone counts through surface slices

This file contains the finite counting step needed to replace the
high-dimensional Salberger input by a family of two-dimensional determinant
estimates.  A finite progression point set is partitioned by a fixed rational
linear projection.  Good fibres receive a surface estimate, while all bad
points are counted together on one fixed exceptional locus.

No geometric or determinant-method assertion is made here.  In particular,
the fibre and exceptional estimates are hypotheses of the numerical
aggregation theorem, rather than a renamed high-dimensional point count.
-/

set_option autoImplicit false
noncomputable section

namespace CubicTenVariables.FixedConeSurfaceSliceAggregation

open TranslatedDepthSeven
open scoped BigOperators

local instance fixedConeSurfaceSliceAggregation_propDecidable
    (p : Prop) : Decidable p := Classical.propDecidable p

/-- The literal fibre of a finite point set under a displayed slice map. -/
def sliceFiber {Point Base : Type*} [DecidableEq Point]
    [DecidableEq Base] (slice : Point → Base)
    (S : Finset Point) (y : Base) : Finset Point :=
  S.filter fun x ↦ slice x = y

@[simp]
theorem mem_sliceFiber_iff {Point Base : Type*} [DecidableEq Point]
    [DecidableEq Base] (slice : Point → Base)
    (S : Finset Point) (y : Base) (x : Point) :
    x ∈ sliceFiber slice S y ↔ x ∈ S ∧ slice x = y := by
  simp [sliceFiber]

/-- Exact decomposition of a finite set over the slice values which actually
occur.  No ambient finiteness assumption on the parameter space is needed. -/
theorem card_eq_sum_sliceFiber {Point Base : Type*} [DecidableEq Point]
    [DecidableEq Base] (slice : Point → Base) (S : Finset Point) :
    S.card = ∑ y ∈ S.image slice, (sliceFiber slice S y).card := by
  classical
  simpa only [sliceFiber] using
    (Finset.card_eq_sum_card_fiberwise
      (s := S) (t := S.image slice) (f := slice)
      (fun x hx ↦ Finset.mem_image.mpr ⟨x, hx, rfl⟩))

/-- Elementary good/bad fibre aggregation in natural cardinalities. -/
theorem card_le_good_bad_sliceFibers
    {Point Base : Type*} [DecidableEq Point] [DecidableEq Base]
    (slice : Point → Base) (good : Base → Prop) [DecidablePred good]
    (S : Finset Point) (G B : ℕ)
    (hgood : ∀ y ∈ S.image slice, good y →
      (sliceFiber slice S y).card ≤ G)
    (hbad : ∀ y ∈ S.image slice, ¬ good y →
      (sliceFiber slice S y).card ≤ B) :
    S.card ≤
      ((S.image slice).filter good).card * G +
      ((S.image slice).filter fun y ↦ ¬ good y).card * B := by
  classical
  let Y := S.image slice
  let Ygood := Y.filter good
  let Ybad := Y.filter fun y ↦ ¬ good y
  have hunion : Ygood ∪ Ybad = Y := by
    ext y
    simp only [Ygood, Ybad, Finset.mem_union, Finset.mem_filter]
    tauto
  have hdisjoint : Disjoint Ygood Ybad := by
    apply Finset.disjoint_left.mpr
    intro y hyG hyB
    exact (Finset.mem_filter.mp hyB).2 (Finset.mem_filter.mp hyG).2
  rw [card_eq_sum_sliceFiber slice S]
  change (∑ y ∈ Y, (sliceFiber slice S y).card) ≤
    Ygood.card * G + Ybad.card * B
  rw [← hunion, Finset.sum_union hdisjoint]
  apply Nat.add_le_add
  · calc
      (∑ y ∈ Ygood, (sliceFiber slice S y).card) ≤
          ∑ _y ∈ Ygood, G := by
        apply Finset.sum_le_sum
        intro y hy
        exact hgood y (Finset.mem_filter.mp hy).1
          (Finset.mem_filter.mp hy).2
      _ = Ygood.card * G := by simp
  · calc
      (∑ y ∈ Ybad, (sliceFiber slice S y).card) ≤
          ∑ _y ∈ Ybad, B := by
        apply Finset.sum_le_sum
        intro y hy
        exact hbad y (Finset.mem_filter.mp hy).1
          (Finset.mem_filter.mp hy).2
      _ = Ybad.card * B := by simp

/-- Numerical slicing lemma in the exact shape needed by the fixed-cone
consumer.  There are `O(H^s)` possible good slice values, each good surface
fibre contributes `O(W^ε H^2)`, and the whole exceptional locus contributes
`O(H^(s+2))`.  Since `W^ε ≥ 1`, the total is
`O(W^ε H^(s+2))`.

The exceptional hypothesis concerns the single filtered subset of bad
points, not a high-dimensional count for the original set. -/
theorem card_cast_le_surfaceSlices_add_exceptional
    {Point Base : Type*} [DecidableEq Point] [DecidableEq Base]
    (slice : Point → Base) (good : Base → Prop) [DecidablePred good]
    (S : Finset Point) (s : ℕ)
    (H W ε A C E : ℝ)
    (hH : 1 ≤ H) (hW : 1 ≤ W) (hε : 0 ≤ ε)
    (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hbase : (((S.image slice).filter good).card : ℝ) ≤ A * H ^ s)
    (hgood : ∀ y ∈ S.image slice, good y →
      ((sliceFiber slice S y).card : ℝ) ≤
        C * W ^ ε * H ^ 2)
    (hexceptional :
      ((S.filter fun x ↦ ¬ good (slice x)).card : ℝ) ≤
        E * H ^ (s + 2)) :
    (S.card : ℝ) ≤ (A * C + E) * W ^ ε * H ^ (s + 2) := by
  classical
  let Y := S.image slice
  let Ygood := Y.filter good
  let Sgood := S.filter fun x ↦ good (slice x)
  let Sbad := S.filter fun x ↦ ¬ good (slice x)
  have hSunion : Sgood ∪ Sbad = S := by
    ext x
    simp only [Sgood, Sbad, Finset.mem_union, Finset.mem_filter]
    tauto
  have hSdisjoint : Disjoint Sgood Sbad := by
    apply Finset.disjoint_left.mpr
    intro x hxG hxB
    exact (Finset.mem_filter.mp hxB).2 (Finset.mem_filter.mp hxG).2
  have hgoodDecomp : Sgood.card =
      ∑ y ∈ Ygood, (sliceFiber slice S y).card := by
    have hsum := card_eq_sum_sliceFiber slice Sgood
    have himage : Sgood.image slice = Ygood := by
      ext y
      constructor
      · intro hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨x, (Finset.mem_filter.mp hx).1, rfl⟩,
            (Finset.mem_filter.mp hx).2⟩
      · intro hy
        obtain ⟨hyY, hyGood⟩ := Finset.mem_filter.mp hy
        obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hyY
        apply Finset.mem_image.mpr
        refine ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩, hxy⟩
        simpa only [hxy] using hyGood
    rw [himage] at hsum
    rw [hsum]
    apply Finset.sum_congr rfl
    intro y hy
    have hfibereq : sliceFiber slice Sgood y = sliceFiber slice S y := by
      apply Finset.ext
      intro x
      simp only [sliceFiber, Sgood, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hx, _hxgood⟩, hxy⟩
        exact ⟨hx, hxy⟩
      · rintro ⟨hx, hxy⟩
        have hyGood := (Finset.mem_filter.mp hy).2
        exact ⟨⟨hx, by simpa only [hxy] using hyGood⟩, hxy⟩
    exact congrArg Finset.card hfibereq
  have hgoodCount : (Sgood.card : ℝ) ≤
      (A * C) * W ^ ε * H ^ (s + 2) := by
    rw [hgoodDecomp, Nat.cast_sum]
    calc
      (∑ y ∈ Ygood, ((sliceFiber slice S y).card : ℝ)) ≤
          ∑ _y ∈ Ygood, C * W ^ ε * H ^ 2 := by
        apply Finset.sum_le_sum
        intro y hy
        exact hgood y (Finset.mem_filter.mp hy).1
          (Finset.mem_filter.mp hy).2
      _ = (Ygood.card : ℝ) * (C * W ^ ε * H ^ 2) := by simp
      _ ≤ (A * H ^ s) * (C * W ^ ε * H ^ 2) := by
        gcongr
      _ = (A * C) * W ^ ε * H ^ (s + 2) := by
        rw [pow_add]
        ring
  have hWε : 1 ≤ W ^ ε := Real.one_le_rpow hW hε
  rw [← hSunion, Finset.card_union_of_disjoint hSdisjoint, Nat.cast_add]
  calc
    (Sgood.card : ℝ) + (Sbad.card : ℝ) ≤
        (A * C) * W ^ ε * H ^ (s + 2) + E * H ^ (s + 2) :=
      add_le_add hgoodCount hexceptional
    _ ≤ (A * C) * W ^ ε * H ^ (s + 2) +
        E * W ^ ε * H ^ (s + 2) := by
      gcongr
      calc
        E = E * 1 := by ring
        _ ≤ E * W ^ ε := mul_le_mul_of_nonneg_left hWε hE
    _ = (A * C + E) * W ^ ε * H ^ (s + 2) := by ring

/-- The image of any displayed slice map which lands in an `s`-dimensional
translated box and one residue class has the expected `O(H^s)` size. -/
theorem sliceImage_card_cast_le_progressionBox
    {Point : Type*} [DecidableEq Point]
    {s : ℕ} (slice : Point → (Fin s → ℤ))
    (S : Finset Point) (center : Fin s → ℝ)
    (R : ℝ) (hR : 0 ≤ R) (m : ℕ) (hm : 0 < m)
    (hbox : ∀ x ∈ S, ∀ i,
      |(slice x i : ℝ) - center i| ≤ R)
    (hres : ∀ x ∈ S, ∀ y ∈ S, ∀ i,
      (slice x i : ZMod m) = (slice y i : ZMod m)) :
    ((S.image slice).card : ℝ) ≤
      7 ^ s * (1 + R / (m : ℝ)) ^ s := by
  classical
  letI : NeZero m := ⟨hm.ne'⟩
  have himageBox : ∀ z ∈ S.image slice, ∀ i,
      |(z i : ℝ) - center i| ≤ R := by
    intro z hz i
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact hbox x hx i
  have himageRes : ∀ z ∈ S.image slice, ∀ w ∈ S.image slice, ∀ i,
      (z i : ZMod m) = (w i : ZMod m) := by
    intro z hz w hw i
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
    exact hres x hx y hy i
  have hc := ResidueBoxCount.card_le_of_constant_residue
    m (S.image slice) center R hR himageBox himageRes
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have ht : 0 ≤ R / (m : ℝ) := div_nonneg hR hmR.le
  have hbase : 4 * R / (m : ℝ) + 3 ≤
      7 * (1 + R / (m : ℝ)) := by
    rw [mul_div_assoc]
    linarith
  calc
    ((S.image slice).card : ℝ) ≤
        (4 * R / (m : ℝ) + 3) ^ s := hc
    _ ≤ (7 * (1 + R / (m : ℝ))) ^ s :=
      pow_le_pow_left₀ (by positivity) hbase s
    _ = 7 ^ s * (1 + R / (m : ℝ)) ^ s := by rw [mul_pow]

/-- Real center of a fixed rectangular integral projection. -/
def integerProjectionRealCenter {n s : ℕ}
    (A : Matrix (Fin s) (Fin n) ℤ) (u : Fin n → ℝ) : Fin s → ℝ :=
  (A.map (Int.castRingHom ℝ)).mulVec u

/-- A fixed rectangular integral projection enlarges a translated box by
at most its explicit sum-of-coefficients constant. -/
theorem integerProjection_transformedBox
    {n s : ℕ} (A : Matrix (Fin s) (Fin n) ℤ)
    (x : Fin n → ℤ) (u : Fin n → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hx : ∀ j, |(x j : ℝ) - u j| ≤ L) :
    ∀ i, |(A.mulVec x i : ℝ) - integerProjectionRealCenter A u i| ≤
      (integerProjectionCoefficientBound A : ℝ) * L := by
  intro i
  have hrow : (∑ j, |(A i j : ℝ)|) ≤
      (integerProjectionCoefficientBound A : ℝ) := by
    exact_mod_cast integerProjection_row_sum_le A i
  calc
    |(A.mulVec x i : ℝ) - integerProjectionRealCenter A u i| =
        |∑ j, (A i j : ℝ) * ((x j : ℝ) - u j)| := by
      simp only [Matrix.mulVec, dotProduct, integerProjectionRealCenter,
        Matrix.map_apply, Int.cast_sum, Int.cast_mul, Int.coe_castRingHom]
      rw [← Finset.sum_sub_distrib]
      congr 2
      funext j
      ring
    _ ≤ ∑ j, |(A i j : ℝ) * ((x j : ℝ) - u j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |(A i j : ℝ)| * |(x j : ℝ) - u j| := by
      simp only [abs_mul]
    _ ≤ ∑ j, |(A i j : ℝ)| * L := by
      exact Finset.sum_le_sum fun j _ ↦
        mul_le_mul_of_nonneg_left (hx j) (abs_nonneg _)
    _ = (∑ j, |(A i j : ℝ)|) * L := (Finset.sum_mul ..).symm
    _ ≤ (integerProjectionCoefficientBound A : ℝ) * L :=
      mul_le_mul_of_nonneg_right hrow hL

/-- Integral linear maps preserve a common coordinatewise progression. -/
theorem integerProjection_preservesProgression
    {n s : ℕ} (A : Matrix (Fin s) (Fin n) ℤ)
    (x b : Fin n → ℤ) (m : ℕ)
    (hx : ∀ j, (m : ℤ) ∣ x j - b j) :
    ∀ i, (m : ℤ) ∣ A.mulVec x i - A.mulVec b i := by
  intro i
  rw [← Pi.sub_apply, ← Matrix.mulVec_sub]
  change (m : ℤ) ∣ ∑ j, A i j * (x j - b j)
  apply Finset.dvd_sum
  intro j _hj
  exact dvd_mul_of_dvd_right (hx j) (A i j)

/-- The actual cleared-numerator image of a fixed rational slice projection
has `O((1+L/m)^s)` values, with a completely explicit constant depending
only on the fixed matrix. -/
theorem rationalNumeratorSlice_image_card_cast_le
    {n s : ℕ} (A : Matrix (Fin s) (Fin n) ℚ)
    (S : Finset (Fin n → ℤ)) (u : Fin n → ℝ)
    (L : ℝ) (hL : 0 ≤ L) (m : ℕ) (hm : 0 < m)
    (b : Fin n → ℤ)
    (hbox : ∀ x ∈ S, ∀ j, |(x j : ℝ) - u j| ≤ L)
    (hres : ∀ x ∈ S, ∀ j, (m : ℤ) ∣ x j - b j) :
    ((S.image (integralNumeratorLinearProjection A)).card : ℝ) ≤
      (7 * (max 1 (integerProjectionCoefficientBound A.num) : ℕ)) ^ s *
        (1 + L / (m : ℝ)) ^ s := by
  classical
  let B : Matrix (Fin s) (Fin n) ℤ := A.num
  let K : ℕ := max 1 (integerProjectionCoefficientBound B)
  have hproj : integralNumeratorLinearProjection A = B.mulVec := by
    funext x i
    rfl
  have hsliceBox : ∀ x ∈ S, ∀ i,
      |(integralNumeratorLinearProjection A x i : ℝ) -
        integerProjectionRealCenter B u i| ≤
          (integerProjectionCoefficientBound B : ℝ) * L := by
    intro x hx i
    rw [hproj]
    exact integerProjection_transformedBox B x u L hL (hbox x hx) i
  have hsliceRes : ∀ x ∈ S, ∀ y ∈ S, ∀ i,
      (integralNumeratorLinearProjection A x i : ZMod m) =
        (integralNumeratorLinearProjection A y i : ZMod m) := by
    intro x hx y hy i
    rw [hproj]
    rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hxb := integerProjection_preservesProgression B x b m (hres x hx) i
    have hyb := integerProjection_preservesProgression B y b m (hres y hy) i
    simpa only [sub_sub_sub_cancel_right] using dvd_sub hxb hyb
  have hraw := sliceImage_card_cast_le_progressionBox
    (integralNumeratorLinearProjection A) S
    (integerProjectionRealCenter B u)
    ((integerProjectionCoefficientBound B : ℝ) * L)
    (mul_nonneg (Nat.cast_nonneg _) hL) m hm hsliceBox hsliceRes
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have ht : 0 ≤ L / (m : ℝ) := div_nonneg hL hmR.le
  have hCK : (integerProjectionCoefficientBound B : ℝ) ≤ K := by
    exact_mod_cast le_max_right 1 (integerProjectionCoefficientBound B)
  have hK1 : (1 : ℝ) ≤ K := by
    exact_mod_cast le_max_left 1 (integerProjectionCoefficientBound B)
  have hscale : 1 +
      ((integerProjectionCoefficientBound B : ℝ) * L) / (m : ℝ) ≤
      (K : ℝ) * (1 + L / (m : ℝ)) := by
    rw [mul_div_assoc]
    nlinarith
  calc
    ((S.image (integralNumeratorLinearProjection A)).card : ℝ) ≤
        7 ^ s * (1 + ((integerProjectionCoefficientBound B : ℝ) * L) /
          (m : ℝ)) ^ s := hraw
    _ ≤ 7 ^ s * ((K : ℝ) * (1 + L / (m : ℝ))) ^ s := by
      gcongr
    _ = (7 * K : ℕ) ^ s * (1 + L / (m : ℝ)) ^ s := by
      rw [mul_pow]
      push_cast
      ring
    _ = (7 * (max 1 (integerProjectionCoefficientBound A.num) : ℕ)) ^ s *
        (1 + L / (m : ℝ)) ^ s := by simp [K, B]

end CubicTenVariables.FixedConeSurfaceSliceAggregation
