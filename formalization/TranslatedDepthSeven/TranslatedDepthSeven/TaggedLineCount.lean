import TranslatedDepthSeven.Parameters
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

/-!
# Counting one tagged affine line

This file proves the elementary estimate behind equation `eq:tagged-line`
of the short translated depth-seven argument.  Everything is stated over
integers.  A direction is primitive when an integral linear combination of
its coordinates is one.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- An integral vector is primitive if its coordinates generate the unit
ideal in `ℤ`. -/
def PrimitiveDirection {n : ℕ} (h : IntVector n) : Prop :=
  ∃ c : IntVector n, ∑ i, c i * h i = 1

/-- The integral sup norm of a direction vector. -/
def directionHeight {n : ℕ} (h : IntVector n) : ℕ :=
  Finset.univ.sup fun i ↦ (h i).natAbs

theorem PrimitiveDirection.exists_ne_zero
    {n : ℕ} {h : IntVector n} (hprimitive : PrimitiveDirection h) :
    ∃ i, h i ≠ 0 := by
  by_contra hzero
  push_neg at hzero
  obtain ⟨c, hc⟩ := hprimitive
  simp [hzero] at hc

/-- A primitive direction has a coordinate which attains its positive sup
norm. -/
theorem PrimitiveDirection.exists_natAbs_eq_directionHeight
    {n : ℕ} {h : IntVector n} (hprimitive : PrimitiveDirection h) :
    ∃ i, h i ≠ 0 ∧ (h i).natAbs = directionHeight h := by
  classical
  obtain ⟨i₀, hi₀⟩ := hprimitive.exists_ne_zero
  have huniv : (Finset.univ : Finset (Fin n)).Nonempty := ⟨i₀, Finset.mem_univ _⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup (s := (Finset.univ : Finset (Fin n)))
    huniv (fun i ↦ (h i).natAbs)
  have hheight_pos : 0 < directionHeight h := by
    unfold directionHeight
    exact lt_of_lt_of_le (Int.natAbs_pos.mpr hi₀)
      (Finset.le_sup (f := fun i ↦ (h i).natAbs) (Finset.mem_univ i₀))
  refine ⟨i, ?_, ?_⟩
  · exact Int.natAbs_ne_zero.mp (ne_of_gt (hi ▸ hheight_pos))
  · exact hi.symm

/-- If two integral points lie on a rational affine line whose integral
direction is primitive, then their rational line parameter is integral.

The proof is the elementary Bézout argument: if
`x - y₀ = a h` over `ℚ` and `∑ i, c i * h i = 1`, then
`a = ∑ i, c i * (x i - y₀ i)`.
-/
theorem PrimitiveDirection.exists_integral_parameter_of_rational_line
    {n : ℕ} {h y₀ x : IntVector n} (hprimitive : PrimitiveDirection h)
    (hline : ∃ a : ℚ, ∀ i,
      ((x i - y₀ i : ℤ) : ℚ) = a * ((h i : ℤ) : ℚ)) :
    ∃ z : ℤ, ∀ i, x i = y₀ i + z * h i := by
  classical
  obtain ⟨a, ha⟩ := hline
  obtain ⟨c, hc⟩ := hprimitive
  let z : ℤ := ∑ i, c i * (x i - y₀ i)
  have hza : (z : ℚ) = a := by
    calc
      (z : ℚ) = ∑ i, (c i : ℚ) * ((x i - y₀ i : ℤ) : ℚ) := by
        simp [z]
      _ = ∑ i, (c i : ℚ) * (a * (h i : ℚ)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [ha i]
      _ = a * ∑ i, (c i : ℚ) * (h i : ℚ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = a * ((∑ i, c i * h i : ℤ) : ℚ) := by simp
      _ = a := by rw [hc]; norm_num
  refine ⟨z, ?_⟩
  intro i
  have hiQ : (x i : ℚ) = (y₀ i : ℚ) + (z : ℚ) * (h i : ℚ) := by
    have hai := ha i
    push_cast at hai
    rw [hza]
    linarith
  exact_mod_cast hiQ

/-- The integral parameter on a line with nonzero primitive direction is
unique. -/
theorem PrimitiveDirection.integral_parameter_unique
    {n : ℕ} {h y₀ x : IntVector n} (hprimitive : PrimitiveDirection h)
    {z z' : ℤ}
    (hz : ∀ i, x i = y₀ i + z * h i)
    (hz' : ∀ i, x i = y₀ i + z' * h i) :
    z = z' := by
  obtain ⟨i, hi⟩ := hprimitive.exists_ne_zero
  apply mul_right_cancel₀ hi
  linarith [hz i, hz' i]

/-- Exact integral parametrization of the integral points on a rational
affine line with primitive integral direction. -/
theorem PrimitiveDirection.existsUnique_integral_parameter_of_rational_line
    {n : ℕ} {h y₀ x : IntVector n} (hprimitive : PrimitiveDirection h)
    (hline : ∃ a : ℚ, ∀ i,
      ((x i - y₀ i : ℤ) : ℚ) = a * ((h i : ℤ) : ℚ)) :
    ∃! z : ℤ, ∀ i, x i = y₀ i + z * h i := by
  obtain ⟨z, hz⟩ :=
    hprimitive.exists_integral_parameter_of_rational_line hline
  refine ⟨z, hz, ?_⟩
  intro z' hz'
  exact hprimitive.integral_parameter_unique hz' hz

/-- On a line with primitive integral direction, two points in the same
coordinatewise residue class modulo `r` have parameters congruent modulo
`r`. -/
theorem parameter_modEq_of_primitive
    {n : ℕ} {h y₀ residue : IntVector n} {r : ℕ} {a b : ℤ}
    (hprimitive : PrimitiveDirection h)
    (ha : ∀ i, y₀ i + a * h i ≡ residue i [ZMOD (r : ℤ)])
    (hb : ∀ i, y₀ i + b * h i ≡ residue i [ZMOD (r : ℤ)]) :
    a ≡ b [ZMOD (r : ℤ)] := by
  rw [Int.modEq_iff_dvd]
  obtain ⟨c, hc⟩ := hprimitive
  have hcoordinate : ∀ i, (r : ℤ) ∣ (b - a) * h i := by
    intro i
    have hab : y₀ i + a * h i ≡ y₀ i + b * h i [ZMOD (r : ℤ)] :=
      (ha i).trans (hb i).symm
    have hdvd := Int.modEq_iff_dvd.mp hab
    convert hdvd using 1
    ring
  have hsum : (r : ℤ) ∣ ∑ i, c i * ((b - a) * h i) := by
    exact Finset.dvd_sum fun i _ ↦ dvd_mul_of_dvd_right (hcoordinate i) (c i)
  have heq :
      ∑ i, c i * ((b - a) * h i) = (b - a) * ∑ i, c i * h i := by
    calc
      ∑ i, c i * ((b - a) * h i) = ∑ i, (b - a) * (c i * h i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (b - a) * ∑ i, c i * h i := (Finset.mul_sum _ _ _).symm
  rw [heq, hc, mul_one] at hsum
  exact hsum

/-- A finite collection of integers contained in an interval of diameter
`W` and lying in one residue class modulo a positive `s` contains at most
`1 + W / s` elements. -/
theorem finset_card_le_one_add_div_of_modEq_of_diameter
    (S : Finset ℤ) {s W : ℕ} (hs : 0 < s)
    (hmod : ∀ x ∈ S, ∀ y ∈ S, x ≡ y [ZMOD (s : ℤ)])
    (hdiameter : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ (W : ℤ)) :
    S.card ≤ 1 + W / s := by
  classical
  by_cases hS : S.Nonempty
  · let m : ℤ := S.min' hS
    have hm_mem : m ∈ S := by
      dsimp [m]
      exact S.min'_mem hS
    have hm_le : ∀ x ∈ S, m ≤ x := by
      intro x hx
      dsimp [m]
      exact S.min'_le x hx
    have hdvd : ∀ x : {x // x ∈ S}, (s : ℤ) ∣ x.1 - m := by
      intro x
      exact Int.modEq_iff_dvd.mp (hmod m hm_mem x.1 x.2)
    let q : {x // x ∈ S} → ℤ := fun x ↦ Classical.choose (hdvd x)
    have hq_spec : ∀ x : {x // x ∈ S}, x.1 - m = (s : ℤ) * q x := by
      intro x
      exact Classical.choose_spec (hdvd x)
    have hq_nonneg : ∀ x : {x // x ∈ S}, 0 ≤ q x := by
      intro x
      have hxnonneg : 0 ≤ x.1 - m := sub_nonneg.mpr (hm_le x.1 x.2)
      have hsInt : (0 : ℤ) < s := by exact_mod_cast hs
      rw [hq_spec x] at hxnonneg
      nlinarith
    have hq_bound : ∀ x : {x // x ∈ S}, (q x).toNat ≤ W / s := by
      intro x
      have hxdiam := hdiameter x.1 x.2 m hm_mem
      have hxnonneg : 0 ≤ x.1 - m := sub_nonneg.mpr (hm_le x.1 x.2)
      rw [abs_of_nonneg hxnonneg, hq_spec x] at hxdiam
      have hcast : s * (q x).toNat ≤ W := by
        have hxdiam' : (s : ℤ) * ((q x).toNat : ℤ) ≤ (W : ℤ) := by
          simpa [Int.toNat_of_nonneg (hq_nonneg x)] using hxdiam
        exact_mod_cast hxdiam'
      exact (Nat.le_div_iff_mul_le hs).2 (by simpa [mul_comm] using hcast)
    let f : {x // x ∈ S} → Fin (W / s + 1) := fun x ↦
      ⟨(q x).toNat, Nat.lt_succ_of_le (hq_bound x)⟩
    have hf : Function.Injective f := by
      intro x y hxy
      have hnat : (q x).toNat = (q y).toNat := congrArg Fin.val hxy
      have hq : q x = q y := by
        have hcast := congrArg (fun z : ℕ ↦ (z : ℤ)) hnat
        simpa [Int.toNat_of_nonneg (hq_nonneg x),
          Int.toNat_of_nonneg (hq_nonneg y)] using hcast
      apply Subtype.ext
      have hx := hq_spec x
      have hy := hq_spec y
      rw [hq] at hx
      linarith
    have hcard := Fintype.card_le_of_injective f hf
    simpa [Fintype.card_coe, Nat.add_comm] using hcard
  · simp only [Finset.not_nonempty_iff_eq_empty] at hS
    simp [hS]

/-- Concrete tagged-line estimate.  The parameters in `A` describe the
integral points `y₀ + a h`.  If these points lie in one coordinatewise box
of radius `T` and in one coordinatewise residue class modulo `r`, then any
nonzero coordinate `h j` gives the sharp bound

`A.card ≤ 1 + (2*T)/(r*|h j|)`.
-/
theorem taggedLineParameters_card_le
    {n : ℕ} {h y₀ center residue : IntVector n}
    (A : Finset ℤ) {T r : ℕ} (hr : 0 < r)
    (hprimitive : PrimitiveDirection h)
    (hbox : ∀ a ∈ A, ∀ i,
      |y₀ i + a * h i - center i| ≤ (T : ℤ))
    (hresidue : ∀ a ∈ A, ∀ i,
      y₀ i + a * h i ≡ residue i [ZMOD (r : ℤ)])
    (j : Fin n) (hj : h j ≠ 0) :
    A.card ≤ 1 + (2 * T) / (r * (h j).natAbs) := by
  classical
  let coordinate : ℤ → ℤ := fun a ↦ y₀ j + a * h j
  have hcoordinate_injective : Function.Injective coordinate := by
    intro a b hab
    dsimp [coordinate] at hab
    have hmul : (a - b) * h j = 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hj)
  let S : Finset ℤ := A.image coordinate
  have hcard : S.card = A.card := by
    dsimp [S]
    exact Finset.card_image_of_injective A hcoordinate_injective
  have hmod : ∀ x ∈ S, ∀ y ∈ S,
      x ≡ y [ZMOD (r * (h j).natAbs : ℕ)] := by
    intro x hx y hy
    simp only [S, Finset.mem_image] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    have hab : a ≡ b [ZMOD (r : ℤ)] :=
      parameter_modEq_of_primitive hprimitive (hresidue a ha) (hresidue b hb)
    have hraw :
        coordinate a ≡ coordinate b [ZMOD (r : ℤ) * h j] := by
      dsimp [coordinate]
      have hscaled : a * h j ≡ b * h j [ZMOD (r : ℤ) * h j] :=
        hab.mul_right'
      exact hscaled.add_left (y₀ j)
    have habs :
        coordinate a ≡ coordinate b
          [ZMOD (((r : ℤ) * h j).natAbs : ℤ)] :=
      Int.modEq_natAbs.mpr hraw
    simpa [Int.natAbs_mul] using habs
  have hdiameter : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ (2 * T : ℕ) := by
    intro x hx y hy
    simp only [S, Finset.mem_image] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    have haBox := hbox a ha j
    have hbBox := hbox b hb j
    dsimp [coordinate]
    have haBounds := abs_le.mp haBox
    have hbBounds := abs_le.mp hbBox
    apply abs_le.mpr
    constructor <;> omega
  have hspos : 0 < r * (h j).natAbs :=
    Nat.mul_pos hr (Int.natAbs_pos.mpr hj)
  have hbound := finset_card_le_one_add_div_of_modEq_of_diameter
    S hspos hmod hdiameter
  rw [hcard] at hbound
  simpa using hbound

/-- The tagged-line estimate with the denominator written using the exact
integral sup norm of the primitive direction. -/
theorem taggedLineParameters_card_le_directionHeight
    {n : ℕ} {h y₀ center residue : IntVector n}
    (A : Finset ℤ) {T r : ℕ} (hr : 0 < r)
    (hprimitive : PrimitiveDirection h)
    (hbox : ∀ a ∈ A, ∀ i,
      |y₀ i + a * h i - center i| ≤ (T : ℤ))
    (hresidue : ∀ a ∈ A, ∀ i,
      y₀ i + a * h i ≡ residue i [ZMOD (r : ℤ)]) :
    A.card ≤ 1 + (2 * T) / (r * directionHeight h) := by
  obtain ⟨j, hj, hheight⟩ := hprimitive.exists_natAbs_eq_directionHeight
  simpa [hheight] using
    taggedLineParameters_card_le A hr hprimitive hbox hresidue j hj

/-- Center-free tagged-line estimate.  It is enough to know the diameter of
one coordinate of the finite line segment. -/
theorem taggedLineParameters_card_le_of_coordinate_diameter
    {n : ℕ} {h y₀ residue : IntVector n}
    (A : Finset ℤ) {W r : ℕ} (hr : 0 < r)
    (hprimitive : PrimitiveDirection h)
    (hresidue : ∀ a ∈ A, ∀ i,
      y₀ i + a * h i ≡ residue i [ZMOD (r : ℤ)])
    (j : Fin n) (hj : h j ≠ 0)
    (hdiameter : ∀ a ∈ A, ∀ b ∈ A,
      |a * h j - b * h j| ≤ (W : ℤ)) :
    A.card ≤ 1 + W / (r * (h j).natAbs) := by
  classical
  let values : Finset ℤ := A.image fun a ↦ a * h j
  have hmap_injective : Function.Injective (fun a : ℤ ↦ a * h j) := by
    intro a b hab
    exact mul_right_cancel₀ hj hab
  have hcard : values.card = A.card := by
    dsimp [values]
    exact Finset.card_image_of_injective A hmap_injective
  have hmod : ∀ x ∈ values, ∀ y ∈ values,
      x ≡ y [ZMOD (r * (h j).natAbs : ℕ)] := by
    intro x hx y hy
    simp only [values, Finset.mem_image] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    have hab : a ≡ b [ZMOD (r : ℤ)] :=
      parameter_modEq_of_primitive hprimitive (hresidue a ha) (hresidue b hb)
    have hraw : a * h j ≡ b * h j [ZMOD (r : ℤ) * h j] := hab.mul_right'
    have habs : a * h j ≡ b * h j
        [ZMOD (((r : ℤ) * h j).natAbs : ℤ)] := Int.modEq_natAbs.mpr hraw
    simpa [Int.natAbs_mul] using habs
  have hvalue_diameter : ∀ x ∈ values, ∀ y ∈ values,
      |x - y| ≤ (W : ℤ) := by
    intro x hx y hy
    simp only [values, Finset.mem_image] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact hdiameter a ha b hb
  have hbound := finset_card_le_one_add_div_of_modEq_of_diameter values
    (Nat.mul_pos hr (Int.natAbs_pos.mpr hj)) hmod hvalue_diameter
  rw [hcard] at hbound
  exact hbound

/-- Tagged-line estimate for the actual manuscript situation: an arbitrary
real translated box of nonnegative radius `R`.  The integral diameter is
bounded by `⌈2R⌉`. -/
theorem taggedLineParameters_card_le_realBox
    {n : ℕ} {h y₀ residue : IntVector n} {center : RealVector n}
    (A : Finset ℤ) {R : ℝ} {r : ℕ} (hr : 0 < r)
    (hprimitive : PrimitiveDirection h)
    (hbox : ∀ a ∈ A, ∀ i,
      |((y₀ i + a * h i : ℤ) : ℝ) - center i| ≤ R)
    (hresidue : ∀ a ∈ A, ∀ i,
      y₀ i + a * h i ≡ residue i [ZMOD (r : ℤ)])
    (j : Fin n) (hj : h j ≠ 0) :
    A.card ≤ 1 + ⌈2 * R⌉₊ / (r * (h j).natAbs) := by
  apply taggedLineParameters_card_le_of_coordinate_diameter A hr hprimitive
    hresidue j hj
  intro a ha b hb
  have habReal :
      |(((a * h j - b * h j : ℤ) : ℝ))| ≤ 2 * R := by
    have haBox := hbox a ha j
    have hbBox := hbox b hb j
    calc
      |(((a * h j - b * h j : ℤ) : ℝ))| =
          |(((y₀ j + a * h j : ℤ) : ℝ) - center j) -
            (((y₀ j + b * h j : ℤ) : ℝ) - center j)| := by
              congr 1
              push_cast
              ring
      _ ≤ |(((y₀ j + a * h j : ℤ) : ℝ) - center j)| +
          |(((y₀ j + b * h j : ℤ) : ℝ) - center j)| := abs_sub _ _
      _ ≤ R + R := add_le_add haBox hbBox
      _ = 2 * R := by ring
  have hceil : 2 * R ≤ (⌈2 * R⌉₊ : ℝ) := Nat.le_ceil _
  have habCast : ((|(a * h j - b * h j : ℤ)| : ℤ) : ℝ) ≤
      (⌈2 * R⌉₊ : ℝ) := by
    rw [Int.cast_abs]
    exact habReal.trans hceil
  exact_mod_cast habCast

/-- Real-box tagged-line estimate with the exact primitive sup norm in the
denominator. -/
theorem taggedLineParameters_card_le_realBox_directionHeight
    {n : ℕ} {h y₀ residue : IntVector n} {center : RealVector n}
    (A : Finset ℤ) {R : ℝ} {r : ℕ} (hr : 0 < r)
    (hprimitive : PrimitiveDirection h)
    (hbox : ∀ a ∈ A, ∀ i,
      |((y₀ i + a * h i : ℤ) : ℝ) - center i| ≤ R)
    (hresidue : ∀ a ∈ A, ∀ i,
      y₀ i + a * h i ≡ residue i [ZMOD (r : ℤ)]) :
    A.card ≤ 1 + ⌈2 * R⌉₊ / (r * directionHeight h) := by
  obtain ⟨j, hj, hheight⟩ := hprimitive.exists_natAbs_eq_directionHeight
  simpa [hheight] using taggedLineParameters_card_le_realBox A hr
    hprimitive hbox hresidue j hj

end

end TranslatedDepthSeven
