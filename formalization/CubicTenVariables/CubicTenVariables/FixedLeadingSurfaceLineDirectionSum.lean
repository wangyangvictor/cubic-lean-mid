import CubicTenVariables.FixedLeadingSurfaceLineDirectionSumNumerical
import TranslatedDepthSeven.PrimitiveProjectiveDirectionCount

/-!
# Summing actual active lines by their projective directions

The only point-count premise concerns rational points on one fixed
projective zero locus. Integral line parameters, the active height cutoff,
the fibre multiplicity and the reciprocal-height sum are proved here.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace CubicTenVariables.FixedLeadingSurfaceLineDirectionSum
open MvPolynomial TranslatedDepthSeven Published
open FixedLeadingSurfaceLineDirectionSumNumerical
open scoped BigOperators LinearAlgebra.Projectivization

local instance : DecidableEq (Projectivization ℚ (Fin 3 → ℚ)) := Classical.decEq _

variable {n : ℕ}

theorem primitiveDirection_ne_zero {h : IntVector n} (hp : PrimitiveDirection h) : h ≠ 0 := by
  intro hz
  obtain ⟨i, hi⟩ := hp.exists_ne_zero
  exact hi (congrFun hz i)

theorem primitiveDirection_height_pos {h : IntVector n} (hp : PrimitiveDirection h) :
    0 < directionHeight h := by
  obtain ⟨i, hi, he⟩ := hp.exists_natAbs_eq_directionHeight
  rw [← he]
  exact Int.natAbs_pos.mpr hi

/-- The projective class of the actual primitive direction, without a
fallback class or a choice of sign. -/
def directionClass (h : IntVector n) (hp : PrimitiveDirection h) :
    Projectivization ℚ (Fin n → ℚ) :=
  integralProjectiveClass h (primitiveDirection_ne_zero hp)

theorem height_directionClass (h : IntVector n) (hp : PrimitiveDirection h) :
    primitiveRationalVectorHeight (directionClass h hp).rep = directionHeight h :=
  primitiveRationalVectorHeight_integralProjectiveClass_eq_directionHeight hp _

/-- Count a literal finite set of boxed integer points on a rational
line. Integral parameters are derived from primitivity, not assumed. -/
theorem boxed_line_card_le (points : Finset (IntVector n)) (base h : IntVector n)
    (hp : PrimitiveDirection h) (B : ℕ)
    (hline : ∀ x ∈ points, ∃ a : ℚ, ∀ i,
      ((x i - base i : ℤ) : ℚ) = a * (h i : ℚ))
    (hbox : ∀ x ∈ points, ∀ i, |x i| ≤ (B : ℤ)) :
    points.card ≤ 1 + (2 * B) / directionHeight h := by
  classical
  let parameter : {x // x ∈ points} → ℤ := fun x =>
    Classical.choose (hp.exists_integral_parameter_of_rational_line (hline x.val x.property))
  have hparameter (x : {x // x ∈ points}) (i : Fin n) :
      x.val i = base i + parameter x * h i :=
    Classical.choose_spec (hp.exists_integral_parameter_of_rational_line (hline x.val x.property)) i
  have hinj : Function.Injective parameter := by
    intro x y he
    apply Subtype.ext
    funext i
    rw [hparameter x i, hparameter y i, he]
  let A := points.attach.image parameter
  have hcard : A.card = points.card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
  have hAbox : ∀ a ∈ A, ∀ i, |base i + a * h i - (0 : IntVector n) i| ≤ (B : ℤ) := by
    intro a ha i
    obtain ⟨x, _hx, rfl⟩ := Finset.mem_image.mp ha
    simpa only [Pi.zero_apply, sub_zero, ← hparameter x i] using hbox x.val x.property i
  have hb := taggedLineParameters_card_le_directionHeight
    (h := h) (y₀ := base) (center := 0) (residue := 0)
    A (T := B) (r := 1) (by decide) hp hAbox
    (fun _ _ _ => Int.modEq_one)
  simpa only [one_mul, hcard] using hb

/-- Two points force the primitive direction height to be at most the
box diameter; this cutoff is not an additional geometric input. -/
theorem active_line_directionHeight_le (points : Finset (IntVector n)) (base h : IntVector n)
    (hp : PrimitiveDirection h) (B : ℕ) (hactive : 2 ≤ points.card)
    (hline : ∀ x ∈ points, ∃ a : ℚ, ∀ i,
      ((x i - base i : ℤ) : ℚ) = a * (h i : ℚ))
    (hbox : ∀ x ∈ points, ∀ i, |x i| ≤ (B : ℤ)) :
    directionHeight h ≤ 2 * B := by
  have hb := boxed_line_card_le points base h hp B hline hbox
  by_contra hn
  have hz : (2 * B) / directionHeight h = 0 := Nat.div_eq_of_lt (by omega)
  omega

/-- On active lines the additive one in the tagged bound is absorbed
into the radial weight 4B/height. -/
theorem active_boxed_line_card_le_weight
    (points : Finset (IntVector n)) (base h : IntVector n)
    (hp : PrimitiveDirection h) (B : ℕ) (hactive : 2 ≤ points.card)
    (hline : ∀ x ∈ points, ∃ a : ℚ, ∀ i,
      ((x i - base i : ℤ) : ℚ) = a * (h i : ℚ))
    (hbox : ∀ x ∈ points, ∀ i, |x i| ≤ (B : ℤ)) :
    (points.card : ℝ) ≤ 4 * B * ((1 : ℝ) / directionHeight h) := by
  have hnat := boxed_line_card_le points base h hp B hline hbox
  have hheight := active_line_directionHeight_le points base h hp B hactive hline hbox
  have hpos : (0 : ℝ) < directionHeight h := by exact_mod_cast primitiveDirection_height_pos hp
  have hone : (1 : ℝ) ≤ (2 * B : ℝ) / directionHeight h := by
    rw [le_div_iff₀ hpos, one_mul]
    exact_mod_cast hheight
  have hreal : (points.card : ℝ) ≤ 1 + (2 * B : ℝ) / directionHeight h := by
    calc
      _ ≤ 1 + (((2 * B) / directionHeight h : ℕ) : ℝ) := by exact_mod_cast hnat
      _ ≤ _ := by
        have hc : (((2 * B) / directionHeight h : ℕ) : ℝ) ≤
            ((2 * B : ℕ) : ℝ) / (directionHeight h : ℝ) := Nat.cast_div_le
        push_cast at hc
        linarith
  calc
    _ ≤ 1 + (2 * B : ℝ) / directionHeight h := hreal
    _ ≤ 2 * ((2 * B : ℝ) / directionHeight h) := by linarith
    _ = _ := by ring

/-- Bounding the actual projective-direction fibres turns a fixed
projective curve count into a line-height prefix bound. -/
theorem line_height_prefix_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → IntVector 3) (hp : ∀ l, PrimitiveDirection (h l))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) (M : ℕ) (C ε : ℝ)
    (hvanish : ∀ l, ∀ f ∈ I, eval (directionClass (h l) (hp l)).rep f = 0)
    (hmultiple : ∀ P : Projectivization ℚ (Fin 3 → ℚ),
      (Finset.univ.filter fun l => directionClass (h l) (hp l) = P).card ≤ M)
    (hcurve : ∀ R : ℕ, 1 ≤ R →
      (rationalProjectivePoints I (R : ℝ)).Finite ∧
      ((rationalProjectivePoints I (R : ℝ)).ncard : ℝ) ≤ C * (R : ℝ) ^ (1 + ε))
    (R : ℕ) (hR : 1 ≤ R) :
    ((heightPrefix Finset.univ (fun l => directionHeight (h l)) R).card : ℝ) ≤
      ((M : ℝ) * C) * (R : ℝ) ^ (1 + ε) := by
  classical
  let L := heightPrefix Finset.univ (fun l => directionHeight (h l)) R
  let D := L.image (fun l => directionClass (h l) (hp l))
  obtain ⟨hfinite, hcount⟩ := hcurve R hR
  have hsubset : (↑D : Set (Projectivization ℚ (Fin 3 → ℚ))) ⊆
      rationalProjectivePoints I (R : ℝ) := by
    intro P hP
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hP
    refine ⟨hvanish l, ?_⟩
    rw [height_directionClass]
    exact_mod_cast (Finset.mem_filter.mp hl).2
  have hD : (D.card : ℝ) ≤ C * (R : ℝ) ^ (1 + ε) := by
    have hn : D.card ≤ (rationalProjectivePoints I (R : ℝ)).ncard := by
      simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hsubset hfinite
    exact (Nat.cast_le.mpr hn).trans hcount
  have hL : L.card ≤ D.card * M := by
    apply finiteSet_card_le_index_card_mul_of_fibres L D
      (fun l => directionClass (h l) (hp l)) M
    · intro l hl
      exact Finset.mem_image.mpr ⟨l, hl, rfl⟩
    · intro P _hP
      apply le_trans _ (hmultiple P)
      apply Finset.card_le_card
      intro l hl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, (Finset.mem_filter.mp hl).2⟩
  calc
    _ ≤ (D.card : ℝ) * M := by exact_mod_cast hL
    _ ≤ (C * (R : ℝ) ^ (1 + ε)) * M :=
      mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg M)
    _ = _ := by ring

/-- Sum all the actual active boxed lines. The constant depends on the
fixed curve count, direction multiplicity and ε, but not on B or the
number, positions or lower coefficients of the lines. -/
theorem active_line_points_sum_le_curve_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (points : ι → Finset (IntVector 3)) (base h : ι → IntVector 3)
    (hp : ∀ l, PrimitiveDirection (h l))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) (M B : ℕ) (C ε : ℝ)
    (hB : 1 ≤ B) (hC : 0 ≤ C) (hε : 0 < ε)
    (hactive : ∀ l, 2 ≤ (points l).card)
    (hline : ∀ l, ∀ x ∈ points l, ∃ a : ℚ, ∀ i,
      ((x i - base l i : ℤ) : ℚ) = a * (h l i : ℚ))
    (hbox : ∀ l, ∀ x ∈ points l, ∀ i, |x i| ≤ (B : ℤ))
    (hvanish : ∀ l, ∀ f ∈ I, eval (directionClass (h l) (hp l)).rep f = 0)
    (hmultiple : ∀ P : Projectivization ℚ (Fin 3 → ℚ),
      (Finset.univ.filter fun l => directionClass (h l) (hp l) = P).card ≤ M)
    (hcurve : ∀ R : ℕ, 1 ≤ R →
      (rationalProjectivePoints I (R : ℝ)).Finite ∧
      ((rationalProjectivePoints I (R : ℝ)).ncard : ℝ) ≤ C * (R : ℝ) ^ (1 + ε)) :
    (∑ l, ((points l).card : ℝ)) ≤
      (4 * M * C * (1 + pSeriesConstant ε) * (2 : ℝ) ^ (2 * ε)) *
        (B : ℝ) ^ (1 + 2 * ε) := by
  have hweights := reciprocalHeight_sum_le_curve_power Finset.univ
    (fun l => directionHeight (h l)) (2 * B) ((M : ℝ) * C) ε
    (by omega) (mul_nonneg (Nat.cast_nonneg M) hC) hε
    (fun l _ => primitiveDirection_height_pos (hp l))
    (fun l _ => active_line_directionHeight_le (points l) (base l) (h l)
      (hp l) B (hactive l) (hline l) (hbox l))
    (fun R hR _ => line_height_prefix_le h hp I M C ε hvanish hmultiple hcurve R hR)
  have hsum : (∑ l, ((points l).card : ℝ)) ≤
      4 * B * ∑ l, ((1 : ℝ) / directionHeight (h l)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun l _ => active_boxed_line_card_le_weight
      (points l) (base l) (h l) (hp l) B (hactive l) (hline l) (hbox l)
  apply hsum.trans
  calc
    _ ≤ (4 * B) * (((M : ℝ) * C) * (1 + pSeriesConstant ε) *
        ((2 * B : ℕ) : ℝ) ^ (2 * ε)) :=
      mul_le_mul_of_nonneg_left hweights (by positivity)
    _ = _ := by
      have hBp : (0 : ℝ) < B := by exact_mod_cast Nat.zero_lt_of_lt hB
      have he : (B : ℝ) ^ (1 + 2 * ε) = (B : ℝ) * (B : ℝ) ^ (2 * ε) := by
        rw [Real.rpow_add hBp, Real.rpow_one]
      push_cast
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg B), he]
      ring

/-- Allocate half the requested exponent to the fixed-curve count and
half to summation. -/
theorem active_line_points_sum_le_target_exponent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (points : ι → Finset (IntVector 3)) (base h : ι → IntVector 3)
    (hp : ∀ l, PrimitiveDirection (h l))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) (M B : ℕ) (C ε : ℝ)
    (hB : 1 ≤ B) (hC : 0 ≤ C) (hε : 0 < ε)
    (hactive : ∀ l, 2 ≤ (points l).card)
    (hline : ∀ l, ∀ x ∈ points l, ∃ a : ℚ, ∀ i,
      ((x i - base l i : ℤ) : ℚ) = a * (h l i : ℚ))
    (hbox : ∀ l, ∀ x ∈ points l, ∀ i, |x i| ≤ (B : ℤ))
    (hvanish : ∀ l, ∀ f ∈ I, eval (directionClass (h l) (hp l)).rep f = 0)
    (hmultiple : ∀ P : Projectivization ℚ (Fin 3 → ℚ),
      (Finset.univ.filter fun l => directionClass (h l) (hp l) = P).card ≤ M)
    (hcurve : ∀ R : ℕ, 1 ≤ R →
      (rationalProjectivePoints I (R : ℝ)).Finite ∧
      ((rationalProjectivePoints I (R : ℝ)).ncard : ℝ) ≤ C * (R : ℝ) ^ (1 + ε / 2)) :
    (∑ l, ((points l).card : ℝ)) ≤
      (4 * M * C * (1 + pSeriesConstant (ε / 2)) * (2 : ℝ) ^ ε) *
        (B : ℝ) ^ (1 + ε) := by
  have hb := active_line_points_sum_le_curve_bound points base h hp I M B C (ε / 2)
    hB hC (by linarith) hactive hline hbox hvanish hmultiple hcurve
  simpa only [show (2 : ℝ) * (ε / 2) = ε by ring] using hb

end CubicTenVariables.FixedLeadingSurfaceLineDirectionSum
