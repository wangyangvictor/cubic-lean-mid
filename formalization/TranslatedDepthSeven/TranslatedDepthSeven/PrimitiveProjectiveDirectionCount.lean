import TranslatedDepthSeven.RankSevenDegreeOneLowDirectionSource
import TranslatedDepthSeven.RankSevenDegreeOneProperStarSource
import TranslatedDepthSeven.ExplicitLineContribution

/-!
# Counting the bounded primitive directions on the fixed fivefold

Primitive integral representatives of one rational projective point differ
only by sign. Thus Salberger's projective theorem counts any finite set of
primitive directions with a factor of at most two. The constant is chosen
before the height cutoff and the finite set; it depends only on the fixed
variety and epsilon. There is no assumed direction-counting estimate.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

local instance : DecidableEq (Projectivization ℚ (Fin 13 → ℚ)) :=
  Classical.decEq _

set_option maxHeartbeats 8000000

theorem eq_or_neg_of_primitive_integralProjectiveClass_eq
    {n : ℕ} (h k : IntVector n)
    (hp : PrimitiveDirection h) (kp : PrimitiveDirection k)
    (hh : h ≠ 0) (hk : k ≠ 0)
    (heq : integralProjectiveClass k hk = integralProjectiveClass h hh) :
    k = h ∨ k = -h := by
  obtain ⟨q, hq, hscale⟩ :=
    exists_nonzero_rational_proportionality_of_integralProjectiveClass_eq
      h k hh hk heq
  rcases primitive_proportional_scalar_eq_one_or_neg_one q h k hq
      hp.isPrimitiveIntVector kp.isPrimitiveIntVector hscale with hqone | hqneg
  · left
    funext i
    have hi : (k i : ℚ) = (h i : ℚ) := by simpa [hqone] using hscale i
    exact_mod_cast hi
  · right
    funext i
    have hi : (k i : ℚ) = -(h i : ℚ) := by simpa [hqneg] using hscale i
    exact_mod_cast hi

/-- The literal fibre over a rational projective direction has at most
the two primitive integral representatives `h` and `-h`. -/
theorem primitiveDirectionFinset_card_le_two_mul_projectiveImage
    (directions : Finset (IntVector 13))
    (hprimitive : ∀ h ∈ directions, PrimitiveDirection h) :
    directions.card ≤
      (directions.image integralProjectiveClassOrFirstRankSeven).card * 2 := by
  classical
  apply finiteSet_card_le_index_card_mul_of_fibres directions
    (directions.image integralProjectiveClassOrFirstRankSeven)
    integralProjectiveClassOrFirstRankSeven 2
  · intro h hh
    exact Finset.mem_image.mpr ⟨h, hh, rfl⟩
  · intro P hP
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hP
    have hne : h ≠ 0 := by
      intro hzero
      obtain ⟨i, hi⟩ := (hprimitive h hh).exists_ne_zero
      exact hi (congrFun hzero i)
    have hsubset :
        (directions.filter fun k ↦ integralProjectiveClassOrFirstRankSeven k =
          integralProjectiveClassOrFirstRankSeven h) ⊆ {h, -h} := by
      intro k hk
      obtain ⟨hk, heq⟩ := Finset.mem_filter.mp hk
      have kne : k ≠ 0 := by
        intro kzero
        obtain ⟨i, hi⟩ := (hprimitive k hk).exists_ne_zero
        exact hi (congrFun kzero i)
      rw [integralProjectiveClassOrFirstRankSeven, dif_pos kne,
        integralProjectiveClassOrFirstRankSeven, dif_pos hne] at heq
      rcases eq_or_neg_of_primitive_integralProjectiveClass_eq h k
          (hprimitive h hh) (hprimitive k hk) hne kne heq with hsame | hneg
      · simp [hsame]
      · simp [hneg]
    exact (Finset.card_le_card hsubset).trans Finset.card_le_two

/-- Uniform in every bounded set of primitive common zeros of the fixed
fivefold. The fixed-variety constant in Salberger's Theorem 0.1 is used
with precisely its stated dependence. -/
theorem exists_uniform_primitiveDirectionFinset_bound_of_salberger2023
    (hSalberger : Salberger2023Theorem01)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (d : ℕ)
    (hI : IsIntegralProjectiveVariety
      (rationalDepthSevenEquationIdeal equations) 5 d)
    (hd : 2 ≤ d) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (directions : Finset (IntVector 13))
      (B : ℝ), 1 ≤ B →
      (∀ h ∈ directions, PrimitiveDirection h) →
      (∀ h ∈ directions, IntegralCommonZero equations h) →
      (∀ h ∈ directions, (directionHeight h : ℝ) ≤ B) →
      (directions.card : ℝ) ≤ C * B ^ (5 + epsilon) := by
  classical
  obtain ⟨C, hC, hsource⟩ := hSalberger 12 5 d
    (rationalDepthSevenEquationIdeal equations) hI hd epsilon hepsilon
  refine ⟨2 * C, by positivity, ?_⟩
  intro directions B hB hprimitive hzero hheight
  obtain ⟨hfinite, hcount⟩ := hsource B hB
  let image := directions.image integralProjectiveClassOrFirstRankSeven
  have hsubset : ↑image ⊆
      rationalProjectivePoints (rationalDepthSevenEquationIdeal equations) B := by
    intro P hP
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hP
    exact primitiveDirection_mem_rationalProjectivePoints_of_commonZero
      equations hhomogeneous h (hprimitive h hh) (hzero h hh) B (hheight h hh)
  have himage : image.card ≤
      (rationalProjectivePoints (rationalDepthSevenEquationIdeal equations) B).ncard := by
    simpa [Set.ncard_eq_toFinset_card _ hfinite] using
      Finset.card_le_card (s := image) (t := hfinite.toFinset) (by
        intro P hP
        simpa using hsubset hP)
  have hprojective : (image.card : ℝ) ≤ C * B ^ (5 + epsilon) := by
    exact (Nat.cast_le.mpr himage).trans hcount
  have hrepresentatives : (directions.card : ℝ) ≤ (image.card : ℝ) * 2 := by
    exact_mod_cast primitiveDirectionFinset_card_le_two_mul_projectiveImage
      directions hprimitive
  calc
    (directions.card : ℝ) ≤ (image.card : ℝ) * 2 := hrepresentatives
    _ ≤ (C * B ^ (5 + epsilon)) * 2 :=
      mul_le_mul_of_nonneg_right hprojective (by norm_num)
    _ = (2 * C) * B ^ (5 + epsilon) := by ring

end

end TranslatedDepthSeven
