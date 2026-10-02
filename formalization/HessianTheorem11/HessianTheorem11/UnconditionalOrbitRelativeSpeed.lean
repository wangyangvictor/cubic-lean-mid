import HessianTheorem11.UnconditionalOrbitFrameOrder
import HessianTheorem11.UnconditionalWeightMixedSpeed
import HessianTheorem11.UnconditionalOrbitMaximumDefs

/-! Exact relative ideal order and normalized speed are computed by the
finite active-character minimum. The factor n is retained explicitly. -/
noncomputable section
namespace HessianTheorem11.UnconditionalOrbitGlobal
open MvPolynomial PolynomialRestriction PolynomialWeightTransport RationalDescent ReducedRelative
  UnconditionalOrbitIdeal UnconditionalOrbitWeights
variable {K : Type*} [Field K] [Infinite K] {n d : ℕ}

theorem restrict_not_mem_target
    (F : MvPolynomial (Fin n) K) (S : Set (MvPolynomial (Fin n) K))
    (hS : slInvariant S) (hnot : F ∉ S)
    (B : Matrix (Fin n) (Fin n) K) (hB : B.det = 1) : restrict B F ∉ S := by
  intro h
  apply hnot
  have hi : B⁻¹.det = 1 := by rw [Matrix.det_nonsing_inv,hB,Ring.inverse_one]
  have hh := hS B⁻¹ hi _ h
  rwa [restrict_restrict,Matrix.mul_nonsing_inv B (hB ▸ isUnit_one),restrict_one] at hh

/-- Centered active characters have minimum exactly n times the relative
order, including order zero and the zero weight. -/
theorem finiteMinimum_eq_n_mul_order (hn : 0 < n)
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (S : Set (MvPolynomial (Fin n) K)) (hclosed : coefficientClosed S)
    (hS : slInvariant S) (hhom : ∀ G ∈ S, G.IsHomogeneous d) (hnot : F ∉ S)
    (w : Fin n → ℤ) (hw : ∑ i, w i = 0) (hW : HasNonnegativeWeights F w) (N : ℕ)
    (hgen : Ideal.span (boundedIdeal (finiteTarget (d := d) S) N :
      Set (MvPolynomial (DegreeIndex n d) K)) = vanishingIdeal K (finiteTarget (d := d) S)) :
    UnconditionalWeightMixed.finiteMinimum (activeCharacters (d := d) F S N) w =
      (n : ℤ) * relativeOrder d F S (identityWeightFrame w hw) := by
  classical
  let r := relativeOrder d F S (identityWeightFrame w hw)
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
  have hT := activeCharacters_nonempty F hF S hclosed hhom hnot N hgen
  obtain ⟨a,ha,hmin⟩ := UnconditionalWeightMixed.finiteMinimum_attained hT w
  have ha' := activeCharacters_subset F S N ha
  change a ∈ (equationMonomials n d N).image equationCharacter at ha'
  obtain ⟨e,_,hea⟩ := Finset.mem_image.mp ha'
  have hp : UnconditionalWeightMixed.integralCharacter a w =
      (n : ℤ) * exponentWeight (coefficientWeights w) e := by
    rw [←hea]
    exact equationCharacter_pairing e w hw
  let k := exponentWeight (coefficientWeights w) e
  have hlo : (n : ℤ) * r ≤ UnconditionalWeightMixed.integralCharacter a w :=
    (le_relativeOrder_iff_activeCharacters hn F hF S hclosed hS hhom hnot
      w hw hW N r hgen).mp le_rfl a ha
  rw [hp] at hlo
  have hle : (r : ℤ) ≤ k := (mul_le_mul_iff_right₀ hnZ).mp hlo
  have hk0 : 0 ≤ k := (Int.natCast_nonneg r).trans hle
  have hkbound : k.toNat ≤ r := by
    apply (le_relativeOrder_iff_activeCharacters hn F hF S hclosed hS hhom hnot
      w hw hW N k.toNat hgen).mpr
    intro b hb
    rw [Int.toNat_of_nonneg hk0]
    have hh := UnconditionalWeightMixed.finiteMinimum_le w hb
    rw [hmin,hp] at hh
    exact hh
  have hkle : k ≤ (r : ℤ) := by
    have hh : (k.toNat : ℤ) ≤ (r : ℤ) := by exact_mod_cast hkbound
    simpa only [Int.toNat_of_nonneg hk0] using hh
  have hk : k = (r : ℤ) := le_antisymm hkle hle
  rw [hmin,hp]
  change (n : ℤ) * k = (n : ℤ) * r
  rw [hk]

theorem relativeSpeed_eq_finiteSpeed_div (hn : 0 < n)
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (S : Set (MvPolynomial (Fin n) K)) (hclosed : coefficientClosed S)
    (hS : slInvariant S) (hhom : ∀ G ∈ S, G.IsHomogeneous d) (hnot : F ∉ S)
    (f : WeightFrame K n) (hdet : f.matrix.det = 1)
    (hW : HasNonnegativeWeights (restrict f.matrix F) f.weight) (N : ℕ)
    (hgen : Ideal.span (boundedIdeal (finiteTarget (d := d) S) N :
      Set (MvPolynomial (DegreeIndex n d) K)) = vanishingIdeal K (finiteTarget (d := d) S)) :
    relativeSpeed d F S f =
      UnconditionalWeightMixed.finiteSpeed
        (activeCharacters (d := d) (restrict f.matrix F) S N) f.weight / n := by
  have hmin := finiteMinimum_eq_n_mul_order hn (restrict f.matrix F)
    (homogeneous_restrict f.matrix F hF) S hclosed hS hhom
    (restrict_not_mem_target F S hS hnot f.matrix hdet) f.weight f.sum_zero hW N hgen
  unfold relativeSpeed UnconditionalWeightMixed.finiteSpeed
  rw [hmin,←relativeOrder_coordinate F hF S hclosed hS hhom hnot f hdet]
  have hnorm : ‖UnconditionalWeightOptimization.realWeight f.weight‖ =
      Real.sqrt (∑ i, (f.weight i : ℝ)^2) := by
    simp [UnconditionalWeightOptimization.realWeight,EuclideanSpace.norm_eq,Real.norm_eq_abs,sq_abs]
  rw [hnorm,Int.cast_mul,Int.cast_natCast]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [mul_div_assoc,mul_div_cancel_left₀ _ hnR]
  norm_cast

end HessianTheorem11.UnconditionalOrbitGlobal
