import CubicTenVariables.PlanAlphaSmithMoments

/-! Arithmetic mass estimates for supplied majorant masses and widths.
These are the two Smith-weight summations used in the mixed-modulus
argument; their pointwise mass and width hypotheses remain explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CubicTenVariables.PlanAlphaMajorantMasses
open CubeFullSmithParameters CubefullSmithWeightLocal
open scoped BigOperators

private theorem scaled_mass_le (η X Cg : ℝ) (hη : 0 ≤ η) (hX : 1 ≤ X)
    (hCg : 0 ≤ Cg) (r : ℕ) (hr : (r : ℝ) ≤ 2*X) (P : ℝ)
    (hP : P ≤ Cg*(r : ℝ)^(10+η)*omega r) :
    P ≤ (Cg*(2 : ℝ)^(10+η)*X^(10+η))*omega r := by
  have hw : 0 ≤ omega r := by unfold omega; positivity
  have hp := Real.rpow_le_rpow (Nat.cast_nonneg r) hr (by linarith : 0 ≤ 10+η)
  calc
    P ≤ Cg*(2*X)^(10+η)*omega r :=
      hP.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hCg) hw)
    _ = _ := by rw [Real.mul_rpow (by norm_num) (zero_le_one.trans hX)]; ring

private theorem complement_shape_le (d T u : ℝ) (hd : 1 ≤ d)
    (hT : 0 ≤ T) (hu : 0 ≤ u) (hwidth : T ≤ 1+2*d*u) :
    T/d+(T/d)^9 ≤ 131072*(1+u+u^9) := by
  have hd0 : 0 < d := zero_lt_one.trans_le hd
  have hz0 : 0 ≤ T/d := div_nonneg hT hd0.le
  have hz : T/d ≤ 1+2*u := (div_le_iff₀ hd0).mpr (by nlinarith)
  have hz9 := pow_le_pow_left₀ hz0 hz 9
  have ha := add_pow_le (by norm_num : (0 : ℝ) ≤ 1)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hu) 9
  norm_num [mul_pow] at ha
  nlinarith [pow_nonneg hu 9]

/-- The tenth width moment has precisely the `121/12` cube-full scale
power and `10/3` cube-free width power. The scale-two losses are constants. -/
theorem exists_tenth_mass_bound (η ε : ℝ) (hη : 0 ≤ η) (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ X : ℝ, 1 ≤ X → ∀ Q : Finset ℕ,
      (∀ r ∈ Q, 0 < r ∧ CubeFull r ∧ (r : ℝ) ≤ 2*X) →
      ∀ D : ℝ, 1 ≤ D → ∀ Cg : ℝ, 0 ≤ Cg → ∀ P T : ℕ → ℝ,
      (∀ r ∈ Q, 0 ≤ P r) →
      (∀ r ∈ Q, P r ≤ Cg*(r : ℝ)^(10+η)*omega r) →
      (∀ r ∈ Q, 0 ≤ T r ∧ T r ≤ 1+2*D^((1 : ℝ)/3)*u r) →
      (∑ r ∈ Q, (T r)^10*P r) ≤
        K*Cg*X^((121 : ℝ)/12+η+ε)*D^((10 : ℝ)/3) := by
  obtain ⟨K,hK,hbound⟩ := PlanAlphaSmithMoments.exists_tenth_bound ε hε
  have htwo : 1 ≤ (2 : ℝ)^(10+η) := Real.one_le_rpow (by norm_num) (by linarith)
  refine ⟨K*(2 : ℝ)^(10+η)*1024,
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK htwo) (by norm_num),?_⟩
  intro X hX Q hQ D hD Cg hCg P T hP0 hP hT
  let R : ℝ := Cg*(2 : ℝ)^(10+η)*X^(10+η)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hd : 1 ≤ D^((1 : ℝ)/3) := Real.one_le_rpow hD (by norm_num)
  have hm := hbound X hX Q hQ (2*D^((1 : ℝ)/3)) (by linarith)
  have hpoint (r : ℕ) (hr : r ∈ Q) :
      (T r)^10*P r ≤ R*(omega r*(1+(2*D^((1 : ℝ)/3))*u r)^10) := by
    have hw : 0 ≤ u r := by unfold u; positivity
    have ht := pow_le_pow_left₀ (hT r hr).1 (hT r hr).2 10
    have hp := scaled_mass_le η X Cg hη hX hCg r (hQ r hr).2.2 (P r) (hP r hr)
    have hh := mul_le_mul ht hp (hP0 r hr) (by positivity)
    convert hh using 1 <;> dsimp [R] <;> ring
  have hscale : (2*D^((1 : ℝ)/3))^10 = 1024*D^((10 : ℝ)/3) := by
    rw [mul_pow,← Real.rpow_mul_natCast hD0]
    norm_num
  have hx : X^(10+η)*X^((1 : ℝ)/12+ε) = X^((121 : ℝ)/12+η+ε) := by
    rw [← Real.rpow_add (zero_lt_one.trans_le hX)]
    congr 1
    ring
  calc
    _ ≤ ∑ r ∈ Q, R*(omega r*(1+(2*D^((1 : ℝ)/3))*u r)^10) :=
      Finset.sum_le_sum hpoint
    _ = R*(∑ r ∈ Q, omega r*(1+(2*D^((1 : ℝ)/3))*u r)^10) := by
      rw [Finset.mul_sum]
    _ ≤ R*(K*X^((1 : ℝ)/12+ε)*(2*D^((1 : ℝ)/3))^10) :=
      mul_le_mul_of_nonneg_left hm hR
    _ = K*(2 : ℝ)^(10+η)*1024*Cg*(X^(10+η)*X^((1 : ℝ)/12+ε))*D^((10 : ℝ)/3) := by
      rw [hscale]
      dsimp [R]
      ring
    _ = _ := by rw [hx]

/-- The complementary width shape uses the zero, first and ninth Smith
moments, so it has no additional power loss beyond `η+ε`. -/
theorem exists_complement_mass_bound (η ε : ℝ) (hη : 0 ≤ η) (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ X : ℝ, 1 ≤ X → ∀ Q : Finset ℕ,
      (∀ r ∈ Q, 0 < r ∧ CubeFull r ∧ (r : ℝ) ≤ 2*X) →
      ∀ D : ℝ, 1 ≤ D → ∀ Cg : ℝ, 0 ≤ Cg → ∀ P T : ℕ → ℝ,
      (∀ r ∈ Q, 0 ≤ P r) →
      (∀ r ∈ Q, P r ≤ Cg*(r : ℝ)^(10+η)*omega r) →
      (∀ r ∈ Q, 0 ≤ T r ∧ T r ≤ 1+2*D^((1 : ℝ)/3)*u r) →
      (∑ r ∈ Q, (T r/D^((1 : ℝ)/3)+(T r/D^((1 : ℝ)/3))^9)*P r) ≤
        K*Cg*X^(10+η+ε) := by
  obtain ⟨K,hK,hbound⟩ := PlanAlphaSmithMoments.exists_complement_shape_bound ε hε
  have htwo : 1 ≤ (2 : ℝ)^(10+η) := Real.one_le_rpow (by norm_num) (by linarith)
  refine ⟨K*(2 : ℝ)^(10+η)*131072,
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK htwo) (by norm_num),?_⟩
  intro X hX Q hQ D hD Cg hCg P T hP0 hP hT
  let R : ℝ := Cg*(2 : ℝ)^(10+η)*X^(10+η)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hd : 1 ≤ D^((1 : ℝ)/3) := Real.one_le_rpow hD (by norm_num)
  have hpoint (r : ℕ) (hr : r ∈ Q) :
      (T r/D^((1 : ℝ)/3)+(T r/D^((1 : ℝ)/3))^9)*P r ≤
        R*131072*(omega r*(1+u r+(u r)^9)) := by
    have hu : 0 ≤ u r := by unfold u; positivity
    have hs := complement_shape_le (D^((1 : ℝ)/3)) (T r) (u r) hd
      (hT r hr).1 hu (hT r hr).2
    have hp := scaled_mass_le η X Cg hη hX hCg r (hQ r hr).2.2 (P r) (hP r hr)
    have hh := mul_le_mul hs hp (hP0 r hr) (by positivity)
    convert hh using 1 <;> dsimp [R] <;> ring
  calc
    _ ≤ ∑ r ∈ Q, R*131072*(omega r*(1+u r+(u r)^9)) := Finset.sum_le_sum hpoint
    _ = R*131072*(∑ r ∈ Q, omega r*(1+u r+(u r)^9)) := by rw [Finset.mul_sum]
    _ ≤ R*131072*(K*X^ε) :=
      mul_le_mul_of_nonneg_left (hbound X hX Q hQ) (by positivity)
    _ = K*(2 : ℝ)^(10+η)*131072*Cg*(X^(10+η)*X^ε) := by dsimp [R]; ring
    _ = _ := by rw [← Real.rpow_add (zero_lt_one.trans_le hX)]

end CubicTenVariables.PlanAlphaMajorantMasses
