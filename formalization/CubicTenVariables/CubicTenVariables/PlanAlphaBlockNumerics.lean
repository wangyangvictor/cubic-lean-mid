import CubicTenVariables.PlanAlphaMixedNumerics

/-! The numerical saving from explicit mass bounds at comparable dyadic
scales. All mass hypotheses remain supplied; this module makes no claim
that an arithmetic block satisfies them. Zero masses require no division. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CubicTenVariables.PlanAlphaBlockNumerics

private theorem scaled_product (S A B a b : ℝ) (hS : 0 ≤ S)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    (S*A)^a*(S*B)^b = S*(A^a*B^b) := by
  rw [Real.mul_rpow hS hA,Real.mul_rpow hS hB]
  calc
    _ = (S^a*S^b)*(A^a*B^b) := by ring
    _ = _ := by rw [← Real.rpow_add_of_nonneg hS ha hb,hab,Real.rpow_one]

private theorem first_identity (g D C : ℝ) (hg : 1 ≤ g) (hD : 1 ≤ D) (hC : 1 ≤ C) :
    g^((28 : ℝ)/3)*C^10*D^((59 : ℝ)/6) =
      (g*D*C)^10*g^(-(2 : ℝ)/3)*D^(-(1 : ℝ)/6) := by
  have hg0 : 0 < g := zero_lt_one.trans_le hg
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
  simp (discharger := positivity) only [Real.log_mul,Real.log_rpow,Real.log_pow]
  ring

private theorem second_identity (g D C : ℝ) (hg : 1 ≤ g) (hD : 1 ≤ D) (hC : 1 ≤ C) :
    D^9*g^7*C^((13 : ℝ)/2)*(g*D*C)^((10 : ℝ)/3) =
      (g*D*C)^((10 : ℝ)-1/6)*g^((1 : ℝ)/2)*D^((5 : ℝ)/2) := by
  have hg0 : 0 < g := zero_lt_one.trans_le hg
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
  simp (discharger := positivity) only [Real.log_mul,Real.log_rpow,Real.log_pow]
  ring

/-- The comparison constants two and eight are absorbed into one fixed
constant before all scales and masses. The complementary estimate retains
both supplied alternatives, with coefficient one in `E ≤ D^9*W`. -/
theorem exists_bound (δ KJ KW KE : ℝ) (hδ : 0 ≤ δ)
    (hKJ : 1 ≤ KJ) (hKW : 1 ≤ KW) (hKE : 1 ≤ KE) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ g D C Q : ℝ,
      1 ≤ g → 1 ≤ D → 1 ≤ C → 1 ≤ Q →
      g*D*C ≤ 2*Q → Q ≤ 8*g*D*C → ∀ J W E : ℝ,
      0 ≤ J → 0 ≤ W → 0 ≤ E →
      J ≤ KJ*g^((28 : ℝ)/3)*C^((121 : ℝ)/12+δ)*D^((10 : ℝ)/3) →
      W ≤ KW*g^7*C^((32 : ℝ)/5+δ)*Q^((10 : ℝ)/3) →
      E ≤ KE*g^((28 : ℝ)/3)*C^(10+δ)*D^((59 : ℝ)/6) →
      E ≤ D^9*W →
      E+D^((13 : ℝ)/2)*J^((2 : ℝ)/3)*W^((1 : ℝ)/3) ≤
        K*Q^((10 : ℝ)-1/96+δ) := by
  let a : ℝ := 10-1/96
  let b8 : ℝ := (8 : ℝ)^((10 : ℝ)/3)
  let L : ℝ := KJ+KW+KE
  let B : ℝ := L*b8
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hb8 : 1 ≤ b8 := Real.one_le_rpow (by norm_num) (by norm_num)
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le hL hb8
  have hLB : L ≤ B := le_mul_of_one_le_right (zero_le_one.trans hL) hb8
  have hKJB : KJ ≤ B := (by dsimp [L]; linarith : KJ ≤ L).trans hLB
  have hKEB : KE ≤ B := (by dsimp [L]; linarith : KE ≤ L).trans hLB
  have hKWB : KW*b8 ≤ B := mul_le_mul_of_nonneg_right
    (by dsimp [L]; linarith : KW ≤ L) (zero_le_one.trans hb8)
  have haδ : 0 ≤ a+δ := by dsimp [a]; linarith
  have htwo : 1 ≤ (2 : ℝ)^(a+δ) := Real.one_le_rpow (by norm_num) haδ
  refine ⟨2*B*(2 : ℝ)^(a+δ),
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by norm_num) hB) htwo,?_⟩
  intro g D C Q hg hD hC hQ hlo hhi J W E hJ0 hW0 hE0 hJ hW hE hEW
  let Q₀ : ℝ := g*D*C
  let U : ℝ := B*Q₀^δ
  let J₀ : ℝ := g^((28 : ℝ)/3)*C^((121 : ℝ)/12)*D^((10 : ℝ)/3)
  let W₀ : ℝ := g^7*C^((32 : ℝ)/5)*Q₀^((10 : ℝ)/3)
  let A₀ : ℝ := Q₀^10*g^(-(2 : ℝ)/3)*D^(-(1 : ℝ)/6)
  let A₁ : ℝ := Q₀^((10 : ℝ)-1/6)*g^((1 : ℝ)/2)*D^((5 : ℝ)/2)
  have hg0 : 0 < g := zero_lt_one.trans_le hg
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hQ₀ : 1 ≤ Q₀ :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hg hD) hC
  have hQ₀pos : 0 < Q₀ := zero_lt_one.trans_le hQ₀
  have hCQ : C ≤ Q₀ := le_mul_of_one_le_left hC0.le
    (one_le_mul_of_one_le_of_one_le hg hD)
  have hCδ : C^δ ≤ Q₀^δ := Real.rpow_le_rpow hC0.le hCQ hδ
  have hU0 : 0 ≤ U := by dsimp [U]; positivity
  have hJ₀ : 0 ≤ J₀ := by dsimp [J₀]; positivity
  have hW₀ : 0 ≤ W₀ := by dsimp [W₀]; positivity
  have hA₀ : 0 ≤ A₀ := by dsimp [A₀]; positivity
  have hA₁ : 0 ≤ A₁ := by dsimp [A₁]; positivity
  have hcoef (c : ℝ) (hc : c ≤ B) : c*C^δ ≤ U :=
    mul_le_mul hc hCδ (Real.rpow_nonneg hC0.le _) (zero_le_one.trans hB)
  have hJ' : J ≤ U*J₀ := by
    calc
      J ≤ KJ*g^((28 : ℝ)/3)*C^((121 : ℝ)/12+δ)*D^((10 : ℝ)/3) := hJ
      _ = (KJ*C^δ)*J₀ := by rw [Real.rpow_add hC0]; dsimp [J₀]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hcoef KJ hKJB) hJ₀
  have hQhigh : Q ≤ 8*Q₀ := by simpa only [Q₀,mul_assoc] using hhi
  have hQpow : Q^((10 : ℝ)/3) ≤ b8*Q₀^((10 : ℝ)/3) := by
    have ht := Real.rpow_le_rpow hQpos.le hQhigh (by norm_num : (0 : ℝ) ≤ 10/3)
    simpa only [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) hQ₀pos.le,b8] using ht
  have hW' : W ≤ U*W₀ := by
    calc
      W ≤ KW*g^7*C^((32 : ℝ)/5+δ)*Q^((10 : ℝ)/3) := hW
      _ ≤ KW*g^7*C^((32 : ℝ)/5+δ)*(b8*Q₀^((10 : ℝ)/3)) :=
        mul_le_mul_of_nonneg_left hQpow (by positivity)
      _ = (KW*b8*C^δ)*W₀ := by rw [Real.rpow_add hC0]; dsimp [W₀]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hcoef (KW*b8) hKWB) hW₀
  have haeq : g^((28 : ℝ)/3)*C^10*D^((59 : ℝ)/6) = A₀ :=
    first_identity g D C hg hD hC
  have hE' : E ≤ U*A₀ := by
    calc
      E ≤ KE*g^((28 : ℝ)/3)*C^(10+δ)*D^((59 : ℝ)/6) := hE
      _ = (KE*C^δ)*A₀ := by
        rw [← haeq,Real.rpow_add hC0]
        simp only [Real.rpow_ofNat]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hcoef KE hKEB) hA₀
  have hE'' : E ≤ U*A₁ := by
    have hc := Real.rpow_le_rpow_of_exponent_le hC (by norm_num : (32 : ℝ)/5 ≤ 13/2)
    calc
      E ≤ D^9*W := hEW
      _ ≤ D^9*(U*W₀) := mul_le_mul_of_nonneg_left hW' (pow_nonneg hD0.le _)
      _ = U*(D^9*g^7*C^((32 : ℝ)/5)*Q₀^((10 : ℝ)/3)) := by dsimp [W₀]; ring
      _ ≤ U*(D^9*g^7*C^((13 : ℝ)/2)*Q₀^((10 : ℝ)/3)) := by
        apply mul_le_mul_of_nonneg_left _ hU0
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by positivity)) (by positivity)
      _ = U*A₁ := congrArg (U*·) (second_identity g D C hg hD hC)
  have hEbound : E ≤ U*Q₀^a := by
    have heq : E = E^((15 : ℝ)/16)*E^((1 : ℝ)/16) := by
      rw [← Real.rpow_add_of_nonneg hE0 (by norm_num) (by norm_num)]
      norm_num
    calc
      E = E^((15 : ℝ)/16)*E^((1 : ℝ)/16) := heq
      _ ≤ (U*A₀)^((15 : ℝ)/16)*(U*A₁)^((1 : ℝ)/16) :=
        mul_le_mul (Real.rpow_le_rpow hE0 hE' (by norm_num))
          (Real.rpow_le_rpow hE0 hE'' (by norm_num)) (Real.rpow_nonneg hE0 _)
          (Real.rpow_nonneg (mul_nonneg hU0 hA₀) _)
      _ = U*(A₀^((15 : ℝ)/16)*A₁^((1 : ℝ)/16)) :=
        scaled_product U A₀ A₁ _ _ hU0 hA₀ hA₁ (by norm_num) (by norm_num) (by norm_num)
      _ ≤ U*Q₀^a := mul_le_mul_of_nonneg_left
        (PlanAlphaMixedNumerics.complement_interpolation_le Q₀ g D hQ₀ hg hD) hU0
  have hHbound : D^((13 : ℝ)/2)*J^((2 : ℝ)/3)*W^((1 : ℝ)/3) ≤ U*Q₀^a := by
    calc
      _ = D^((13 : ℝ)/2)*(J^((2 : ℝ)/3)*W^((1 : ℝ)/3)) := by ring
      _ ≤ D^((13 : ℝ)/2)*((U*J₀)^((2 : ℝ)/3)*(U*W₀)^((1 : ℝ)/3)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (Real.rpow_le_rpow hJ0 hJ' (by norm_num))
            (Real.rpow_le_rpow hW0 hW' (by norm_num)) (Real.rpow_nonneg hW0 _)
            (Real.rpow_nonneg (mul_nonneg hU0 hJ₀) _)) (Real.rpow_nonneg hD0.le _)
      _ = U*(D^((13 : ℝ)/2)*J₀^((2 : ℝ)/3)*W₀^((1 : ℝ)/3)) := by
        rw [scaled_product U J₀ W₀ _ _ hU0 hJ₀ hW₀ (by norm_num) (by norm_num) (by norm_num)]
        ring
      _ ≤ U*Q₀^a := mul_le_mul_of_nonneg_left
        (PlanAlphaMixedNumerics.holder_le Q₀ g D C hg hD hC rfl) hU0
  have hQlow : Q₀ ≤ 2*Q := hlo
  have hQtransfer := Real.rpow_le_rpow hQ₀pos.le hQlow haδ
  calc
    E+D^((13 : ℝ)/2)*J^((2 : ℝ)/3)*W^((1 : ℝ)/3) ≤ U*Q₀^a+U*Q₀^a :=
      add_le_add hEbound hHbound
    _ = 2*B*Q₀^(a+δ) := by rw [Real.rpow_add hQ₀pos]; dsimp [U]; ring
    _ ≤ 2*B*(2*Q)^(a+δ) := mul_le_mul_of_nonneg_left hQtransfer (by positivity)
    _ = _ := by rw [Real.mul_rpow (by norm_num) hQpos.le]; dsimp [a]; ring

end CubicTenVariables.PlanAlphaBlockNumerics
