import CubicTenVariables.IntegralNormalizationEvaluation
import CubicTenVariables.NormalizedGeometricSieve
import CubicTenVariables.GeometricSieveRescaling

/-! The translated composite sieve for original integral models of fixed
homogeneous cones. Every modulus and equation is literal, including bad primes.
No external geometric or analytic counting assertion is an input. -/
noncomputable section
namespace CubicTenVariables.TranslatedGeometricSieve
open MvPolynomial IntegralLinearNormalization IntegralCoordinateBoxes
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- A squarefree modulus in the closed dyadic interval, prime to the given
progression modulus, on which all original integral equations vanish. -/
def Admissible (J : Ideal (MvPolynomial (Fin n) ℤ)) (m : ℕ) (S0 : ℝ)
    (x : Fin n → ℤ) : Prop :=
  ∃ q : ℕ, Squarefree q ∧ q.Coprime m ∧ S0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ 2*S0 ∧
    ∀ f ∈ J, (q : ℤ) ∣ eval x f

/-- One fixed coordinate certificate yields the source admissible-point
bound, uniformly in the real center, radius, progression and dyadic scale. -/
theorem exists_admissible_bound_of_certificate
    {J : Ideal (MvPolynomial (Fin n) ℤ)} {r : ℕ} (D : Certificate J r)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c K : ℝ, 1 ≤ c ∧ 1 ≤ K ∧
      ∀ (u : Fin n → ℝ) (L : ℝ), 1 ≤ L → ∀ (m : ℕ), 0 < m →
      ∀ (b : Fin n → ℤ) (S0 : ℝ), c*(1+L/(m : ℝ)) ≤ S0 →
      ∀ S : Finset (Fin n → ℤ),
      (∀ x ∈ S, ∀ i, |(x i : ℝ)-u i| ≤ L) →
      (∀ x ∈ S, ∀ i, (m : ℤ) ∣ x i-b i) →
      (∀ x ∈ S, Admissible J m S0 x) →
      (S.card : ℝ) ≤ K*(L*S0+‖u‖)^ε*(1+L/(m : ℝ))^(r+1) := by
  classical
  let a : ℝ := coefficientBound D.matrix
  have ha : 1 ≤ a := by
    dsimp only [a]
    exact_mod_cast one_le_coefficientBound D.matrix
  have hlead : (D.leading : ℤ) ≠ 0 := by exact_mod_cast D.leading_pos.ne'
  obtain ⟨K,hK,hbound⟩ := NormalizedGeometricSieve.exists_bound D.base D.polynomial
    (fun i => (D.polynomial i).natDegree) D.degreeBound (D.leading : ℤ)
    D.degreeBound_pos hlead (fun i _ => D.degree_le i)
    (fun i _ => IntegralNormalizationEvaluation.certificate_coefficient D i) (ε/2) (by positivity)
  let B : ℝ := a^(ε/2)*2^(ε/2)*(4*a)^(r+1)
  have hB : 1 ≤ B := by
    apply one_le_mul_of_one_le_of_one_le
    · exact one_le_mul_of_one_le_of_one_le
        (Real.one_le_rpow ha (by positivity)) (Real.one_le_rpow (by norm_num) (by positivity))
    · exact one_le_pow₀ (by linarith : 1 ≤ 4*a)
  refine ⟨a,K*B,ha,one_le_mul_of_one_le_of_one_le hK hB,?_⟩
  intro u L hL m hm b S0 hS0 S hbox hres hadm
  letI : NeZero m := ⟨hm.ne'⟩
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hratio : 0 ≤ L/(m : ℝ) := div_nonneg (by linarith) hmR.le
  have hS01 : 1 ≤ S0 := by nlinarith
  have hL' : 1 ≤ a*L := one_le_mul_of_one_le_of_one_le ha hL
  have hS0' : 1+(a*L)/(m : ℝ) ≤ S0 := by
    have he : (a*L)/(m : ℝ)=a*(L/(m : ℝ)) := by ring
    rw [he]
    nlinarith
  have h := hbound ((realMatrix D.matrix).mulVec u) (a*L) hL' m
    (D.matrix.mulVec b) S0 hS0' (S.image D.matrix.mulVec) (by
      intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      exact transformed_box D.matrix x u L (by linarith) (hbox x hx)) (by
      intro y hy i
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      apply sub_eq_zero.mp
      rw [← Int.cast_sub]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
        (transformed_progression D.matrix x b m (hres x hx) i)) (by
      intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨q,hq,hcop,hlo,hhi,hzero⟩ := hadm x hx
      refine ⟨q,hq,hcop,hlo,hhi,?_⟩
      intro i
      exact IntegralNormalizationEvaluation.certificate_divisibility D x q hzero i)
  rw [Finset.card_image_of_injective _ D.matrix_injective] at h
  have hscale := GeometricSieveRescaling.estimate a L ‖u‖ ‖(realMatrix D.matrix).mulVec u‖
    (m : ℝ) S0 ε D.parameterCount r ha hL (norm_nonneg _) (norm_nonneg _)
    (transformed_center_norm D.matrix u) hmR hS01 hε D.parameterCount_le
  calc
    (S.card : ℝ) ≤ K*((a*L+‖(realMatrix D.matrix).mulVec u‖)^(ε/2)*
        (2*S0)^(ε/2)*(4*(a*L)/(m : ℝ)+3)^(D.parameterCount+1)) := by
      convert h using 1
      ring
    _ ≤ K*(B*(L*S0+‖u‖)^ε*(1+L/(m : ℝ))^(r+1)) :=
      mul_le_mul_of_nonneg_left hscale (by linarith)
    _ = (K*B)*(L*S0+‖u‖)^ε*(1+L/(m : ℝ))^(r+1) := by ring

/-- The needed homogeneous-cone application constructs normalization data
internally; only properness, homogeneity and the actual quotient dimension
are mathematical hypotheses. -/
theorem exists_admissible_bound (J : Ideal (MvPolynomial (Fin n) ℤ))
    (hproper : rationalIdeal J ≠ ⊤)
    (hhom : (rationalIdeal J).IsHomogeneous (homogeneousSubmodule (Fin n) ℚ))
    (r : ℕ) (hdim : ringKrullDim (MvPolynomial (Fin n) ℚ ⧸ rationalIdeal J) ≤
      (r : WithBot ℕ∞)) (ε : ℝ) (hε : 0 < ε) :
    ∃ c K : ℝ, 1 ≤ c ∧ 1 ≤ K ∧
      ∀ (u : Fin n → ℝ) (L : ℝ), 1 ≤ L → ∀ (m : ℕ), 0 < m →
      ∀ (b : Fin n → ℤ) (S0 : ℝ), c*(1+L/(m : ℝ)) ≤ S0 →
      ∀ S : Finset (Fin n → ℤ),
      (∀ x ∈ S, ∀ i, |(x i : ℝ)-u i| ≤ L) →
      (∀ x ∈ S, ∀ i, (m : ℤ) ∣ x i-b i) →
      (∀ x ∈ S, Admissible J m S0 x) →
      (S.card : ℝ) ≤ K*(L*S0+‖u‖)^ε*(1+L/(m : ℝ))^(r+1) := by
  obtain ⟨D⟩ := exists_certificate J hproper hhom r hdim
  exact exists_admissible_bound_of_certificate D ε hε

end CubicTenVariables.TranslatedGeometricSieve
