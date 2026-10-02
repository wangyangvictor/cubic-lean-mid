import CubicTenVariables.FiniteFieldCoprimeCommonZeroCount
import CubicTenVariables.SingularCubicProjectionCoprime
import CubicTenVariables.SingularCubicProjectionCount
import CubicTenVariables.CubicSmallSingularPointCount

/-! Uniform singular-point projection counts over every finite field.
The actual rational singular point remains explicit; its existence is not
inferred from geometric singularity. No point-count literature is needed
for the projection branch. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.FiniteFieldCubicSingularPointCount
open MvPolynomial HessianTheorem11 CubicSingularQuotient
open SingularCubicLinearFibers SingularCubicProjectionCount

/-- One constant precedes every finite field and every cubic with the
specified singular point and relatively prime projection equations. -/
theorem exists_bound_of_coprime (n : ℕ) (hn : 2 ≤ n) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (K : Type) [Field K] [Fintype K]
      (F : MvPolynomial (Fin (n+1)) K), F.IsHomogeneous 3 →
      (2 : K) ≠ 0 → (3 : K) ≠ 0 →
      Literature.GeometricallyNonconicalCubic F →
      ∀ (z : Fin (n+1) → K), eval z F=0 → gradient F z=0 →
      ∀ (i : Fin (n+1)), z i ≠ 0 →
      IsRelPrime (zeroSection i (quadraticPolynomial F z)) (zeroSection i F) →
      |(Literature.affineZeroCount F : ℝ)-(Fintype.card K : ℝ)^n| ≤
        B*((Fintype.card K : ℝ)-1)*(Fintype.card K : ℝ)^(n-2) := by
  classical
  obtain ⟨A,hA,hcount⟩ := FiniteFieldCoprimeCommonZeroCount.exists_quadratic_cubic_bound n hn
  have hB : 1 ≤ 2*((A : ℝ)+2) := by
    have ha : (0 : ℝ) ≤ A := by positivity
    linarith
  refine ⟨2*((A : ℝ)+2),hB,?_⟩
  intro K _ _ F hF h2 h3 hNC z hzero hsing i hi hcop
  have hI := hcount K (zeroSection i (quadraticPolynomial F z)) (zeroSection i F)
    (section_quadratic_ne_zero F hF h2 h3 hNC z hzero hsing i hi)
    (homogeneous_section i _ (homogeneous_quadraticPolynomial F hF z)).totalDegree_le
    (homogeneous_section i F hF).totalDegree_le hcop
  have hI' : (Nat.card {y : Fin n → K //
      eval y (zeroSection i (quadraticPolynomial F z))=0 ∧ eval y (zeroSection i F)=0} : ℝ) ≤
      (A : ℝ)*(Fintype.card K : ℝ)^(n-2) := by
    simp only [Nat.card_eq_fintype_card] at hI ⊢
    exact_mod_cast hI
  have hb := bound_of_common_zero_bound hn F hF h2 h3 hNC z hzero hsing i hi A hI'
  have hp2 : (2 : ℝ) ≤ Fintype.card K := by exact_mod_cast Nat.succ_le_of_lt (Fintype.one_lt_card (α := K))
  have hpow : (Fintype.card K : ℝ)^(n-1)=(Fintype.card K : ℝ)*(Fintype.card K : ℝ)^(n-2) := by
    rw [← pow_succ']
    congr 1
    omega
  apply hb.trans
  rw [hpow]
  calc
    _ = ((A : ℝ)+2)*(Fintype.card K : ℝ)*(Fintype.card K : ℝ)^(n-2) := by ring
    _ ≤ ((A : ℝ)+2)*(2*((Fintype.card K : ℝ)-1))*(Fintype.card K : ℝ)^(n-2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) (by positivity)
    _ = _ := by ring


/-- A uniform finite-field cubic bound at a supplied nonzero singular zero.
Only the ordinary cubic hypotheses and that actual zero remain. -/
theorem exists_bound (n : ℕ) (hn : 2 ≤ n) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (K : Type) [Field K] [Fintype K]
      (F : MvPolynomial (Fin (n+1)) K), F.IsHomogeneous 3 →
      (2 : K) ≠ 0 → (3 : K) ≠ 0 →
      Literature.GeometricallyIntegralForm F →
      Literature.GeometricallyNonconicalCubic F →
      (∃ z : Fin (n+1) → K, z ≠ 0 ∧ eval z F=0 ∧ gradient F z=0) →
      |(Literature.affineZeroCount F : ℝ)-(Fintype.card K : ℝ)^n| ≤
        B*((Fintype.card K : ℝ)-1)*(Fintype.card K : ℝ)^(n-2) := by
  classical
  obtain ⟨B,hB,h⟩ := exists_bound_of_coprime n hn
  refine ⟨B,hB,?_⟩
  intro K _ _ F hF h2 h3 hI hNC hs
  obtain ⟨z,hz,hzero,hsing⟩ := hs
  obtain ⟨i,hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra! he
    exact hz (funext he)
  have hQ := SingularCubicProjectionCount.section_quadratic_ne_zero
    F hF h2 h3 hNC z hzero hsing i hi
  exact h K F hF h2 h3 hNC z hzero hsing i hi
    (SingularCubicProjectionCoprime.of_geometricallyIntegral F hF hI z hzero hsing i hi hQ)

/-- The nine-variable instance used for cubic hyperplane sections. -/
theorem exists_nine_variable_bound :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (K : Type) [Field K] [Fintype K]
      (F : MvPolynomial (Fin 9) K), F.IsHomogeneous 3 →
      (2 : K) ≠ 0 → (3 : K) ≠ 0 →
      Literature.GeometricallyIntegralForm F →
      Literature.GeometricallyNonconicalCubic F →
      (∃ z : Fin 9 → K, z ≠ 0 ∧ eval z F=0 ∧ gradient F z=0) →
      |(Literature.affineZeroCount F : ℝ)-(Fintype.card K : ℝ)^8| ≤
        B*((Fintype.card K : ℝ)-1)*(Fintype.card K : ℝ)^6 :=
  exists_bound 8 (by decide)

/-- The two currently closed nine-variable branches share one constant.
Hooley--Katz is needed only in the small-singular-locus branch. -/
theorem exists_nine_variable_bound_of_small_singular_or_rational_point
    (hk : Literature.HooleyKatzPointCount) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (K : Type) [Field K] [Fintype K]
      (F : MvPolynomial (Fin 9) K), F.IsHomogeneous 3 →
      (2 : K) ≠ 0 → (3 : K) ≠ 0 →
      Literature.GeometricallyIntegralForm F →
      Literature.GeometricallyNonconicalCubic F →
      (ReducedGaussSection.coordinateDimension (Literature.geometricSingularCone F) ≤
        (5 : WithBot ℕ∞) ∨
        ∃ z : Fin 9 → K, z ≠ 0 ∧ eval z F=0 ∧ gradient F z=0) →
      |(Literature.affineZeroCount F : ℝ)-(Fintype.card K : ℝ)^8| ≤
        B*((Fintype.card K : ℝ)-1)*(Fintype.card K : ℝ)^6 := by
  obtain ⟨C,hC,hsmall⟩ := CubicSmallSingularPointCount.exists_nine_variable_bound hk
  obtain ⟨D,hD,hrat⟩ := exists_nine_variable_bound
  refine ⟨max C D,hC.trans (le_max_left _ _),?_⟩
  intro K _ _ F hF h2 h3 hI hNC hcase
  have hp1 : (1 : ℝ) ≤ Fintype.card K := by exact_mod_cast Nat.le_of_lt (Fintype.one_lt_card (α := K))
  have hmono (a b : ℝ) (hab : a ≤ b) :
      a*((Fintype.card K : ℝ)-1)*(Fintype.card K : ℝ)^6 ≤ b*((Fintype.card K : ℝ)-1)*(Fintype.card K : ℝ)^6 :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hab (sub_nonneg.mpr hp1)) (by positivity)
  rcases hcase with hs | hs
  · have h := hsmall K F hF hI hs
    exact h.trans (hmono _ _ (le_max_left _ _))
  · exact (hrat K F hF h2 h3 hI hNC hs).trans (hmono _ _ (le_max_right _ _))


end CubicTenVariables.FiniteFieldCubicSingularPointCount
