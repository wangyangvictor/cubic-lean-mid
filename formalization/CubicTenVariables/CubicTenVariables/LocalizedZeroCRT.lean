import CubicTenVariables.LocalizedSums
import CubicTenVariables.PrimitiveCharacterCRT
import CubicTenVariables.SmoothResidueLifting

/-! Exact zero-frequency factorization of the actual localized sums.
Restrictions are transported by the genuine CRT projections, and both
the common ambient modulus and the primitive numerator sum are retained. -/
noncomputable section
namespace CubicTenVariables.LocalizedZeroCRT
open MvPolynomial CRTCharacters PrimeSumAdapter PrimitiveCharacterCRT WeightedCRTAdapters
open scoped BigOperators Classical

local instance lcmNeZero (a b : ℕ) [NeZero a] [NeZero b] : NeZero (Nat.lcm a b) :=
  ⟨Nat.lcm_ne_zero (NeZero.ne a) (NeZero.ne b)⟩

def residueSum {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (q A W : ℕ) [NeZero q] [NeZero A] (hqA : q ∣ A) (hWA : W ∣ A)
    (Ω : Set (Fin n → ZMod W)) : ℂ :=
  ∑ x : Fin n → ZMod A,
    if (fun i => ZMod.castHom hWA (ZMod W) (x i)) ∈ Ω then
      characterSum q (eval₂ (Int.castRingHom (ZMod q))
        (fun i => ZMod.castHom hqA (ZMod q) (x i)) F)
    else 0

theorem residueSum_congr_modulus {n q A B W : ℕ}
    [NeZero q] [NeZero A] [NeZero B] (F : MvPolynomial (Fin n) ℤ)
    (hAB : A = B) (hqA : q ∣ A) (hWA : W ∣ A) (hqB : q ∣ B) (hWB : W ∣ B)
    (Ω : Set (Fin n → ZMod W)) :
    residueSum F q A W hqA hWA Ω = residueSum F q B W hqB hWB Ω := by
  subst B
  rfl

private theorem ite_sum_zero {α : Type*} [Fintype α]
    (P : Prop) [Decidable P] (f : α → ℂ) :
    (if P then ∑ x, f x else 0) = ∑ x, if P then f x else 0 := by
  by_cases h : P <;> simp [h]

theorem localized_zero_eq_residueSum {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (q W : ℕ) [NeZero q] [NeZero W] (Ω : Set (Fin n → ZMod W)) :
    localizedCompleteCubicSum F q W Ω 0 =
      residueSum F q (Nat.lcm q W) W (Nat.dvd_lcm_left q W) (Nat.dvd_lcm_right q W) Ω := by
  have hswap : localizedCompleteCubicSum F q W Ω 0 =
      ∑ x : Fin n → Fin (Nat.lcm q W),
        if integerResidue W (fun i => ((x i).val:ℤ)) ∈ Ω then
          ∑ a : Fin q, if Nat.Coprime a.val q then
            residueExponential q ((a.val:ℤ)*eval (fun i => ((x i).val:ℤ)) F) else 0
        else 0 := by
    unfold localizedCompleteCubicSum
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, residueExponential,
      Int.cast_zero, mul_zero, zero_div, Complex.exp_zero, mul_one]
    simp_rw [ite_sum_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs <;> rfl
  rw [hswap]
  simp_rw [sum_fin_eq]
  unfold residueSum
  apply Fintype.sum_equiv (vectorResidueEquiv (Nat.lcm q W) n)
  intro x
  have hm : integerResidue W (fun i => ((x i).val:ℤ)) =
      fun i => ZMod.castHom (Nat.dvd_lcm_right q W) (ZMod W)
        (vectorResidueEquiv (Nat.lcm q W) n x i) := by
    funext i
    simp only [integerResidue, vectorResidueEquiv_apply, Int.cast_natCast, map_natCast]
  simp only [hm, SmoothResidueLifting.cast_eval_int, vectorResidueEquiv_apply,
    map_natCast, Int.cast_natCast]

def productRestriction {n W₀ W₁ : ℕ} (h : W₀.Coprime W₁)
    (Ω₀ : Set (Fin n → ZMod W₀)) (Ω₁ : Set (Fin n → ZMod W₁)) :
    Set (Fin n → ZMod (W₀*W₁)) :=
  {x | (fun i => leftProjection h (x i)) ∈ Ω₀ ∧
    (fun i => rightProjection h (x i)) ∈ Ω₁}

theorem productRestriction_eq_cast {n W₀ W₁ : ℕ} (h : W₀.Coprime W₁)
    (Ω₀ : Set (Fin n → ZMod W₀)) (Ω₁ : Set (Fin n → ZMod W₁)) :
    productRestriction h Ω₀ Ω₁ =
      {x | (fun i => ZMod.castHom (dvd_mul_right W₀ W₁) (ZMod W₀) (x i)) ∈ Ω₀ ∧
        (fun i => ZMod.castHom (dvd_mul_left W₁ W₀) (ZMod W₁) (x i)) ∈ Ω₁} := by
  have hl : leftProjection h = ZMod.castHom (dvd_mul_right W₀ W₁) (ZMod W₀) :=
    Subsingleton.elim _ _
  have hr : rightProjection h = ZMod.castHom (dvd_mul_left W₁ W₀) (ZMod W₁) :=
    Subsingleton.elim _ _
  simp only [productRestriction, hl, hr]

theorem projection_cast_left {a b c d : ℕ} (hac : a ∣ c) (hbd : b ∣ d)
    (hab : a.Coprime b) (hcd : c.Coprime d) (x : ZMod (c*d)) :
    leftProjection hab (ZMod.castHom (mul_dvd_mul hac hbd) (ZMod (a*b)) x) =
      ZMod.castHom hac (ZMod a) (leftProjection hcd x) := by
  exact congrArg (fun f : ZMod (c*d) →+* ZMod a => f x)
    (Subsingleton.elim
      ((leftProjection hab).comp (ZMod.castHom (mul_dvd_mul hac hbd) (ZMod (a*b))))
      ((ZMod.castHom hac (ZMod a)).comp (leftProjection hcd)))

theorem projection_cast_right {a b c d : ℕ} (hac : a ∣ c) (hbd : b ∣ d)
    (hab : a.Coprime b) (hcd : c.Coprime d) (x : ZMod (c*d)) :
    rightProjection hab (ZMod.castHom (mul_dvd_mul hac hbd) (ZMod (a*b)) x) =
      ZMod.castHom hbd (ZMod b) (rightProjection hcd x) := by
  exact congrArg (fun f : ZMod (c*d) →+* ZMod b => f x)
    (Subsingleton.elim
      ((rightProjection hab).comp (ZMod.castHom (mul_dvd_mul hac hbd) (ZMod (a*b))))
      ((ZMod.castHom hbd (ZMod b)).comp (rightProjection hcd)))

/-- The restriction and the polynomial character split independently at
the actual ambient CRT projections. No degree or unit-invariance is needed. -/
theorem residueSum_crt {n q₀ q₁ A₀ A₁ W₀ W₁ : ℕ}
    [NeZero q₀] [NeZero q₁] [NeZero A₀] [NeZero A₁]
    (F : MvPolynomial (Fin n) ℤ) (hq₀ : q₀ ∣ A₀) (hq₁ : q₁ ∣ A₁)
    (hW₀ : W₀ ∣ A₀) (hW₁ : W₁ ∣ A₁) (hA : A₀.Coprime A₁)
    (Ω₀ : Set (Fin n → ZMod W₀)) (Ω₁ : Set (Fin n → ZMod W₁)) :
    residueSum F (q₀*q₁) (A₀*A₁) (W₀*W₁) (mul_dvd_mul hq₀ hq₁)
      (mul_dvd_mul hW₀ hW₁)
      (productRestriction ((hA.of_dvd_left hW₀).of_dvd_right hW₁) Ω₀ Ω₁) =
      residueSum F q₀ A₀ W₀ hq₀ hW₀ Ω₀ * residueSum F q₁ A₁ W₁ hq₁ hW₁ Ω₁ := by
  let hq : q₀.Coprime q₁ := (hA.of_dvd_left hq₀).of_dvd_right hq₁
  let hW : W₀.Coprime W₁ := (hA.of_dvd_left hW₀).of_dvd_right hW₁
  unfold residueSum
  calc
    _ = ∑ x : Fin n → ZMod (A₀*A₁),
        (if (fun i => ZMod.castHom hW₀ (ZMod W₀) (leftProjection hA (x i))) ∈ Ω₀ then
          characterSum q₀ (eval₂ (Int.castRingHom (ZMod q₀))
            (fun i => ZMod.castHom hq₀ (ZMod q₀) (leftProjection hA (x i))) F) else 0) *
        (if (fun i => ZMod.castHom hW₁ (ZMod W₁) (rightProjection hA (x i))) ∈ Ω₁ then
          characterSum q₁ (eval₂ (Int.castRingHom (ZMod q₁))
            (fun i => ZMod.castHom hq₁ (ZMod q₁) (rightProjection hA (x i))) F) else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [productRestriction, Set.mem_setOf_eq,
        projection_cast_left hW₀ hW₁ hW hA,
        projection_cast_right hW₀ hW₁ hW hA]
      rw [characterSum_crt hq]
      simp only [map_eval₂_int, projection_cast_left hq₀ hq₁ hq hA,
        projection_cast_right hq₀ hq₁ hq hA]
      split_ifs <;> simp_all
    _ = _ := sum_crt_product hA
      (fun x : Fin n → ZMod A₀ =>
        if (fun i => ZMod.castHom hW₀ (ZMod W₀) (x i)) ∈ Ω₀ then
          characterSum q₀ (eval₂ (Int.castRingHom (ZMod q₀))
            (fun i => ZMod.castHom hq₀ (ZMod q₀) (x i)) F) else 0)
      (fun x : Fin n → ZMod A₁ =>
        if (fun i => ZMod.castHom hW₁ (ZMod W₁) (x i)) ∈ Ω₁ then
          characterSum q₁ (eval₂ (Int.castRingHom (ZMod q₁))
            (fun i => ZMod.castHom hq₁ (ZMod q₁) (x i)) F) else 0)

theorem lcm_coprime_products (q₀ q₁ W₀ W₁ : ℕ)
    (h : (q₀*W₀).Coprime (q₁*W₁)) :
    Nat.lcm (q₀*q₁) (W₀*W₁) = Nat.lcm q₀ W₀ * Nat.lcm q₁ W₁ := by
  apply Nat.dvd_antisymm
  · exact Nat.lcm_dvd (mul_dvd_mul (Nat.dvd_lcm_left _ _) (Nat.dvd_lcm_left _ _))
      (mul_dvd_mul (Nat.dvd_lcm_right _ _) (Nat.dvd_lcm_right _ _))
  · apply ((h.of_dvd_left (Nat.lcm_dvd_mul _ _)).of_dvd_right
      (Nat.lcm_dvd_mul _ _)).mul_dvd_of_dvd_of_dvd
    · exact Nat.lcm_dvd
        ((dvd_mul_right q₀ q₁).trans (Nat.dvd_lcm_left _ _))
        ((dvd_mul_right W₀ W₁).trans (Nat.dvd_lcm_right _ _))
    · exact Nat.lcm_dvd
        ((dvd_mul_left q₁ q₀).trans (Nat.dvd_lcm_left _ _))
        ((dvd_mul_left W₁ W₀).trans (Nat.dvd_lcm_right _ _))

/-- Literal factorization for two coprime blocks, including arbitrary
product residue restrictions and the zero or constant polynomial. -/
theorem localized_zero_mul {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (q₀ q₁ W₀ W₁ : ℕ) [NeZero q₀] [NeZero q₁] [NeZero W₀] [NeZero W₁]
    (h : (q₀*W₀).Coprime (q₁*W₁))
    (Ω₀ : Set (Fin n → ZMod W₀)) (Ω₁ : Set (Fin n → ZMod W₁)) :
    localizedCompleteCubicSum F (q₀*q₁) (W₀*W₁)
      (productRestriction
        ((h.of_dvd_left (dvd_mul_left W₀ q₀)).of_dvd_right (dvd_mul_left W₁ q₁)) Ω₀ Ω₁) 0 =
      localizedCompleteCubicSum F q₀ W₀ Ω₀ 0 * localizedCompleteCubicSum F q₁ W₁ Ω₁ 0 := by
  rw [localized_zero_eq_residueSum, localized_zero_eq_residueSum,
    localized_zero_eq_residueSum]
  refine (residueSum_congr_modulus F (lcm_coprime_products q₀ q₁ W₀ W₁ h)
    _ _ (mul_dvd_mul (Nat.dvd_lcm_left _ _) (Nat.dvd_lcm_left _ _))
    (mul_dvd_mul (Nat.dvd_lcm_right _ _) (Nat.dvd_lcm_right _ _)) _).trans ?_
  exact residueSum_crt F (Nat.dvd_lcm_left _ _) (Nat.dvd_lcm_left _ _)
    (Nat.dvd_lcm_right _ _) (Nat.dvd_lcm_right _ _)
    ((h.of_dvd_left (Nat.lcm_dvd_mul _ _)).of_dvd_right (Nat.lcm_dvd_mul _ _)) Ω₀ Ω₁

/-- Exact factorization after the genuine least-common-multiple
normalizations. Neither factor at q=1 is replaced by one. -/
theorem localized_seriesTerm_mul {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (q₀ q₁ W₀ W₁ : ℕ) [NeZero q₀] [NeZero q₁] [NeZero W₀] [NeZero W₁]
    (h : (q₀*W₀).Coprime (q₁*W₁))
    (Ω₀ : Set (Fin n → ZMod W₀)) (Ω₁ : Set (Fin n → ZMod W₁)) :
    localizedSingularSeriesTerm F (W₀*W₁)
      (productRestriction
        ((h.of_dvd_left (dvd_mul_left W₀ q₀)).of_dvd_right (dvd_mul_left W₁ q₁)) Ω₀ Ω₁) (q₀*q₁) =
      localizedSingularSeriesTerm F W₀ Ω₀ q₀ * localizedSingularSeriesTerm F W₁ Ω₁ q₁ := by
  simp only [localizedSingularSeriesTerm, if_neg (NeZero.ne q₀), if_neg (NeZero.ne q₁),
    if_neg (NeZero.ne (q₀*q₁))]
  rw [localized_zero_mul F q₀ q₁ W₀ W₁ h Ω₀ Ω₁,
    lcm_coprime_products q₀ q₁ W₀ W₁ h, Nat.cast_mul, mul_pow]
  exact mul_div_mul_comm _ _ _ _

theorem localized_zero_cast_restriction {n W V : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (q : ℕ) (hWV : W = V) (hVW : V ∣ W)
    (Ω : Set (Fin n → ZMod V)) :
    localizedCompleteCubicSum F q W
      {x | (fun i => ZMod.castHom hVW (ZMod V) (x i)) ∈ Ω} 0 =
      localizedCompleteCubicSum F q V Ω 0 := by
  subst W
  simp only [ZMod.castHom_self, RingHom.id_apply]
  rfl

theorem localized_seriesTerm_cast_restriction {n W V : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (q : ℕ) (hWV : W = V) (hVW : V ∣ W)
    (Ω : Set (Fin n → ZMod V)) :
    localizedSingularSeriesTerm F W
      {x | (fun i => ZMod.castHom hVW (ZMod V) (x i)) ∈ Ω} q =
      localizedSingularSeriesTerm F V Ω q := by
  subst W
  simp only [ZMod.castHom_self, RingHom.id_apply]
  rfl

/-- The source's splitting into the fixed localization block and a
coprime unrestricted block, at the actual zero frequency. -/
theorem localized_zero_mul_outside {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (q₀ q₁ W : ℕ) [NeZero q₀] [NeZero q₁] [NeZero W]
    (h : (q₀*W).Coprime q₁) (Ω : Set (Fin n → ZMod W)) :
    localizedCompleteCubicSum F (q₀*q₁) W Ω 0 =
      localizedCompleteCubicSum F q₀ W Ω 0 * completeCubicSum F q₁ 0 := by
  have hh := localized_zero_mul F q₀ q₁ W 1 (by simpa using h) Ω Set.univ
  simp only [productRestriction_eq_cast, Set.mem_univ, and_true,
    localizedCompleteCubicSum_univ_one] at hh
  rw [localized_zero_cast_restriction F (q₀*q₁) (Nat.mul_one W)] at hh
  exact hh

/-- Normalized arithmetic coefficients split with the localization
density preserved, including q₀=1 and q₁=1. -/
theorem localized_seriesTerm_mul_outside {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (q₀ q₁ W : ℕ) [NeZero q₀] [NeZero q₁] [NeZero W]
    (h : (q₀*W).Coprime q₁) (Ω : Set (Fin n → ZMod W)) :
    localizedSingularSeriesTerm F W Ω (q₀*q₁) =
      localizedSingularSeriesTerm F W Ω q₀ * singularSeriesTerm F q₁ := by
  have hh := localized_seriesTerm_mul F q₀ q₁ W 1 (by simpa using h) Ω Set.univ
  simp only [productRestriction_eq_cast, Set.mem_univ, and_true,
    localizedSingularSeriesTerm_univ_one] at hh
  rw [localized_seriesTerm_cast_restriction F (q₀*q₁) (Nat.mul_one W)] at hh
  exact hh

end CubicTenVariables.LocalizedZeroCRT
