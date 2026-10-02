import CubicTenVariables.LocalizedZeroCRT

/-! Exact CRT for the literal localized complete sums at every frequency.
The inverse of the opposite ambient modulus twists each local frequency.
No homogeneity or scalar symmetry of the restriction is assumed here. -/
noncomputable section
namespace CubicTenVariables.LocalizedFourierCRT
open MvPolynomial CRTCharacters PrimeSumAdapter PrimitiveCharacterCRT WeightedCRTAdapters
open LocalizedZeroCRT
open scoped BigOperators Classical

local instance lcmNeZero (a b : ℕ) [NeZero a] [NeZero b] : NeZero (Nat.lcm a b) :=
  ⟨Nat.lcm_ne_zero (NeZero.ne a) (NeZero.ne b)⟩

/-- The primitive polynomial character and the ambient Fourier character
are kept separate, as in the literal localized complete sum. -/
def residueFourierSum {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (q A W : ℕ) [NeZero q] [NeZero A] (hqA : q ∣ A) (hWA : W ∣ A)
    (Ω : Set (Fin n → ZMod W)) (v : Fin n → ZMod A) : ℂ :=
  ∑ x : Fin n → ZMod A,
    if (fun i => ZMod.castHom hWA (ZMod W) (x i)) ∈ Ω then
      characterSum q (eval₂ (Int.castRingHom (ZMod q))
        (fun i => ZMod.castHom hqA (ZMod q) (x i)) F) *
          ZMod.stdAddChar (∑ i, v i * x i)
    else 0

@[simp] theorem residueFourierSum_zero {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (q A W : ℕ) [NeZero q] [NeZero A] (hqA : q ∣ A) (hWA : W ∣ A)
    (Ω : Set (Fin n → ZMod W)) :
    residueFourierSum F q A W hqA hWA Ω 0 = residueSum F q A W hqA hWA Ω := by
  simp [residueFourierSum, residueSum]

theorem residueFourierSum_congr_modulus {n q A B W : ℕ}
    [NeZero q] [NeZero A] [NeZero B] (F : MvPolynomial (Fin n) ℤ)
    (hAB : A = B) (hqA : q ∣ A) (hWA : W ∣ A) (hqB : q ∣ B) (hWB : W ∣ B)
    (Ω : Set (Fin n → ZMod W)) (v : Fin n → ZMod A) :
    residueFourierSum F q A W hqA hWA Ω v =
      residueFourierSum F q B W hqB hWB Ω (hAB ▸ v) := by
  subst B
  rfl

theorem residueFourierSum_congr_modulus_int {n q A B W : ℕ}
    [NeZero q] [NeZero A] [NeZero B] (F : MvPolynomial (Fin n) ℤ)
    (hAB : A = B) (hqA : q ∣ A) (hWA : W ∣ A) (hqB : q ∣ B) (hWB : W ∣ B)
    (Ω : Set (Fin n → ZMod W)) (v : Fin n → ℤ) :
    residueFourierSum F q A W hqA hWA Ω (fun i => (v i : ZMod A)) =
      residueFourierSum F q B W hqB hWB Ω (fun i => (v i : ZMod B)) := by
  subst B
  rfl

/-- Exact adapter, including q = 1, from the manuscript's integer
representatives to the intrinsic residue Fourier sum. -/
theorem localized_eq_residueFourierSum {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (q W : ℕ) [NeZero q] [NeZero W] (Ω : Set (Fin n → ZMod W))
    (v : Fin n → ℤ) :
    localizedCompleteCubicSum F q W Ω v =
      residueFourierSum F q (Nat.lcm q W) W
        (Nat.dvd_lcm_left q W) (Nat.dvd_lcm_right q W) Ω
        (fun i => (v i : ZMod (Nat.lcm q W))) := by
  have hswap : localizedCompleteCubicSum F q W Ω v =
      ∑ x : Fin n → Fin (Nat.lcm q W),
        if integerResidue W (fun i => ((x i).val : ℤ)) ∈ Ω then
          (∑ a : Fin q, if Nat.Coprime a.val q then
            residueExponential q ((a.val : ℤ) * eval (fun i => ((x i).val : ℤ)) F)
            else 0) * residueExponential (Nat.lcm q W) (∑ i, v i * (x i).val)
        else 0 := by
    unfold localizedCompleteCubicSum
    calc
      _ = ∑ x : Fin n → Fin (Nat.lcm q W), ∑ a : Fin q,
          if Nat.Coprime a.val q then
            if integerResidue W (fun i => ((x i).val : ℤ)) ∈ Ω then
              residueExponential q ((a.val : ℤ) * eval (fun i => ((x i).val : ℤ)) F) *
                residueExponential (Nat.lcm q W) (∑ i, v i * (x i).val)
            else 0
          else 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a ha
        split_ifs <;> simp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x hx
        split_ifs with hxΩ
        · simp only [Finset.sum_mul, ite_mul, zero_mul]
        · simp only [ite_self, Finset.sum_const_zero]
  rw [hswap]
  simp_rw [sum_fin_eq]
  unfold residueFourierSum
  apply Fintype.sum_equiv (vectorResidueEquiv (Nat.lcm q W) n)
  intro x
  have hm : integerResidue W (fun i => ((x i).val : ℤ)) =
      fun i => ZMod.castHom (Nat.dvd_lcm_right q W) (ZMod W)
        (vectorResidueEquiv (Nat.lcm q W) n x i) := by
    funext i
    simp only [integerResidue, vectorResidueEquiv_apply, Int.cast_natCast, map_natCast]
  simp only [hm, SmoothResidueLifting.cast_eval_int, vectorResidueEquiv_apply,
    map_natCast, Int.cast_natCast, residueExponential_eq_stdAddChar, Int.cast_sum,
    Int.cast_mul]

/-- CRT for the linear character. The twists use A₁ modulo A₀ and A₀
modulo A₁, not the generally smaller polynomial-character moduli. -/
theorem stdAddChar_dot_crt {n A₀ A₁ : ℕ} [NeZero A₀] [NeZero A₁]
    (hA : A₀.Coprime A₁) (v x : Fin n → ZMod (A₀*A₁)) :
    ZMod.stdAddChar (∑ i, v i*x i) =
      ZMod.stdAddChar (∑ i, ((leftTwist hA : ZMod A₀)*leftProjection hA (v i)) *
        leftProjection hA (x i)) *
      ZMod.stdAddChar (∑ i, ((rightTwist hA : ZMod A₁)*rightProjection hA (v i)) *
        rightProjection hA (x i)) := by
  rw [stdAddChar_crt hA]
  simp only [map_sum, map_mul, Finset.mul_sum, mul_assoc]

/-- Raw CRT for arbitrary polynomial and product restriction, with the
two ambient inverse-modulus frequency twists retained explicitly. -/
theorem residueFourierSum_crt {n q₀ q₁ A₀ A₁ W₀ W₁ : ℕ}
    [NeZero q₀] [NeZero q₁] [NeZero A₀] [NeZero A₁]
    (F : MvPolynomial (Fin n) ℤ) (hq₀ : q₀ ∣ A₀) (hq₁ : q₁ ∣ A₁)
    (hW₀ : W₀ ∣ A₀) (hW₁ : W₁ ∣ A₁) (hA : A₀.Coprime A₁)
    (Ω₀ : Set (Fin n → ZMod W₀)) (Ω₁ : Set (Fin n → ZMod W₁))
    (v : Fin n → ZMod (A₀*A₁)) :
    residueFourierSum F (q₀*q₁) (A₀*A₁) (W₀*W₁) (mul_dvd_mul hq₀ hq₁)
      (mul_dvd_mul hW₀ hW₁)
      (productRestriction ((hA.of_dvd_left hW₀).of_dvd_right hW₁) Ω₀ Ω₁) v =
      residueFourierSum F q₀ A₀ W₀ hq₀ hW₀ Ω₀
        (fun i => (leftTwist hA : ZMod A₀)*leftProjection hA (v i)) *
      residueFourierSum F q₁ A₁ W₁ hq₁ hW₁ Ω₁
        (fun i => (rightTwist hA : ZMod A₁)*rightProjection hA (v i)) := by
  let hq : q₀.Coprime q₁ := (hA.of_dvd_left hq₀).of_dvd_right hq₁
  let hW : W₀.Coprime W₁ := (hA.of_dvd_left hW₀).of_dvd_right hW₁
  unfold residueFourierSum
  calc
    _ = ∑ x : Fin n → ZMod (A₀*A₁),
        (if (fun i => ZMod.castHom hW₀ (ZMod W₀) (leftProjection hA (x i))) ∈ Ω₀ then
          characterSum q₀ (eval₂ (Int.castRingHom (ZMod q₀))
            (fun i => ZMod.castHom hq₀ (ZMod q₀) (leftProjection hA (x i))) F) *
            ZMod.stdAddChar (∑ i, ((leftTwist hA : ZMod A₀)*leftProjection hA (v i)) *
              leftProjection hA (x i)) else 0) *
        (if (fun i => ZMod.castHom hW₁ (ZMod W₁) (rightProjection hA (x i))) ∈ Ω₁ then
          characterSum q₁ (eval₂ (Int.castRingHom (ZMod q₁))
            (fun i => ZMod.castHom hq₁ (ZMod q₁) (rightProjection hA (x i))) F) *
            ZMod.stdAddChar (∑ i, ((rightTwist hA : ZMod A₁)*rightProjection hA (v i)) *
              rightProjection hA (x i)) else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [productRestriction, Set.mem_setOf_eq,
        projection_cast_left hW₀ hW₁ hW hA,
        projection_cast_right hW₀ hW₁ hW hA]
      rw [characterSum_crt hq, stdAddChar_dot_crt hA]
      simp only [map_eval₂_int, projection_cast_left hq₀ hq₁ hq hA,
        projection_cast_right hq₀ hq₁ hq hA]
      split_ifs <;> simp_all
      ring
    _ = _ := sum_crt_product hA
      (fun x : Fin n → ZMod A₀ =>
        if (fun i => ZMod.castHom hW₀ (ZMod W₀) (x i)) ∈ Ω₀ then
          characterSum q₀ (eval₂ (Int.castRingHom (ZMod q₀))
            (fun i => ZMod.castHom hq₀ (ZMod q₀) (x i)) F) *
            ZMod.stdAddChar (∑ i, ((leftTwist hA : ZMod A₀)*leftProjection hA (v i))*x i)
        else 0)
      (fun x : Fin n → ZMod A₁ =>
        if (fun i => ZMod.castHom hW₁ (ZMod W₁) (x i)) ∈ Ω₁ then
          characterSum q₁ (eval₂ (Int.castRingHom (ZMod q₁))
            (fun i => ZMod.castHom hq₁ (ZMod q₁) (x i)) F) *
            ZMod.stdAddChar (∑ i, ((rightTwist hA : ZMod A₁)*rightProjection hA (v i))*x i)
        else 0)

/-- Raw CRT applied to the actual localized complete sum. Each right-hand
frequency is the original integer frequency multiplied by the inverse of
the opposite lcm modulus in the appropriate residue ring. -/
theorem localized_mul_twisted {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (q₀ q₁ W₀ W₁ : ℕ) [NeZero q₀] [NeZero q₁] [NeZero W₀] [NeZero W₁]
    (h : (q₀*W₀).Coprime (q₁*W₁))
    (Ω₀ : Set (Fin n → ZMod W₀)) (Ω₁ : Set (Fin n → ZMod W₁))
    (v : Fin n → ℤ) :
    let hA := (h.of_dvd_left (Nat.lcm_dvd_mul q₀ W₀)).of_dvd_right
      (Nat.lcm_dvd_mul q₁ W₁)
    localizedCompleteCubicSum F (q₀*q₁) (W₀*W₁)
      (productRestriction
        ((h.of_dvd_left (dvd_mul_left W₀ q₀)).of_dvd_right (dvd_mul_left W₁ q₁)) Ω₀ Ω₁) v =
      residueFourierSum F q₀ (Nat.lcm q₀ W₀) W₀
        (Nat.dvd_lcm_left q₀ W₀) (Nat.dvd_lcm_right q₀ W₀) Ω₀
        (fun i => (leftTwist hA : ZMod (Nat.lcm q₀ W₀))*(v i : ZMod (Nat.lcm q₀ W₀))) *
      residueFourierSum F q₁ (Nat.lcm q₁ W₁) W₁
        (Nat.dvd_lcm_left q₁ W₁) (Nat.dvd_lcm_right q₁ W₁) Ω₁
        (fun i => (rightTwist hA : ZMod (Nat.lcm q₁ W₁))*(v i : ZMod (Nat.lcm q₁ W₁))) := by
  dsimp only
  rw [localized_eq_residueFourierSum]
  refine (residueFourierSum_congr_modulus_int F (lcm_coprime_products q₀ q₁ W₀ W₁ h)
    _ _ (mul_dvd_mul (Nat.dvd_lcm_left _ _) (Nat.dvd_lcm_left _ _))
    (mul_dvd_mul (Nat.dvd_lcm_right _ _) (Nat.dvd_lcm_right _ _)) _ v).trans ?_
  simpa only [map_intCast] using
    residueFourierSum_crt F (Nat.dvd_lcm_left q₀ W₀) (Nat.dvd_lcm_left q₁ W₁)
      (Nat.dvd_lcm_right q₀ W₀) (Nat.dvd_lcm_right q₁ W₁)
      ((h.of_dvd_left (Nat.lcm_dvd_mul q₀ W₀)).of_dvd_right (Nat.lcm_dvd_mul q₁ W₁))
      Ω₀ Ω₁ (fun i => (v i : ZMod (Nat.lcm q₀ W₀ * Nat.lcm q₁ W₁)))

end CubicTenVariables.LocalizedFourierCRT
