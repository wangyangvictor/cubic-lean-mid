import CubicTenVariables.LocalizedIneligibleWindow
import CubicTenVariables.ResidueMajorantExtraction

/-! Actual prime-power residue majorants and pointwise estimates for
supplied local data. No new local-solubility or literature input is used. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace CubicTenVariables.LocalizedResidueMajorant
open MvPolynomial HessianTheorem11
open FirstLiftSum SecondLiftSum LocalizedFlexibleLifting
open IntegerResidueClasses (residue)
open scoped BigOperators Classical

variable {p : ℕ} [Fact p.Prime] {F : MvPolynomial (Fin 10) ℤ}

/-- A majorant at the ceiling-third modulus with its literal unnormalised
residue mass. One constant precedes the level and every frequency set. -/
theorem exists_majorant (D : PrimeLocalizationData p F) (hF : F.IsHomogeneous 3) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (k : ℕ) (V : Finset (Fin 10 → ℤ)),
      ∃ P : (Fin 10 → ZMod (p^((k+2)/3))) → ℝ,
        (∀ b, 0 ≤ P b) ∧
        (∀ v ∈ V, ‖localizedCompleteCubicSum F (p^k)
          (p^D.modulusExponent) D.residueSet v‖ ≤ P (residue (p^((k+2)/3)) v)) ∧
        (∑ b, P b) ≤ C*(p : ℝ)^((28 : ℝ)/3*k) := by
  obtain ⟨C,hC,hbound⟩ := LocalizedIneligibleWindow.exists_weighted_window_bound D hF
  refine ⟨C,hC,?_⟩
  intro k V
  apply ResidueMajorantExtraction.exists_majorant (p^((k+2)/3)) V
    (fun v => ‖localizedCompleteCubicSum F (p^k) (p^D.modulusExponent) D.residueSet v‖)
    (C*(p : ℝ)^((28 : ℝ)/3*k)) (fun _ _ => norm_nonneg _) (by positivity)
  intro U _
  simpa only [one_mul] using hbound k U (fun _ => 1) (fun _ _ => zero_le_one)

/-- The actual allowed low-digit gradient congruence has at most two
free residue coordinates, uniformly in its unit multiplier and target. -/
theorem gradient_support_card_le (D : PrimeLocalizationData p F) (a b : ℕ)
    (hb : b.Coprime (p^a)) (v : Fin 10 → ℤ) :
    (Finset.univ.filter fun y : Fin 10 → Fin (p^a) =>
      integerResidue (p^D.modulusExponent) (integerVector y) ∈ D.residueSet ∧
      ∀ i, ((p^a : ℕ) : ℤ) ∣ (b : ℤ)*eval (integerVector y) (pderiv i F)+v i).card ≤
      p^(D.modulusExponent+D.lossExponent*D.minorSize)*p^(2*a) := by
  let pred := fun y : Fin 10 → Fin (p^a) =>
    integerResidue (p^D.modulusExponent) (integerVector y) ∈ D.residueSet ∧
    ∀ i, ((p^a : ℕ) : ℤ) ∣ (b : ℤ)*eval (integerVector y) (pderiv i F)+v i
  let u := ZMod.unitOfCoprime b hb
  let T := GradientTotalCount.gradientFiber p F id a
    (PadicUnitOrbit.unitOrbit p D.center D.modulusExponent) u (fun i => -(v i : ZMod (p^a)))
  let encode : {y // pred y} → T := fun y => ⟨(fun i => ((y.1 i).val : ZMod (p^a))),by
    constructor
    · intro i
      have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (y.2.2 i)
      simp only [Int.cast_add,Int.cast_mul,SmoothResidueLifting.cast_eval_int,
        integerVector,Int.cast_natCast] at hz
      simpa only [u,ZMod.coe_unitOfCoprime,IntegralGradientFibers.modularSelectedGradient,
        id_eq] using (eq_neg_of_add_eq_zero_left hz)
    · refine ⟨(fun i => (integerVector y.1 i : ℤ_[p])),
        (D.integerResidue_mem_iff (integerVector y.1)).mp y.2.1,?_⟩
      intro i
      simp only [integerVector,Int.cast_natCast,map_natCast]⟩
  have hinj : Function.Injective encode := by
    intro y z hyz
    apply Subtype.ext
    funext i
    apply Fin.ext
    have he : ((y.1 i).val : ZMod (p^a)) = ((z.1 i).val : ZMod (p^a)) :=
      congrFun (congrArg Subtype.val hyz) i
    have he' := congrArg ZMod.val he
    simpa only [ZMod.val_natCast_of_lt (y.1 i).isLt,
      ZMod.val_natCast_of_lt (z.1 i).isLt] using he'
  have hcard := (Nat.card_le_card_of_injective encode hinj).trans
    (D.full_gradient_bound a u (fun i => -(v i : ZMod (p^a))))
  have hsize : 10-D.minorSize ≤ 2 := by have := D.minorSize_ge_eight; omega
  have hex : D.modulusExponent+D.lossExponent*D.minorSize+a*(10-D.minorSize) ≤
      D.modulusExponent+D.lossExponent*D.minorSize+2*a := by
    nlinarith
  have hpow := Nat.pow_le_pow_right (Fact.out : p.Prime).one_le hex
  have hc : (Finset.univ.filter pred).card ≤
      p^(D.modulusExponent+D.lossExponent*D.minorSize+a*(10-D.minorSize)) := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype] using hcard
  simpa only [pow_add] using hc.trans hpow

/-- Sum the literal low-digit support, using the actual gradient fibers
and a supplied uniform bound for the terminal quadratic maximum. -/
theorem pointwise_lift_bound (D : PrimeLocalizationData p F) (a t : ℕ)
    (v : Fin 10 → ℤ) (Ct : ℝ) (hCt : 0 ≤ Ct)
    (hterm : ∀ y : Fin 10 → Fin (p^a),
      integerResidue (p^D.modulusExponent) (integerVector y) ∈ D.residueSet →
      residueTerminalMax F (p^a) (p^t) y ≤ Ct*(p : ℝ)^(6*t)) :
    pointwiseBound F (p^a) (p^t) (p^D.modulusExponent) D.residueSet v ≤
      (p : ℝ)^(a+t)*((p : ℝ)^(D.modulusExponent+D.lossExponent*D.minorSize)*
        (p : ℝ)^(2*a))*(Ct*(p : ℝ)^(6*t)) := by
  let Q := (p : ℝ)^(D.modulusExponent+D.lossExponent*D.minorSize)*(p : ℝ)^(2*a)
  let B := Ct*(p : ℝ)^(6*t)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hinner (b : Fin (p^a*p^t)) (hb : b.val.Coprime (p^a*p^t)) :
      (∑ y : Fin 10 → Fin (p^a),
        if integerResidue (p^D.modulusExponent) (integerVector y) ∈ D.residueSet then
          if supportCondition F (p^a) (b.val : ℤ) (integerVector y) v then
            residueTerminalMax F (p^a) (p^t) y else 0 else 0) ≤ Q*B := by
    let S := Finset.univ.filter fun y : Fin 10 → Fin (p^a) =>
      integerResidue (p^D.modulusExponent) (integerVector y) ∈ D.residueSet ∧
      ∀ i, ((p^a : ℕ) : ℤ) ∣ (b.val : ℤ)*eval (integerVector y) (pderiv i F)+v i
    have hcard : (S.card : ℝ) ≤ Q := by
      dsimp [S,Q]
      exact_mod_cast gradient_support_card_le D a b.val (hb.of_dvd_right (dvd_mul_right _ _)) v
    calc
      _ ≤ ∑ y : Fin 10 → Fin (p^a),
          if integerResidue (p^D.modulusExponent) (integerVector y) ∈ D.residueSet ∧
            (∀ i, ((p^a : ℕ) : ℤ) ∣ (b.val : ℤ)*eval (integerVector y) (pderiv i F)+v i)
          then B else 0 := by
        apply Finset.sum_le_sum
        intro y _
        by_cases hy : integerResidue (p^D.modulusExponent) (integerVector y) ∈ D.residueSet
        · rw [if_pos hy]
          by_cases hs : supportCondition F (p^a) (b.val : ℤ) (integerVector y) v
          · rw [if_pos hs,if_pos ⟨hy,hs.2⟩]
            exact hterm y hy
          · rw [if_neg hs]
            split_ifs <;> positivity
        · rw [if_neg hy]
          split_ifs <;> positivity
      _ = (S.card : ℝ)*B := by
        simp only [S,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
      _ ≤ Q*B := mul_le_mul_of_nonneg_right hcard hB
  calc
    _ ≤ ∑ _b : Fin (p^a*p^t), Q*B := by
      unfold pointwiseBound
      apply Finset.sum_le_sum
      intro b _
      split_ifs with hb
      · exact hinner b hb
      · positivity
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,
        nsmul_eq_mul,Nat.cast_mul,Nat.cast_pow,pow_add]; dsimp [Q,B]; ring

/-- At high levels, the two gradient-free coordinates and terminal
Hessian kernel give the exact seventh power of the equation modulus. -/
theorem high_pointwise_bound (D : PrimeLocalizationData p F) (hF : F.IsHomogeneous 3)
    (Ct : ℝ) (hCt : 1 ≤ Ct)
    (hker : ∀ y : Fin 10 → ℤ,
      integerResidue (p^D.modulusExponent) y ∈ D.residueSet → ∀ t : ℕ,
      (Nat.card {z : Fin 10 → ZMod (p^t) //
        (hessian (map (Int.castRingHom (ZMod (p^t))) F)
          (fun i => (y i : ZMod (p^t)))).mulVec z = 0} : ℝ) ≤ Ct*(p : ℝ)^(2*t))
    (k : ℕ) (hk : max 3 (3*D.modulusExponent) ≤ k) (v : Fin 10 → ℤ) :
    ‖localizedCompleteCubicSum F (p^k) (p^D.modulusExponent) D.residueSet v‖ ≤
      ((p : ℝ)^(D.modulusExponent+D.lossExponent*D.minorSize)*Ct)*(p : ℝ)^(7*k) := by
  let a := (k+2)/3
  let t := k-2*a
  have hMa : D.modulusExponent ≤ a := by dsimp [a]; omega
  have ht : 2*a+t=k := by dsimp [a,t]; omega
  have hta : t ≤ a := by dsimp [a,t]; omega
  have hpow : (p^a)^2*p^t=p^k := by rw [←pow_mul,←pow_add]; congr 1; omega
  have hterm : ∀ y : Fin 10 → Fin (p^a),
      integerResidue (p^D.modulusExponent) (integerVector y) ∈ D.residueSet →
      residueTerminalMax F (p^a) (p^t) y ≤ Ct*(p : ℝ)^(6*t) := by
    intro y hy
    apply LocalizedIneligibleWindow.terminal_bound_of_kernel hF a t hta y Ct hCt
    simpa only [integerVector,Int.cast_natCast] using hker (integerVector y) hy t
  have hb := norm_complete_sum_le F hF (p^a) (p^t) (p^D.modulusExponent)
    (pow_dvd_pow p hMa) D.residueSet v
  rw [hpow] at hb
  calc
    _ ≤ ((p^a : ℕ) : ℝ)^11 * pointwiseBound F (p^a) (p^t)
        (p^D.modulusExponent) D.residueSet v := hb
    _ ≤ ((p^a : ℕ) : ℝ)^11 *
        ((p : ℝ)^(a+t)*((p : ℝ)^(D.modulusExponent+D.lossExponent*D.minorSize)*
          (p : ℝ)^(2*a))*(Ct*(p : ℝ)^(6*t))) :=
      mul_le_mul_of_nonneg_left (pointwise_lift_bound D a t v Ct (zero_le_one.trans hCt) hterm)
        (by positivity)
    _ = _ := by
      rw [Nat.cast_pow,←pow_mul,show 7*k=a*11+(a+t)+2*a+6*t by omega]
      simp only [pow_add]
      ring

/-- Uniform pointwise seventh-power bound, including every low level
and level zero. The finite low range is absorbed into the same constant. -/
theorem exists_pointwise_bound (D : PrimeLocalizationData p F) (hF : F.IsHomogeneous 3) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (k : ℕ) (v : Fin 10 → ℤ),
      ‖localizedCompleteCubicSum F (p^k) (p^D.modulusExponent) D.residueSet v‖ ≤
        C*(p : ℝ)^(7*k) := by
  obtain ⟨Ct,hCt,hker⟩ := D.exists_uniform_residue_kernel_bound
  let K := max 3 (3*D.modulusExponent)
  let b : ℕ → ℝ := fun k => (p^k : ℕ)*(Nat.lcm (p^k) (p^D.modulusExponent) : ℝ)^10
  let B := ∑ k ∈ Finset.range K, b k
  let H := (p : ℝ)^(D.modulusExponent+D.lossExponent*D.minorSize)*Ct
  let C := max 1 (max H B)
  have hC : 1 ≤ C := le_max_left _ _
  have hHC : H ≤ C := (le_max_left H B).trans (le_max_right _ _)
  have hBC : B ≤ C := (le_max_right H B).trans (le_max_right _ _)
  have hb : ∀ k, 0 ≤ b k := by intro k; dsimp [b]; positivity
  have hp : 1 ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_le
  refine ⟨C,hC,?_⟩
  intro k v
  by_cases hk : K ≤ k
  · exact (high_pointwise_bound D hF Ct hCt hker k hk v).trans
      (mul_le_mul_of_nonneg_right hHC (by positivity))
  · have hbB : b k ≤ B := Finset.single_le_sum (fun j _ => hb j)
        (Finset.mem_range.mpr (by omega : k < K))
    have htriv := LocalizedFrequencyComparison.trivial_bound F (p^k)
      (p^D.modulusExponent) (pow_pos (Fact.out : p.Prime).pos _)
      (pow_pos (Fact.out : p.Prime).pos _) D.residueSet v
    exact htriv.trans ((hbB.trans hBC).trans
      (le_mul_of_one_le_right (zero_le_one.trans hC) (one_le_pow₀ hp)))

end CubicTenVariables.LocalizedResidueMajorant
