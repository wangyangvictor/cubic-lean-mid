import CubicTenVariables.LocalizedFlexibleLifting
import CubicTenVariables.PrimeLocalizationRootBound
import CubicTenVariables.QuadraticTerminalBound
import CubicTenVariables.PrimeLocalizationKernelBound

/-! The residue-window estimate at a fixed localization prime. All sums and
residue restrictions are the literal ones; small equation moduli retain the
full least-common-multiple ambient modulus. -/
noncomputable section
namespace CubicTenVariables.LocalizedIneligibleWindow
open MvPolynomial HessianTheorem11 SecondLiftSum LocalizedFlexibleLifting
open LocalizedRootSeriesIdentity QuadraticTerminalBound
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {p : ℕ} [Fact p.Prime] {F : MvPolynomial (Fin 10) ℤ}

/-- At T dividing A, the actual Hessian-kernel estimate controls the
terminal quadratic sum, including the prime 2. -/
theorem terminal_bound_of_kernel (hF : F.IsHomogeneous 3) (a t : ℕ)
    (hta : t ≤ a) (y : Fin 10 → Fin (p^a)) (C : ℝ) (hC : 1 ≤ C)
    (hker : (Nat.card {h : Fin 10 → ZMod (p^t) //
      (hessian (map (Int.castRingHom (ZMod (p^t))) F)
        (fun i => ((y i).val : ZMod (p^t)))).mulVec h = 0} : ℝ) ≤
      C*(p : ℝ)^(2*t)) :
    residueTerminalMax F (p^a) (p^t) y ≤ C*(p : ℝ)^(6*t) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  apply (residueTerminalMax_le_kernelRoot F hF (p^a) (p^t) (pow_dvd_pow p hta) y).trans
  unfold residueKernelRoot
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · have hh := mul_le_mul_of_nonneg_left hker (show 0 ≤ (p : ℝ)^(10*t) by positivity)
    have hex : ((p^t : ℕ) : ℝ)^10 = (p : ℝ)^(10*t) := by
      rw [Nat.cast_pow, ←pow_mul, Nat.mul_comm t 10]
    rw [hex]
    have hr : (p : ℝ)^(10*t)*(C*(p : ℝ)^(2*t)) = C*(p : ℝ)^(12*t) := by
      rw [mul_left_comm, ←pow_add]
      congr 2; omega
    have ht : (C*(p : ℝ)^(6*t))^2 = C^2*(p : ℝ)^(12*t) := by
      rw [mul_pow, ←pow_mul]
      congr 2; omega
    rw [hr] at hh
    rw [ht]
    exact hh.trans (mul_le_mul_of_nonneg_right (by nlinarith : C ≤ C^2) (by positivity))

/-- A uniform bound for the terminal maximum and for the actual restricted
root count gives the corresponding restricted zero-fiber sum bound. -/
theorem zeroFiberTotal_le (D : PrimeLocalizationData p F) (a t : ℕ)
    (Cr Ct : ℝ) (hCt : 0 ≤ Ct)
    (hroot : (rootCountAt F p D.modulusExponent a a D.residueSet : ℝ) ≤
      Cr*(p : ℝ)^(9*a))
    (hterm : ∀ y : Fin 10 → Fin (p^a),
      integerResidue (p^D.modulusExponent) (integerVector y) ∈ D.residueSet →
      residueTerminalMax F (p^a) (p^t) y ≤ Ct*(p : ℝ)^(6*t)) :
    zeroFiberTotal F (p^a) (p^t) (p^D.modulusExponent) D.residueSet ≤
      Cr*(p : ℝ)^(9*a) * (Ct*(p : ℝ)^(6*t)) := by
  unfold zeroFiberTotal
  calc
    _ ≤ ∑ y : Fin 10 → Fin (p^a),
        if integerResidue (p^D.modulusExponent) (integerVector y) ∈ D.residueSet ∧
          ((p^a : ℕ) : ℤ) ∣ eval (integerVector y) F then Ct*(p : ℝ)^(6*t) else 0 := by
      apply Finset.sum_le_sum
      intro y _
      split_ifs with hy
      · exact hterm y hy.1
      · rfl
    _ = (rootCountAt F p D.modulusExponent a a D.residueSet : ℝ) *
        (Ct*(p : ℝ)^(6*t)) := by
      rw [←Finset.sum_filter]
      simp only [rootCountAt, Finset.sum_const, nsmul_eq_mul]
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right hroot (by positivity)

/-- The ceiling choice loses at most a fixed fifth power of p. -/
theorem lifting_power_le (k a t : ℕ) (hceil : a = (k+2)/3)
    (hsplit : 2*a+t=k) :
    (p : ℝ)^(19*a+k+6*t) ≤ (p : ℝ)^5 * (p : ℝ)^((28:ℝ)/3*k) := by
  have hp : 1 ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_le
  have hceil' : 3*a ≤ k+2 := by omega
  have hex : (19*a+k+6*t : ℝ) ≤ 5+(28:ℝ)/3*k := by
    have hsplit' : (2:ℝ)*a+t=k := by exact_mod_cast hsplit
    have hceil'' : (3:ℝ)*a ≤ k+2 := by exact_mod_cast hceil'
    nlinarith
  calc
    _ = (p : ℝ)^((19*a+k+6*t : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (p : ℝ)^(5+(28:ℝ)/3*k) := by
      apply Real.rpow_le_rpow_of_exponent_le hp
      exact_mod_cast hex
    _ = _ := by rw [Real.rpow_add (by positivity)]; norm_num

/-- High equation levels, with the two concrete local estimates displayed
separately for reuse. The final theorem below discharges both estimates. -/
theorem high_bound_of_root_terminal (D : PrimeLocalizationData p F)
    (hF : F.IsHomogeneous 3) (Cr Ct : ℝ) (hCr : 0 ≤ Cr) (hCt : 0 ≤ Ct)
    (k : ℕ) (hk : max 3 (3*D.modulusExponent) ≤ k)
    (hroot : (rootCountAt F p D.modulusExponent ((k+2)/3) ((k+2)/3)
      D.residueSet : ℝ) ≤ Cr*(p : ℝ)^(9*((k+2)/3)))
    (hterm : ∀ y : Fin 10 → Fin (p^((k+2)/3)),
      integerResidue (p^D.modulusExponent) (integerVector y) ∈ D.residueSet →
      residueTerminalMax F (p^((k+2)/3)) (p^(k-2*((k+2)/3))) y ≤
        Ct*(p : ℝ)^(6*(k-2*((k+2)/3))))
    (V : Finset (Fin 10 → ℤ)) (w : (Fin 10 → ℤ) → ℝ)
    (hw : ∀ v ∈ V, 0 ≤ w v) :
    (∑ v ∈ V, w v * ‖localizedCompleteCubicSum F (p^k)
        (p^D.modulusExponent) D.residueSet v‖) ≤
      (Cr*Ct*(p : ℝ)^5) * (p : ℝ)^((28:ℝ)/3*k) *
        WeightedResidueMaximum.maximum (p^((k+2)/3)) V w := by
  let a := (k+2)/3
  let t := k-2*a
  have hMa : D.modulusExponent ≤ a := by dsimp [a]; omega
  have ht : 2*a+t=k := by dsimp [a,t]; omega
  have hpow : (p^a)^2*p^t=p^k := by rw [←pow_mul,←pow_add]; congr 1; omega
  have hE := WeightedResidueMaximum.maximum_nonneg (p^a) V w hw
  have hz := zeroFiberTotal_le D a t Cr Ct hCt hroot hterm
  have hphi : (Nat.totient (p^k) : ℝ) ≤ (p : ℝ)^k := by
    exact_mod_cast Nat.totient_le (p^k)
  have hmain := weighted_complete_sum_le F hF (p^a) (p^t)
    (p^D.modulusExponent) (pow_dvd_pow p hMa) D.residueSet V w hw
  rw [hpow] at hmain
  calc
    _ ≤ ((p^a : ℕ) : ℝ)^10*(Nat.totient (p^k) : ℝ)*
        WeightedResidueMaximum.maximum (p^a) V w *
        zeroFiberTotal F (p^a) (p^t) (p^D.modulusExponent) D.residueSet := hmain
    _ ≤ ((p^a : ℕ) : ℝ)^10*(p : ℝ)^k*
        WeightedResidueMaximum.maximum (p^a) V w *
        (Cr*(p : ℝ)^(9*a)*(Ct*(p : ℝ)^(6*t))) := by
      have hz0 : 0 ≤ zeroFiberTotal F (p^a) (p^t)
          (p^D.modulusExponent) D.residueSet := by
        unfold zeroFiberTotal
        apply Finset.sum_nonneg
        intro y _
        split_ifs
        · exact residueTerminalMax_nonneg F (p^a) (p^t) y
        · rfl
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hphi (by positivity)) hE)
        hz hz0 (by positivity)
    _ = (Cr*Ct) * (p : ℝ)^(19*a+k+6*t) *
        WeightedResidueMaximum.maximum (p^a) V w := by
      simp only [Nat.cast_pow,←pow_mul]
      rw [show 19*a+k+6*t=a*10+k+9*a+6*t by omega]
      simp only [pow_add]
      ring
    _ ≤ (Cr*Ct) * ((p : ℝ)^5*(p : ℝ)^((28:ℝ)/3*k)) *
        WeightedResidueMaximum.maximum (p^a) V w := by
      gcongr
      exact lifting_power_le k a t rfl ht
    _ = _ := by ring

/-- The actual ineligible-prime residue-window estimate in ten variables.
The single constant precedes k, the finite frequency set and all nonnegative
weights. No arithmetic estimate or additional literature is assumed. -/
theorem exists_weighted_window_bound (D : PrimeLocalizationData p F)
    (hF : F.IsHomogeneous 3) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ k : ℕ, ∀ V : Finset (Fin 10 → ℤ),
      ∀ w : (Fin 10 → ℤ) → ℝ, (∀ v ∈ V, 0 ≤ w v) →
      (∑ v ∈ V, w v * ‖localizedCompleteCubicSum F (p^k)
          (p^D.modulusExponent) D.residueSet v‖) ≤
        C*(p : ℝ)^((28:ℝ)/3*k)*
          WeightedResidueMaximum.maximum (p^((k+2)/3)) V w := by
  obtain ⟨Cr,hCr,hroot⟩ := D.exists_rootCountAt_bound hF
  obtain ⟨Ct,hCt,hker⟩ := D.exists_uniform_residue_kernel_bound
  let K := max 3 (3*D.modulusExponent)
  let b : ℕ → ℝ := fun k => (p^k : ℕ)*(Nat.lcm (p^k) (p^D.modulusExponent) : ℝ)^10*
    ((p^((k+2)/3) : ℕ) : ℝ)^10
  let B := ∑ k ∈ Finset.range K, b k
  let H := Cr*Ct*(p : ℝ)^5
  let C := max 1 (max H B)
  have hC : 1 ≤ C := le_max_left _ _
  have hHC : H ≤ C := (le_max_left H B).trans (le_max_right _ _)
  have hBC : B ≤ C := (le_max_right H B).trans (le_max_right _ _)
  have hb : ∀ k, 0 ≤ b k := by intro k; dsimp [b]; positivity
  have hp : 1 ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_le
  refine ⟨C,hC,?_⟩
  intro k V w hw
  have hE := WeightedResidueMaximum.maximum_nonneg (p^((k+2)/3)) V w hw
  have hrpow : 1 ≤ (p : ℝ)^((28:ℝ)/3*k) :=
    Real.one_le_rpow hp (by positivity)
  by_cases hk : K ≤ k
  · have hMa : D.modulusExponent ≤ (k+2)/3 := by dsimp [K] at hk; omega
    have hta : k-2*((k+2)/3) ≤ (k+2)/3 := by omega
    have hterm : ∀ y : Fin 10 → Fin (p^((k+2)/3)),
        integerResidue (p^D.modulusExponent) (integerVector y) ∈ D.residueSet →
        residueTerminalMax F (p^((k+2)/3)) (p^(k-2*((k+2)/3))) y ≤
          Ct*(p : ℝ)^(6*(k-2*((k+2)/3))) := by
      intro y hy
      apply terminal_bound_of_kernel hF _ _ hta y Ct hCt
      simpa only [integerVector, Int.cast_natCast] using
        hker (integerVector y) hy (k-2*((k+2)/3))
    apply (high_bound_of_root_terminal D hF Cr Ct (by linarith) (by linarith)
      k hk (hroot _ hMa) hterm V w hw).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hHC (by positivity)) hE
  · have hkK : k < K := by omega
    have hbB : b k ≤ B := Finset.single_le_sum (fun i _ => hb i)
      (Finset.mem_range.mpr hkK)
    have htriv := LocalizedFrequencyComparison.weighted_trivial_bound F (p^k)
      (p^D.modulusExponent) (p^((k+2)/3))
      (pow_pos (Fact.out : p.Prime).pos _) (pow_pos (Fact.out : p.Prime).pos _)
      D.residueSet V w hw
    apply htriv.trans
    change b k * WeightedResidueMaximum.maximum (p^((k+2)/3)) V w ≤ _
    apply mul_le_mul_of_nonneg_right _ hE
    exact (hbB.trans hBC).trans (le_mul_of_one_le_right (by linarith : 0 ≤ C) hrpow)

end CubicTenVariables.LocalizedIneligibleWindow
