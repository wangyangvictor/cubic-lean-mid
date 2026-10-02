import CubicTenVariables.PrimeRankGcdMass
import CubicTenVariables.PrimeFrogOneMass
import CubicTenVariables.PrimeFieldKernelRank

/-! The sharp ten-variable half-Hessian mass O(p^10), obtained by summing
actual rank-conditioned gcd masses and using exact finite-field kernel sizes.
The constant is uniform over all primes, including 2 and 3, and both gcd
weights may independently be omitted. No literature proposition is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace CubicTenVariables.CubicPrimeFrogOneSharp
open MvPolynomial HessianTheorem11 PrimeRankGcdMass OnCubicRankCountsTen
open PrimeFrogZeroMass PrimeFrogOneMass HessianKernelCRT SquarefreeResidueFactors
open scoped BigOperators

/-- Every one of the eleven actual rank classes has cost at most ten. -/
theorem rank_cost_le (r : ℕ) (hr : r ≤ 10) :
    2*(deltaNat r+gammaNat r)+(10-r) ≤ 20 := by
  interval_cases r <;> norm_num [deltaNat,gammaNat]

/-- Avoiding fractional-power rounding preserves the sharp exponent. -/
theorem rank_factor_le (p r : ℕ) (hp : 1 ≤ p) (hr : r ≤ 10) :
    (p : ℝ)^(deltaNat r+gammaNat r)*Real.sqrt ((p : ℝ)^(10-r)) ≤ (p : ℝ)^10 := by
  have he : ((p : ℝ)^(deltaNat r+gammaNat r)*Real.sqrt ((p : ℝ)^(10-r)))^2 =
      (p : ℝ)^(2*(deltaNat r+gammaNat r)+(10-r)) := by
    rw [mul_pow,Real.sq_sqrt (by positivity),← pow_mul,← pow_add]
    congr 1
    omega
  have hb : (p : ℝ)^(2*(deltaNat r+gammaNat r)+(10-r)) ≤ (p : ℝ)^20 := by
    exact_mod_cast Nat.pow_le_pow_right hp (rank_cost_le r hr)
  have hs : ((p : ℝ)^(deltaNat r+gammaNat r)*Real.sqrt ((p : ℝ)^(10-r)))^2 ≤
      ((p : ℝ)^10)^2 := by
    rw [he,← pow_mul]
    norm_num only [Nat.reduceMul]
    exact hb
  nlinarith [show (0 : ℝ) ≤ (p : ℝ)^10 by positivity]

/-- Discarding either gcd factor only decreases the actual weight. -/
theorem optionalRootWeight_le_rootWeight {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (p : ℕ) (hp : 0 < p) (x : Fin n → ZMod p)
    (includeGradient includeCoordinates : Bool) :
    optionalRootWeight F p x includeGradient includeCoordinates ≤ rootWeight F p x := by
  unfold optionalRootWeight rootWeight
  have hg : 1 ≤ vectorGcd p (fun i => eval (integerLift p x) (pderiv i F)) :=
    vectorGcd_pos p hp _
  have hx : 1 ≤ vectorGcd p (integerLift p x) := vectorGcd_pos p hp _
  apply Nat.mul_le_mul <;> split_ifs <;> omega

/-- The true square-root kernel mass on each rank class factors exactly. -/
theorem rank_mass_eq (F : MvPolynomial (Fin 10) ℤ)
    (p r : ℕ) [Fact p.Prime] :
    (∑ x ∈ exactRankRoots F p r,
      (rootWeight F p x : ℝ)*Real.sqrt (hessianKernelCard F p x : ℝ)) =
    ((∑ x ∈ exactRankRoots F p r, rootWeight F p x : ℕ) : ℝ)*
      Real.sqrt ((p : ℝ)^(10-r)) := by
  classical
  rw [Nat.cast_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [PrimeFieldKernelRank.hessianKernelCard_eq_pow,
    ((mem_exactRankRoots F p r x).mp hx).2,Nat.cast_pow]

/-- Exact decomposition of the actual root-filtered mass into all eleven
finite-field Hessian ranks. -/
theorem oneMass_eq_rank_sum (F : MvPolynomial (Fin 10) ℤ)
    (p : ℕ) [Fact p.Prime] :
    oneMass F p true true = ∑ r ∈ Finset.range 11,
      ∑ x ∈ exactRankRoots F p r,
        (rootWeight F p x : ℝ)*Real.sqrt (hessianKernelCard F p x : ℝ) := by
  classical
  let S := Finset.univ.filter fun x : Fin 10 → ZMod p =>
    eval₂ (Int.castRingHom (ZMod p)) x F = 0
  have hm : ∀ x ∈ S,
      (hessian (map (Int.castRingHom (ZMod p)) F) x).rank ∈ Finset.range 11 := by
    intro x _
    have hh := Matrix.rank_le_card_width (hessian (map (Int.castRingHom (ZMod p)) F) x)
    simp only [Fintype.card_fin] at hh
    exact Finset.mem_range.mpr (by omega)
  have hs := Finset.sum_fiberwise_of_maps_to hm
    (fun x => (rootWeight F p x : ℝ)*Real.sqrt (hessianKernelCard F p x : ℝ))
  simpa only [S,oneMass,optionalRootWeight_true_true,exactRankRoots,Finset.filter_filter] using hs.symm

/-- Uniform sharp bound with both source gcd factors retained. -/
theorem exists_full_mass_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : ℕ) [Fact p.Prime],
      oneMass F p true true ≤ C*(p : ℝ)^10 := by
  classical
  obtain ⟨B,hB,hbound⟩ := PrimeRankGcdMass.exists_uniform_bound F hF hA
  refine ⟨11*(B : ℝ),?_,?_⟩
  · have hb : (1 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  intro p hp
  have hrank (r : ℕ) (hr : r ∈ Finset.range 11) :
      (∑ x ∈ exactRankRoots F p r,
        (rootWeight F p x : ℝ)*Real.sqrt (hessianKernelCard F p x : ℝ)) ≤
      (B : ℝ)*(p : ℝ)^10 := by
    have hr10 : r ≤ 10 := by have hh := Finset.mem_range.mp hr; omega
    rw [rank_mass_eq]
    have hm : ((∑ x ∈ exactRankRoots F p r,rootWeight F p x : ℕ) : ℝ) ≤
        (B : ℝ)*(p : ℝ)^(deltaNat r+gammaNat r) := by
      exact_mod_cast hbound p r hr10
    calc
      _ ≤ ((B : ℝ)*(p : ℝ)^(deltaNat r+gammaNat r))*Real.sqrt ((p : ℝ)^(10-r)) :=
        mul_le_mul_of_nonneg_right hm (Real.sqrt_nonneg _)
      _ = (B : ℝ)*((p : ℝ)^(deltaNat r+gammaNat r)*Real.sqrt ((p : ℝ)^(10-r))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (rank_factor_le p r hp.out.one_le hr10) (Nat.cast_nonneg _)
  rw [oneMass_eq_rank_sum]
  calc
    _ ≤ ∑ _r ∈ Finset.range 11, (B : ℝ)*(p : ℝ)^10 := Finset.sum_le_sum hrank
    _ = _ := by simp; ring

/-- The same constant works for all four combinations of source gcd factors. -/
theorem exists_uniform_sqrt_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : ℕ) (hp : p.Prime),
      letI : NeZero p := ⟨hp.ne_zero⟩
      ∀ (includeGradient includeCoordinates : Bool),
        oneMass F p includeGradient includeCoordinates ≤ C*(p : ℝ)^10 := by
  classical
  obtain ⟨C,hC,hbound⟩ := exists_full_mass_bound F hF hA
  refine ⟨C,hC,?_⟩
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  intro includeGradient includeCoordinates
  apply le_trans _ (hbound p)
  unfold oneMass
  apply Finset.sum_le_sum
  intro x _
  rw [optionalRootWeight_true_true]
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast optionalRootWeight_le_rootWeight F p hp.pos x includeGradient includeCoordinates)
    (Real.sqrt_nonneg _)

/-- Literal source half-Hessian estimate with canonical integral gcd weights.
The constant precedes every prime and both omission switches. -/
theorem exists_uniform_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : ℕ) (hp : p.Prime),
      letI : NeZero p := ⟨hp.ne_zero⟩
      ∀ (includeGradient includeCoordinates : Bool),
        (∑ x ∈ Finset.univ.filter (fun x : Fin 10 → ZMod p =>
          eval₂ (Int.castRingHom (ZMod p)) x F = 0),
          (hessianKernelCard F p x : ℝ)^((1 : ℝ)/2) *
          (((if includeGradient then
            vectorGcd p (fun i => eval (integerLift p x) (pderiv i F)) else 1) *
          (if includeCoordinates then vectorGcd p (integerLift p x) else 1) : ℕ) : ℝ)) ≤
            C*(p : ℝ)^10 := by
  classical
  obtain ⟨C,hC,hbound⟩ := exists_uniform_sqrt_bound F hF hA
  refine ⟨C,hC,?_⟩
  intro p hp
  letI : NeZero p := ⟨hp.ne_zero⟩
  intro includeGradient includeCoordinates
  simpa only [oneMass_eq_rpow,optionalRootWeight] using hbound p hp includeGradient includeCoordinates

end CubicTenVariables.CubicPrimeFrogOneSharp
