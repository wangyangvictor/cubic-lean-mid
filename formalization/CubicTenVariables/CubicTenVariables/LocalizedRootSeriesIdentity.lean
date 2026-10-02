import CubicTenVariables.LocalizedSums
import CubicTenVariables.PrimePowerRamanujan
import CubicTenVariables.PrimePowerRootReduction

/-! Exact finite prime-power root densities with an arbitrary fixed congruence
restriction. The ambient modulus is the least common multiple of the equation
modulus and the restriction modulus, including when the latter is larger. -/

noncomputable section
namespace CubicTenVariables.LocalizedRootSeriesIdentity
open MvPolynomial PrimePowerFibers
open scoped BigOperators Classical

/-- Literal restricted roots tested on all representatives at ambient level s.
No relation among the three levels is built into this definition. -/
def rootCountAt {n : ℕ} (F : MvPolynomial (Fin n) ℤ) (p M k s : ℕ)
    (Ω : Set (Fin n → ZMod (p^M))) : ℕ :=
  (Finset.univ.filter fun x : Fin n → Fin (p^s) =>
    integerResidue (p^M) (fun i => ((x i).val : ℤ)) ∈ Ω ∧
      ((p^k : ℕ) : ℤ) ∣ eval (fun i => ((x i).val : ℤ)) F).card

theorem lcm_prime_powers (p k M : ℕ) :
    Nat.lcm (p^k) (p^M) = p^(max k M) := by
  rcases le_total k M with h | h
  · rw [max_eq_right h]
    exact Nat.lcm_eq_right_iff_dvd.mpr (pow_dvd_pow p h)
  · rw [max_eq_left h]
    exact Nat.lcm_eq_left_iff_dvd.mpr (pow_dvd_pow p h)

private theorem reduction_comp (p : ℕ) {s t u : ℕ}
    (hts : t ≤ s) (hut : u ≤ t) (x : ZMod (p^s)) :
    reduction p hut (reduction p hts x) = reduction p (hut.trans hts) x := by
  exact congrArg (fun f : ZMod (p^s) →+* ZMod (p^u) => f x)
    (ZMod.castHom_comp (pow_dvd_pow p hut) (pow_dvd_pow p hts))

theorem rootCountAt_eq_filter {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (p M k s : ℕ) [Fact p.Prime] (Ω : Set (Fin n → ZMod (p^M)))
    (hMs : M ≤ s) (hks : k ≤ s) :
    rootCountAt F p M k s Ω =
      (Finset.univ.filter fun x : Fin n → ZMod (p^s) =>
        (fun i => reduction p hMs (x i)) ∈ Ω ∧
        eval₂ (Int.castRingHom (ZMod (p^k)))
          (fun i => reduction p hks (x i)) F = 0).card := by
  classical
  apply Nat.cast_injective (R := ℂ)
  simp only [rootCountAt, ← Finset.sum_boole]
  apply Fintype.sum_equiv (PrimeSumAdapter.vectorResidueEquiv (p^s) n)
  intro x
  have hmem : integerResidue (p^M) (fun i => ((x i).val : ℤ)) =
      fun i => reduction p hMs (PrimeSumAdapter.vectorResidueEquiv (p^s) n x i) := by
    funext i
    simp [integerResidue, PrimeSumAdapter.vectorResidueEquiv_apply]
  simp only [hmem, PrimePowerRootReduction.dvd_eval_iff_reduced_zero F p hks]

/-- Simultaneous restriction and root conditions lift by the exact ambient
reduction-fiber factor; this includes zero levels and dimension zero. -/
theorem rootCountAt_lift {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (p M k : ℕ) [Fact p.Prime] (Ω : Set (Fin n → ZMod (p^M)))
    {s t : ℕ} (hMt : M ≤ t) (hkt : k ≤ t) (hts : t ≤ s) :
    rootCountAt F p M k s Ω = p^((s-t)*n) * rootCountAt F p M k t Ω := by
  rw [rootCountAt_eq_filter F p M k s Ω (hMt.trans hts) (hkt.trans hts),
    rootCountAt_eq_filter F p M k t Ω hMt hkt]
  simpa only [reduction_comp] using
    PolynomialSingularLifts.card_reduction_preimage p hts
      (fun x : Fin n → ZMod (p^t) =>
        (fun i => reduction p hMt (x i)) ∈ Ω ∧
        eval₂ (Int.castRingHom (ZMod (p^k)))
          (fun i => reduction p hkt (x i)) F = 0)

/-- Root density with the actual common ambient modulus. -/
def rootDensity {n : ℕ} (F : MvPolynomial (Fin n) ℤ) (p M k : ℕ)
    (Ω : Set (Fin n → ZMod (p^M))) : ℂ :=
  (p : ℂ)^k * (rootCountAt F p M k (max k M) Ω : ℂ) /
    (p : ℂ)^((max k M)*n)

theorem normalized_rootCountAt_lift {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (p M k : ℕ) [Fact p.Prime] (Ω : Set (Fin n → ZMod (p^M)))
    {s t : ℕ} (hMt : M ≤ t) (hkt : k ≤ t) (hts : t ≤ s) :
    (rootCountAt F p M k s Ω : ℂ) / (p : ℂ)^(s*n) =
      (rootCountAt F p M k t Ω : ℂ) / (p : ℂ)^(t*n) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [rootCountAt_lift F p M k Ω hMt hkt hts, Nat.cast_mul, Nat.cast_pow]
  have he : s*n = (s-t)*n+t*n := by rw [← Nat.add_mul, Nat.sub_add_cancel hts]
  rw [he, pow_add, mul_div_mul_left _ _ (pow_ne_zero _ hpC)]

private theorem sum_indicator_const {α : Type*} [Fintype α]
    (P : α → Prop) [DecidablePred P] (c : ℂ) :
    (∑ x, if P x then c else 0) = c * ((Finset.univ.filter P).card : ℂ) := by
  rw [← Finset.sum_filter]
  simp [mul_comm]

private theorem ite_sum_zero {α : Type*} [Fintype α]
    (P : Prop) [Decidable P] (f : α → ℂ) :
    (if P then ∑ x, f x else 0) = ∑ x, if P then f x else 0 := by
  by_cases h : P <;> simp [h]

/-- Primitive scalar orthogonality at a fixed ambient level produces the
difference of the two literal restricted root counts. -/
theorem localizedCompleteCubicSum_prime_power {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (p M s : ℕ) [Fact p.Prime]
    (Ω : Set (Fin n → ZMod (p^M))) :
    localizedCompleteCubicSum F (p^(s+1)) (p^M) Ω 0 =
      (p : ℂ)^(s+1) * (rootCountAt F p M (s+1) (max (s+1) M) Ω : ℂ) -
        (p : ℂ)^s * (rootCountAt F p M s (max (s+1) M) Ω : ℂ) := by
  classical
  have hswap : localizedCompleteCubicSum F (p^(s+1)) (p^M) Ω 0 =
      ∑ x : Fin n → Fin (p^(max (s+1) M)),
        if integerResidue (p^M) (fun i => ((x i).val : ℤ)) ∈ Ω then
          ∑ a : Fin (p^(s+1)), if Nat.Coprime a.val (p^(s+1)) then
            residueExponential (p^(s+1))
              ((a.val : ℤ) * eval (fun i => ((x i).val : ℤ)) F) else 0
        else 0 := by
    unfold localizedCompleteCubicSum
    rw [lcm_prime_powers]
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
  simp_rw [PrimePowerRamanujan.sum_primitive_scalar]
  have hterm (x : Fin n → Fin (p^(max (s+1) M))) :
      (if integerResidue (p^M) (fun i => ((x i).val : ℤ)) ∈ Ω then
        (if (p^(s+1) : ℤ) ∣ eval (fun i => ((x i).val : ℤ)) F then
          (p : ℂ)^(s+1) else 0) -
        (if (p^s : ℤ) ∣ eval (fun i => ((x i).val : ℤ)) F then
          (p : ℂ)^s else 0) else 0) =
      (if integerResidue (p^M) (fun i => ((x i).val : ℤ)) ∈ Ω ∧
          (p^(s+1) : ℤ) ∣ eval (fun i => ((x i).val : ℤ)) F then
          (p : ℂ)^(s+1) else 0) -
      (if integerResidue (p^M) (fun i => ((x i).val : ℤ)) ∈ Ω ∧
          (p^s : ℤ) ∣ eval (fun i => ((x i).val : ℤ)) F then
          (p : ℂ)^s else 0) := by split_ifs <;> simp_all
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, sum_indicator_const, sum_indicator_const]
  simp only [rootCountAt, Nat.cast_pow]

/-- The actual localized coefficient is the successive difference of
restricted root densities, with no restriction on M or the dimension. -/
theorem localizedSingularSeriesTerm_prime_power {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (p M s : ℕ) [Fact p.Prime]
    (Ω : Set (Fin n → ZMod (p^M))) :
    localizedSingularSeriesTerm F (p^M) Ω (p^(s+1)) =
      rootDensity F p M (s+1) Ω - rootDensity F p M s Ω := by
  rw [localizedSingularSeriesTerm, if_neg (pow_ne_zero _ (Fact.out : p.Prime).ne_zero),
    localizedCompleteCubicSum_prime_power, lcm_prime_powers, Nat.cast_pow, ← pow_mul,
    sub_div]
  unfold rootDensity
  congr 1
  rw [mul_div_assoc, mul_div_assoc]
  congr 1
  exact normalized_rootCountAt_lift F p M s Ω (le_max_right s M)
    (le_max_left s M) (max_le_max (Nat.le_succ s) le_rfl)

/-- The modulus-one coefficient retains the density of the arbitrary
restriction; it is not replaced by one. -/
theorem localizedSingularSeriesTerm_one {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (p M : ℕ) [Fact p.Prime]
    (Ω : Set (Fin n → ZMod (p^M))) :
    localizedSingularSeriesTerm F (p^M) Ω 1 = rootDensity F p M 0 Ω := by
  unfold localizedSingularSeriesTerm localizedCompleteCubicSum rootDensity rootCountAt
  rw [Nat.lcm_one_left, max_eq_right (Nat.zero_le M)]
  simp [residueExponential, ← Finset.sum_boole, ← pow_mul]

/-- Exact finite identity for every equation level and restriction level.
No local solubility, positivity, convergence or analytic input is assumed. -/
theorem root_density_eq_sum {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (p M k : ℕ) [Fact p.Prime]
    (Ω : Set (Fin n → ZMod (p^M))) :
    rootDensity F p M k Ω =
      ∑ j ∈ Finset.range (k+1), localizedSingularSeriesTerm F (p^M) Ω (p^j) := by
  induction k with
  | zero => simpa using (localizedSingularSeriesTerm_one F p M Ω).symm
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih, localizedSingularSeriesTerm_prime_power]
    ring

/-- Entirely expanded in the actual least-common-multiple representatives,
the finite sum of localized prime-power coefficients is a literal root count. -/
theorem literal_root_density_eq_sum {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (p M k : ℕ) [Fact p.Prime]
    (Ω : Set (Fin n → ZMod (p^M))) :
    (p : ℂ)^k /
        (Nat.lcm (p^k) (p^M) : ℂ)^n *
      ((Finset.univ.filter fun x : Fin n → Fin (Nat.lcm (p^k) (p^M)) =>
        integerResidue (p^M) (fun i => ((x i).val : ℤ)) ∈ Ω ∧
          ((p^k : ℕ) : ℤ) ∣ eval (fun i => ((x i).val : ℤ)) F).card : ℂ) =
      ∑ j ∈ Finset.range (k+1), localizedSingularSeriesTerm F (p^M) Ω (p^j) := by
  rw [lcm_prime_powers]
  simpa only [rootDensity, rootCountAt, Nat.cast_pow, ← pow_mul, div_mul_eq_mul_div]
    using root_density_eq_sum F p M k Ω

/-- Once the equation modulus contains the restriction modulus, this is
the usual normalized count of actual roots in the residue ring. -/
theorem residue_root_density_eq_sum_of_le {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hn : 1 ≤ n) (p M k : ℕ) [Fact p.Prime]
    (Ω : Set (Fin n → ZMod (p^M))) (hMk : M ≤ k) :
    ((Finset.univ.filter fun x : Fin n → ZMod (p^k) =>
      (fun i => reduction p hMk (x i)) ∈ Ω ∧
        eval₂ (Int.castRingHom (ZMod (p^k))) x F = 0).card : ℂ) /
        (p : ℂ)^(k*(n-1)) =
      ∑ j ∈ Finset.range (k+1), localizedSingularSeriesTerm F (p^M) Ω (p^j) := by
  have h := root_density_eq_sum F p M k Ω
  rw [rootDensity, max_eq_left hMk,
    rootCountAt_eq_filter F p M k k Ω hMk le_rfl] at h
  simp only [reduction, ZMod.castHom_self, RingHom.id_apply] at h
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have he : k*n = k+k*(n-1) := by
    have := Nat.sub_add_cancel hn
    nlinarith
  rw [he, pow_add, mul_div_mul_left _ _ (pow_ne_zero _ hpC)] at h
  exact h

/-- At modulus one, only the density of the restriction remains. In
particular an empty restriction gives zero, and no positivity is asserted. -/
theorem localizedSingularSeriesTerm_one_eq_density {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (p M : ℕ) [Fact p.Prime]
    (Ω : Set (Fin n → ZMod (p^M))) :
    localizedSingularSeriesTerm F (p^M) Ω 1 =
      ((Finset.univ.filter fun x : Fin n → ZMod (p^M) => x ∈ Ω).card : ℂ) /
        (p : ℂ)^(M*n) := by
  rw [localizedSingularSeriesTerm_one, rootDensity]
  simp only [pow_zero, one_mul, max_eq_right (Nat.zero_le M)]
  rw [rootCountAt_eq_filter F p M 0 M Ω le_rfl (Nat.zero_le M)]
  have hz (x : Fin n → ZMod (p^M)) :
      eval₂ (Int.castRingHom (ZMod (p^0)))
        (fun i => reduction p (Nat.zero_le M) (x i)) F = 0 := by
    haveI : Subsingleton (ZMod (p^0)) := by
      simpa using (inferInstance : Subsingleton (ZMod 1))
    exact Subsingleton.elim _ _
  simp_rw [hz]
  simp only [and_true, reduction, ZMod.castHom_self, RingHom.id_apply]

end CubicTenVariables.LocalizedRootSeriesIdentity
