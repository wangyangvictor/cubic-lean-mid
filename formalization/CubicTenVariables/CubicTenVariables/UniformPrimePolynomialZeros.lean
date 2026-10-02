import TranslatedDepthSeven.SchwartzZippelResidueCount
import HessianTheorem11.Geometry

/-!
# One polynomial zero-count constant before all primes

A nonzero integral coefficient controls every prime at which the entire
polynomial reduces to zero. At every other prime the proved finite-field
Schwartz--Zippel bound applies. Thus one explicit natural constant bounds
the literal zero count at all primes, including 2 and primes dividing the
content. No geometric reduction theorem or exceptional-prime input is used.

The Hessian-rank subset corollary is only an inclusion in this zero set;
it asserts no stronger estimate for the lower-rank strata.
-/

noncomputable section
namespace CubicTenVariables.UniformPrimePolynomialZeros

open MvPolynomial

/-- Literal zeros of the coefficientwise reduction on the full affine space. -/
def primeZeros {n : ℕ} (F : MvPolynomial (Fin n) ℤ) (p : ℕ) (hp : p.Prime) :
    Finset (Fin n → ZMod p) :=
  TranslatedDepthSeven.mvPolynomialZeroSet p n hp (map (Int.castRingHom (ZMod p)) F)

@[simp]
theorem mem_primeZeros {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (p : ℕ) (hp : p.Prime) (x : Fin n → ZMod p) :
    x ∈ primeZeros F p hp ↔ eval x (map (Int.castRingHom (ZMod p)) F) = 0 :=
  TranslatedDepthSeven.mem_mvPolynomialZeroSet_iff hp _ x

/-- The constant is fixed by one integral coefficient, before choosing a prime. -/
def coefficientConstant {n : ℕ} (F : MvPolynomial (Fin n) ℤ) (d : Fin n →₀ ℕ) : ℕ :=
  max F.totalDegree (coeff d F).natAbs

theorem coefficientConstant_pos {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (d : Fin n →₀ ℕ) (hd : coeff d F ≠ 0) : 0 < coefficientConstant F d :=
  (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hd)).trans_le (le_max_right _ _)

theorem totalDegree_reduction_le {n p : ℕ} (F : MvPolynomial (Fin n) ℤ) :
    (map (Int.castRingHom (ZMod p)) F).totalDegree ≤ F.totalDegree :=
  Finset.sup_mono (support_map_subset _ _)

/-- If reduction is identically zero, each fixed nonzero coefficient bounds p. -/
theorem prime_le_coefficient_of_reduction_eq_zero {n p : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (d : Fin n →₀ ℕ) (hd : coeff d F ≠ 0)
    (hzero : map (Int.castRingHom (ZMod p)) F = 0) :
    p ≤ (coeff d F).natAbs := by
  have hc : ((coeff d F : ℤ) : ZMod p) = 0 := by
    simpa only [coeff_map, coeff_zero] using
      congrArg (coeff d) hzero
  have hdiv := (ZMod.intCast_zmod_eq_zero_iff_dvd (coeff d F) p).mp hc
  simpa only [Int.natAbs_natCast] using Int.natAbs_le_of_dvd_ne_zero hdiv hd

/-- The literal zero count, with an explicit coefficient constant, at every prime.
Natural subtraction also allows n=0; the exceptional constant case is included. -/
theorem card_primeZeros_le_coefficientConstant {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (d : Fin n →₀ ℕ) (hd : coeff d F ≠ 0)
    (p : ℕ) (hp : p.Prime) :
    (primeZeros F p hp).card ≤ coefficientConstant F d * p ^ (n - 1) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  by_cases hzero : map (Int.castRingHom (ZMod p)) F = 0
  · have hpc : p ≤ coefficientConstant F d :=
      (prime_le_coefficient_of_reduction_eq_zero F d hd hzero).trans (le_max_right _ _)
    have hfull : (primeZeros F p hp).card ≤ p ^ n := by
      calc
        _ ≤ Fintype.card (Fin n → ZMod p) := Finset.card_le_univ _
        _ = p ^ n := by simp [ZMod.card]
    refine hfull.trans ?_
    cases n with
    | zero => simpa using coefficientConstant_pos F d hd
    | succ n =>
        simpa only [Nat.succ_sub_one, pow_succ, mul_comm] using
          Nat.mul_le_mul_right (p ^ n) hpc
  · exact (TranslatedDepthSeven.card_mvPolynomialZeroSet_le_degree_mul hp _ hzero
      (totalDegree_reduction_le F)).trans
        (Nat.mul_le_mul_right _ (le_max_left _ _))

/-- A single positive constant is constructed before all primes. -/
theorem exists_uniform_prime_zero_bound {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F ≠ 0) :
    ∃ C : ℕ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime),
      (primeZeros F p hp).card ≤ C * p ^ (n - 1) := by
  obtain ⟨d, hd⟩ := exists_coeff_ne_zero hF
  exact ⟨coefficientConstant F d, coefficientConstant_pos F d hd,
    card_primeZeros_le_coefficientConstant F d hd⟩

/-- For a nonzero homogeneous cubic the explicit degree factor is exactly 3. -/
theorem card_primeZeros_cubic_le {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (d : Fin n →₀ ℕ) (hd : coeff d F ≠ 0)
    (p : ℕ) (hp : p.Prime) :
    (primeZeros F p hp).card ≤ max 3 (coeff d F).natAbs * p ^ (n - 1) := by
  have hne : F ≠ 0 := by intro h; simp [h] at hd
  simpa only [coefficientConstant, hF.totalDegree hne] using
    card_primeZeros_le_coefficientConstant F d hd p hp

/-- Any selected subset of actual zeros obeys the same uniform estimate. -/
theorem card_primeZeros_filter_le {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (d : Fin n →₀ ℕ) (hd : coeff d F ≠ 0)
    (p : ℕ) (hp : p.Prime) (P : (Fin n → ZMod p) → Prop) [DecidablePred P] :
    ((primeZeros F p hp).filter P).card ≤ coefficientConstant F d * p ^ (n - 1) :=
  (Finset.card_filter_le _ _).trans (card_primeZeros_le_coefficientConstant F d hd p hp)

/-- One constant simultaneously controls all zeros and the rank-at-least-eight
zero subset in ten variables. The displayed matrix is the actual reduced Hessian. -/
theorem exists_uniform_ten_rank_eight_zero_bound
    (F : MvPolynomial (Fin 10) ℤ) (hF : F ≠ 0) :
    ∃ C : ℕ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime),
      (primeZeros F p hp).card ≤ C * p ^ 9 ∧
      ((primeZeros F p hp).filter fun x =>
        8 ≤ (HessianTheorem11.hessian (map (Int.castRingHom (ZMod p)) F) x).rank).card
          ≤ C * p ^ 9 := by
  classical
  obtain ⟨d, hd⟩ := exists_coeff_ne_zero hF
  refine ⟨coefficientConstant F d, coefficientConstant_pos F d hd, fun p hp => ?_⟩
  exact ⟨card_primeZeros_le_coefficientConstant F d hd p hp,
    card_primeZeros_filter_le F d hd p hp _⟩

/-- The same one constant precedes both the prime and the exact rank label.
Every exact-rank zero stratum is a subset of the zero set, so the exponent
is always 9 here; this does not assert the sharper lower-rank exponents. -/
theorem exists_uniform_ten_exact_rank_zero_bound
    (F : MvPolynomial (Fin 10) ℤ) (hF : F ≠ 0) :
    ∃ C : ℕ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (ρ : ℕ),
      ((primeZeros F p hp).filter fun x =>
        (HessianTheorem11.hessian (map (Int.castRingHom (ZMod p)) F) x).rank = ρ).card
          ≤ C * p ^ 9 := by
  classical
  obtain ⟨d, hd⟩ := exists_coeff_ne_zero hF
  exact ⟨coefficientConstant F d, coefficientConstant_pos F d hd,
    fun p hp _ => card_primeZeros_filter_le F d hd p hp _⟩

end CubicTenVariables.UniformPrimePolynomialZeros
