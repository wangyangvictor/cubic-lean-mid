import CubicTenVariables.AdmissibleSmithCount
import CubicTenVariables.PrimePowerKernelProfile

/-! The exact admissible low-digit count in terms of the actual truncated
prime valuations of an integral diagonal. The diagonal is proved to exist
and is chosen before the prime, exponents, linear frequency, and unit.
-/

noncomputable section
namespace CubicTenVariables.AdmissiblePrimePowerCount
open AdmissibleSmithCount PrimePowerKernelProfile
open scoped BigOperators Matrix

/-- Scaling by p^b adds b to the valuation before truncation, including zero entries. -/
theorem truncatedValuation_primePower_mul (p a b : ℕ) (hp : p.Prime) (d : ℤ) :
    truncatedValuation p a (((p^b : ℕ) : ℤ) * d) =
      min (b + truncatedValuation p a d) a := by
  by_cases hd : d = 0
  · simp [hd, truncatedValuation]
  · have hpz : (((p^b : ℕ) : ℤ)) ≠ 0 := by exact_mod_cast pow_ne_zero b hp.ne_zero
    have hpd : (((p^b : ℕ) : ℤ) * d) ≠ 0 := mul_ne_zero hpz hd
    have hdabs : d.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hd
    simp only [truncatedValuation, if_neg hd, if_neg hpd, Int.natAbs_mul,
      Int.natAbs_natCast, Nat.factorization_mul (pow_ne_zero b hp.ne_zero) hdabs,
      Finsupp.add_apply, Nat.factorization_pow_self hp]
    omega

/-- The elementary exponent cancellation needed after the exact kernel-count ratio. -/
theorem admissible_exponent_identity {n : ℕ} (a b : ℕ) (j : Fin n → ℕ)
    (hj : ∀ i, j i ≤ a) :
    (∑ i, (b - min b (a - j i))) + (∑ i, min (b + j i) a) =
      b*n + ∑ i, j i := by
  rw [← Finset.sum_add_distrib]
  calc
    ∑ i, ((b - min b (a - j i)) + min (b + j i) a) =
        ∑ i, (b + j i) := by
      apply Finset.sum_congr rfl
      intro i _
      have hi := hj i
      omega
    _ = _ := by simp [Finset.sum_add_distrib, mul_comm]

/-- The exact admissible count from a displayed actual integral diagonalization. -/
theorem admissible_fin_primePower_count_of_diagonalization {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℤ)
    (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ) (d : Fin n → ℤ)
    (hD : (U : Matrix (Fin n) (Fin n) ℤ) * B * V = Matrix.diagonal d)
    (p : ℕ) (hp : p.Prime) (a b : ℕ)
    (ell : Fin n → ZMod (p^a)) (alpha : (ZMod (p^a))ˣ) :
    let H := B.map (Int.castRingHom (ZMod (p^a)))
    let K := Nat.card {v : Fin n → Fin (p^b) // ∃ x : Fin n → ZMod (p^a),
      ((p^b : ZMod (p^a)) • H).mulVec x =
        ell + (alpha : ZMod (p^a)) • H.mulVec (fun i => ((v i).val : ZMod (p^a)))}
    K = 0 ∨ K = ∏ i, p ^ (b - min b (a - truncatedValuation p a (d i))) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have h := admissible_fin_gcd_ratio_of_diagonalization B U V d hD (p^a) (p^b) ell alpha
  dsimp only at h ⊢
  simp_rw [gcd_primePower p a hp, truncatedValuation_primePower_mul p a b hp] at h
  simp only [Nat.cast_pow] at h
  simp_rw [Finset.prod_pow_eq_pow_sum] at h
  rcases h with hz | hratio
  · exact Or.inl hz
  · right
    rw [Finset.prod_pow_eq_pow_sum]
    apply Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos (∑ i, min (b + truncatedValuation p a (d i)) a))
    calc
      _ = (p^b)^n * p^(∑ i, truncatedValuation p a (d i)) := by
        simpa only [Nat.cast_pow] using hratio
      _ = p ^ (b*n + ∑ i, truncatedValuation p a (d i)) := by rw [← pow_mul, pow_add]
      _ = _ := by
        rw [← admissible_exponent_identity a b (fun i => truncatedValuation p a (d i))
          (fun i => truncatedValuation_le p a (d i)), pow_add]

/-- Actual unimodular diagonalization and its exact admissible count,
with the same diagonal chosen before all primes and exponents. -/
theorem exists_diagonalization_and_admissible_primePower_count {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℤ) :
    ∃ (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ) (d : Fin n → ℤ),
      (U : Matrix (Fin n) (Fin n) ℤ) * B * V = Matrix.diagonal d ∧
      ∀ (p : ℕ), p.Prime → ∀ (a b : ℕ),
      ∀ (ell : Fin n → ZMod (p^a)) (alpha : (ZMod (p^a))ˣ),
      let H := B.map (Int.castRingHom (ZMod (p^a)))
      let K := Nat.card {v : Fin n → Fin (p^b) // ∃ x : Fin n → ZMod (p^a),
        ((p^b : ZMod (p^a)) • H).mulVec x =
          ell + (alpha : ZMod (p^a)) • H.mulVec (fun i => ((v i).val : ZMod (p^a)))}
      K = 0 ∨ K = ∏ i, p ^ (b - min b (a - truncatedValuation p a (d i))) := by
  obtain ⟨U,V,d,hD⟩ := MatrixSmithExistence.exists_integer_diagonalization B
  exact ⟨U,V,d,hD,admissible_fin_primePower_count_of_diagonalization B U V d hD⟩

/-- The exact manuscript count for the original canonical representatives:
zero, or ∏ p^(b-min(b,a-j_i)). The actual integral diagonal is chosen before
all primes and exponents, with j_i its literal truncated valuation at p^a. -/
theorem exists_admissible_fin_primePower_count {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℤ) :
    ∃ d : Fin n → ℤ, ∀ (p : ℕ), p.Prime → ∀ (a b : ℕ),
      ∀ (ell : Fin n → ZMod (p^a)) (alpha : (ZMod (p^a))ˣ),
      let H := B.map (Int.castRingHom (ZMod (p^a)))
      let K := Nat.card {v : Fin n → Fin (p^b) // ∃ x : Fin n → ZMod (p^a),
        ((p^b : ZMod (p^a)) • H).mulVec x =
          ell + (alpha : ZMod (p^a)) • H.mulVec (fun i => ((v i).val : ZMod (p^a)))}
      K = 0 ∨ K = ∏ i, p ^ (b - min b (a - truncatedValuation p a (d i))) := by
  obtain ⟨U,V,d,hD,hd⟩ := exists_diagonalization_and_admissible_primePower_count B
  exact ⟨d,hd⟩

end CubicTenVariables.AdmissiblePrimePowerCount
