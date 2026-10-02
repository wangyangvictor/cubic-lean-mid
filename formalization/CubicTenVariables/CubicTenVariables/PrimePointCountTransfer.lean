import CubicTenVariables.PrimeScalarAveraging
import CubicTenVariables.QuadraticGaussBound

/-! Assembly of literal affine point-count errors into prime complete-sum
bounds. The point-count estimates remain explicit hypotheses of these
helpers. No literature proposition is assumed by this module. -/

noncomputable section
namespace CubicTenVariables.PrimePointCountTransfer
open MvPolynomial PrimeScalarAveraging
open scoped BigOperators

theorem norm_count_sub_pow (N p e : ℕ) :
    ‖(N : ℂ)-(p : ℂ)^e‖ = |(N : ℝ)-(p : ℝ)^e| := by
  have he : (N : ℂ)-(p : ℂ)^e = ((N : ℝ)-(p : ℝ)^e : ℝ) := by push_cast; rfl
  rw [he,Complex.norm_real,Real.norm_eq_abs]

/-- Triangle inequality applied to every actual scalar and vector term. -/
theorem trivial_bound {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (p : ℕ) [Fact p.Prime] (v : Fin n → ℤ) :
    ‖completeCubicSum F p v‖ ≤ (p : ℝ)^(n+1) := by
  classical
  unfold completeCubicSum
  calc
    _ ≤ ∑ a : Fin p, ‖if Nat.Coprime a.val p then
        ∑ x : Fin n → Fin p, residueExponential p (completeSumPhase F a x v) else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _a : Fin p, (p : ℝ)^n := by
      apply Finset.sum_le_sum
      intro a _
      split_ifs
      · apply (norm_sum_le _ _).trans
        simp only [PrimeSumAdapter.residueExponential_eq_stdAddChar,
          QuadraticGaussBound.norm_stdAddChar,Finset.sum_const,Finset.card_univ,
          Fintype.card_fun,Fintype.card_fin,nsmul_eq_mul,mul_one,Nat.cast_pow]
        exact le_rfl
      · simp
    _ = _ := by simp [pow_succ,mul_comm]

theorem zero_frequency_bound (F : MvPolynomial (Fin 10) ℤ)
    (p : ℕ) [Fact p.Prime] (v : Fin 10 → ℤ)
    (hv : (fun i => (v i : ZMod p))=0) (A : ℝ) (hA : 0 ≤ A)
    (hcount : |(Nat.card {x : Fin 10 → ZMod p //
      eval₂ (Int.castRingHom (ZMod p)) x F=0} : ℝ)-(p : ℝ)^9| ≤
        A*((p : ℝ)-1)*(p : ℝ)^((13 : ℝ)/2)) :
    ‖completeCubicSum F p v‖ ≤ A*(p : ℝ)^((17 : ℝ)/2) := by
  let N := Nat.card {x : Fin 10 → ZMod p // eval₂ (Int.castRingHom (ZMod p)) x F=0}
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hid : completeCubicSum F p v = (p : ℂ)*((N : ℂ)-(p : ℂ)^9) := by
    rw [completeCubicSum_of_frequency_mod_zero F p v hv]
    dsimp [N]
    ring
  rw [hid,norm_mul,Complex.norm_natCast,norm_count_sub_pow]
  calc
    (p : ℝ)*|(N : ℝ)-(p : ℝ)^9| ≤
        (p : ℝ)*(A*((p : ℝ)-1)*(p : ℝ)^((13 : ℝ)/2)) :=
      mul_le_mul_of_nonneg_left hcount hp.le
    _ ≤ A*(p : ℝ)^2*(p : ℝ)^((13 : ℝ)/2) := by
      have hpow : 0 ≤ (p : ℝ)^((13 : ℝ)/2) := Real.rpow_nonneg hp.le _
      nlinarith [mul_nonneg (mul_nonneg hA hp.le) hpow]
    _ = A*(p : ℝ)^((17 : ℝ)/2) := by
      rw [mul_assoc,← Real.rpow_natCast (p : ℝ) 2,← Real.rpow_add hp]
      norm_num

theorem nonzero_frequency_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (p : ℕ) [Fact p.Prime] (v : Fin 10 → ℤ)
    (hv : (fun i => (v i : ZMod p))≠0) (A B : ℝ) (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hcount : |(Nat.card {x : Fin 10 → ZMod p //
      eval₂ (Int.castRingHom (ZMod p)) x F=0} : ℝ)-(p : ℝ)^9| ≤
        A*((p : ℝ)-1)*(p : ℝ)^((13 : ℝ)/2))
    (hsection : |(Nat.card {x : Fin 10 → ZMod p //
      eval₂ (Int.castRingHom (ZMod p)) x F=0 ∧
        dotProduct (fun i => (v i : ZMod p)) x=0} : ℝ)-(p : ℝ)^8| ≤
          B*((p : ℝ)-1)*(p : ℝ)^6) :
    ‖completeCubicSum F p v‖ ≤ (A+B)*(p : ℝ)^8 := by
  let N := Nat.card {x : Fin 10 → ZMod p // eval₂ (Int.castRingHom (ZMod p)) x F=0}
  let H := Nat.card {x : Fin 10 → ZMod p // eval₂ (Int.castRingHom (ZMod p)) x F=0 ∧
    dotProduct (fun i => (v i : ZMod p)) x=0}
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp : 0 < (p : ℝ) := lt_trans zero_lt_one hp1
  have hid : ((p : ℂ)-1)*completeCubicSum F p v =
      (p : ℂ)^2*((H : ℂ)-(p : ℂ)^8)-(p : ℂ)*((N : ℂ)-(p : ℂ)^9) := by
    have he := completeCubicSum_nonzero_mul F hF p v hv
    dsimp [H,N]
    linear_combination he
  have hpm : ‖(p : ℂ)-1‖=(p : ℝ)-1 := by
    have he : (p : ℂ)-1 = ((p : ℝ)-1 : ℝ) := by push_cast; rfl
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr hp1)]
  have hnorm : ((p : ℝ)-1)*‖completeCubicSum F p v‖ ≤
      (p : ℝ)^2*|(H : ℝ)-(p : ℝ)^8|+(p : ℝ)*|(N : ℝ)-(p : ℝ)^9| := by
    have he := norm_sub_le ((p : ℂ)^2*((H : ℂ)-(p : ℂ)^8))
      ((p : ℂ)*((N : ℂ)-(p : ℂ)^9))
    rw [← hid,norm_mul,hpm] at he
    simpa only [norm_mul,norm_pow,Complex.norm_natCast,norm_count_sub_pow] using he
  have hpow : (p : ℝ)^((13 : ℝ)/2) ≤ (p : ℝ)^7 := by
    rw [← Real.rpow_natCast (p : ℝ) 7]
    exact Real.rpow_le_rpow_of_exponent_le hp1.le (by norm_num)
  have hbound : ((p : ℝ)-1)*‖completeCubicSum F p v‖ ≤
      ((p : ℝ)-1)*((A+B)*(p : ℝ)^8) := by
    calc
      _ ≤ (p : ℝ)^2*(B*((p : ℝ)-1)*(p : ℝ)^6)+
          (p : ℝ)*(A*((p : ℝ)-1)*(p : ℝ)^((13 : ℝ)/2)) :=
        hnorm.trans (add_le_add
          (mul_le_mul_of_nonneg_left hsection (sq_nonneg _))
          (mul_le_mul_of_nonneg_left hcount hp.le))
      _ ≤ (p : ℝ)^2*(B*((p : ℝ)-1)*(p : ℝ)^6)+
          (p : ℝ)*(A*((p : ℝ)-1)*(p : ℝ)^7) := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpow (mul_nonneg hA (sub_pos.mpr hp1).le)) hp.le)
      _ = _ := by ring
  exact (mul_le_mul_iff_right₀ (sub_pos.mpr hp1)).mp hbound

/-- A fixed excluded integer is absorbed in one constant. Both alternatives use
    the reduction of the frequency modulo the prime, including nonzero integer
    frequencies whose reduction is zero. -/
theorem exists_uniform_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (D : ℕ) (hD : 1 ≤ D)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcounts : ∀ p : ℕ, p.Prime → ¬ p ∣ D →
      |(Nat.card {x : Fin 10 → ZMod p //
        eval₂ (Int.castRingHom (ZMod p)) x F=0} : ℝ)-(p : ℝ)^9| ≤
          A*((p : ℝ)-1)*(p : ℝ)^((13 : ℝ)/2) ∧
      ∀ v : Fin 10 → ZMod p, v ≠ 0 →
        |(Nat.card {x : Fin 10 → ZMod p //
          eval₂ (Int.castRingHom (ZMod p)) x F=0 ∧ dotProduct v x=0} : ℝ)-
          (p : ℝ)^8| ≤ B*((p : ℝ)-1)*(p : ℝ)^6) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p : ℕ, p.Prime → ∀ v : Fin 10 → ℤ,
      ((fun i => (v i : ZMod p))=0 →
        ‖completeCubicSum F p v‖ ≤ C*(p : ℝ)^((17 : ℝ)/2)) ∧
      ((fun i => (v i : ZMod p))≠0 →
        ‖completeCubicSum F p v‖ ≤ C*(p : ℝ)^8) := by
  let C : ℝ := 1+A+B+(D : ℝ)^11
  have hDpow : 0 ≤ (D : ℝ)^11 := pow_nonneg (Nat.cast_nonneg _) _
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hCA : A ≤ C := by dsimp [C]; linarith
  have hCAB : A+B ≤ C := by dsimp [C]; linarith
  have hCD : (D : ℝ)^11 ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro p hp v
  letI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  have hp0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg _
  by_cases hbad : p ∣ D
  · have hpD : (p : ℝ) ≤ (D : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one hD) hbad
    have htriv : ‖completeCubicSum F p v‖ ≤ C :=
      (trivial_bound F p v).trans ((pow_le_pow_left₀ hp0 hpD 11).trans hCD)
    constructor
    · intro _
      exact htriv.trans (le_mul_of_one_le_right (zero_le_one.trans hC)
        (Real.one_le_rpow hp1 (by norm_num)))
    · intro _
      exact htriv.trans (le_mul_of_one_le_right (zero_le_one.trans hC)
        (one_le_pow₀ hp1))
  · obtain ⟨hambient,hsection⟩ := hcounts p hp hbad
    constructor
    · intro hv
      exact (zero_frequency_bound F p v hv A hA hambient).trans
        (mul_le_mul_of_nonneg_right hCA (Real.rpow_nonneg hp0 _))
    · intro hv
      exact (nonzero_frequency_bound F hF p v hv A B hA hB hambient
        (hsection (fun i => (v i : ZMod p)) hv)).trans
        (mul_le_mul_of_nonneg_right hCAB (pow_nonneg hp0 _))

end CubicTenVariables.PrimePointCountTransfer
