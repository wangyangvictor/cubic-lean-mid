import CubicTenVariables.PrimeSumAdapter
import CubicTenVariables.CubicGradientScaling

/-! Exact scalar averaging on homogeneous affine zero sets. All counts
are literal finite-field point counts. There is no point-count estimate or
literature premise, and the character uses the project's positive sign. -/

noncomputable section
namespace CubicTenVariables.PrimeScalarAveraging
open MvPolynomial FiniteFieldFourier
open scoped BigOperators

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {n d : ℕ}

theorem sum_nonzero_scalar_phase (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (b : k) :
    (∑ a ∈ Finset.univ.filter (fun a : k => a ≠ 0), ψ (a*b)) =
      (if b=0 then (Fintype.card k : ℂ) else 0)-1 := by
  classical
  have he := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun a : k => a ≠ 0) (fun a => ψ (a*b))
  have hz : (∑ a ∈ Finset.univ.filter (fun a : k => ¬a≠0), ψ (a*b))=1 := by
    simp [Finset.sum_filter]
  rw [hz,sum_scalar_phase ψ hψ b] at he
  exact eq_sub_of_add_eq he

/-- Scalar multiplication is a genuine bijection of the actual zero set. -/
theorem zeroFiberSum_scalar_phase (ψ : AddChar k ℂ)
    (F : MvPolynomial (Fin n) k) (hF : F.IsHomogeneous d)
    (v : Fin n → k) (a : k) (ha : a ≠ 0) :
    (∑ x ∈ Finset.univ.filter (fun x : Fin n → k => eval x F=0),
      ψ (a * dotProduct v x)) = zeroFiberSum ψ F v := by
  classical
  unfold zeroFiberSum
  simp only [Finset.sum_filter]
  apply Fintype.sum_equiv (LinearEquiv.smulOfNeZero k (Fin n → k) a ha).toEquiv _ _
  intro x
  have he : eval (a • x) F = a^d * eval x F := by
    simpa only [eval₂_id] using
      CubicGradientScaling.homogeneous_eval₂_smul F hF (RingHom.id k) x a
  have hz : eval (a • x) F=0 ↔ eval x F=0 := by
    rw [he,mul_eq_zero]
    simp [pow_ne_zero d ha]
  simp only [LinearEquiv.coe_toEquiv,LinearEquiv.smulOfNeZero_apply,
    hz,dotProduct_smul,smul_eq_mul]

theorem zeroFiberSum_zero (ψ : AddChar k ℂ) (F : MvPolynomial (Fin n) k) :
    zeroFiberSum ψ F 0 = (Nat.card {x : Fin n → k // eval x F=0} : ℂ) := by
  classical
  simp [zeroFiberSum,Nat.card_eq_fintype_card,Fintype.card_subtype]
  congr 1
  ext x
  simp

/-- Scalar averaging is valid at every frequency, including zero. The
homogeneity degree may be arbitrary. -/
theorem scalar_average (ψ : AddChar k ℂ) (hψ : ψ ≠ 1)
    (F : MvPolynomial (Fin n) k) (hF : F.IsHomogeneous d) (v : Fin n → k) :
    ((Fintype.card k : ℂ)-1) * zeroFiberSum ψ F v =
      (Fintype.card k : ℂ) *
        (Nat.card {x : Fin n → k // eval x F=0 ∧ dotProduct v x=0} : ℂ) -
      (Nat.card {x : Fin n → k // eval x F=0} : ℂ) := by
  classical
  have hcard : ((Finset.univ.filter (fun a : k => a≠0)).card : ℂ) =
      (Fintype.card k : ℂ)-1 := by
    have he := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun a : k => a≠0) (fun _ => (1 : ℂ))
    have hz : (∑ a ∈ Finset.univ.filter (fun a : k => ¬a≠0), (1 : ℂ))=1 := by
      have hset : Finset.univ.filter (fun a : k => ¬a≠0) = {0} := by
        ext x
        simp
      rw [hset]
      simp
    rw [hz] at he
    simp only [Finset.sum_const,nsmul_eq_mul,mul_one,Finset.card_univ] at he
    exact eq_sub_of_add_eq he
  calc
    _ = ∑ a ∈ Finset.univ.filter (fun a : k => a≠0), zeroFiberSum ψ F v := by
      rw [Finset.sum_const,nsmul_eq_mul,hcard]
    _ = ∑ a ∈ Finset.univ.filter (fun a : k => a≠0),
        ∑ x ∈ Finset.univ.filter (fun x : Fin n → k => eval x F=0),
          ψ (a*dotProduct v x) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (zeroFiberSum_scalar_phase ψ F hF v a (Finset.mem_filter.mp ha).2).symm
    _ = ∑ x ∈ Finset.univ.filter (fun x : Fin n → k => eval x F=0),
        ∑ a ∈ Finset.univ.filter (fun a : k => a≠0), ψ (a*dotProduct v x) :=
      Finset.sum_comm
    _ = ∑ x ∈ Finset.univ.filter (fun x : Fin n → k => eval x F=0),
        ((if dotProduct v x=0 then (Fintype.card k : ℂ) else 0)-1) := by
      simp_rw [sum_nonzero_scalar_phase ψ hψ]
    _ = _ := by
      rw [Finset.sum_sub_distrib,← Finset.sum_filter]
      simp only [Finset.filter_filter,Finset.sum_const,nsmul_eq_mul]
      simp [Nat.card_eq_fintype_card,Fintype.card_subtype,mul_comm]

theorem completeSum_zero (ψ : AddChar k ℂ) (hψ : ψ ≠ 1)
    (F : MvPolynomial (Fin n) k) :
    completeSum ψ F 0 = (Fintype.card k : ℂ) *
      (Nat.card {x : Fin n → k // eval x F=0} : ℂ) - (Fintype.card k : ℂ)^n := by
  have he := completeSum_add_linear_phase ψ hψ F 0
  rw [zeroFiberSum_zero] at he
  have hz : (∑ x : Fin n → k, ψ (dotProduct 0 x))=(Fintype.card k : ℂ)^n := by
    simp
  rw [hz] at he
  exact eq_sub_of_add_eq he

/-- The standard prime-field version, with no supplied character premise. -/
theorem prime_scalar_average (p : ℕ) [Fact p.Prime]
    (F : MvPolynomial (Fin n) (ZMod p)) (hF : F.IsHomogeneous d)
    (v : Fin n → ZMod p) :
    ((p : ℂ)-1) * zeroFiberSum ZMod.stdAddChar F v =
      (p : ℂ) * (Nat.card {x : Fin n → ZMod p // eval x F=0 ∧ dotProduct v x=0} : ℂ) -
      (Nat.card {x : Fin n → ZMod p // eval x F=0} : ℂ) := by
  simpa only [ZMod.card] using
    scalar_average ZMod.stdAddChar (PrimeSumAdapter.stdAddChar_ne_one p) F hF v

theorem completeCubicSum_nonzero_mul (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous d) (p : ℕ) [Fact p.Prime] (v : Fin n → ℤ)
    (hv : (fun i => (v i : ZMod p)) ≠ 0) :
    ((p : ℂ)-1) * completeCubicSum F p v =
      (p : ℂ)^2 * (Nat.card {x : Fin n → ZMod p //
        eval₂ (Int.castRingHom (ZMod p)) x F=0 ∧
        dotProduct (fun i => (v i : ZMod p)) x=0} : ℂ) -
      (p : ℂ) * (Nat.card {x : Fin n → ZMod p //
        eval₂ (Int.castRingHom (ZMod p)) x F=0} : ℂ) := by
  rw [PrimeSumAdapter.completeCubicSum_eq_prime_mul_zeroFiberSum F p v hv]
  have he := prime_scalar_average p (map (Int.castRingHom (ZMod p)) F)
    (hF.map _) (fun i => (v i : ZMod p))
  simp only [eval_map] at he
  linear_combination (p : ℂ)*he

theorem completeCubicSum_zero (F : MvPolynomial (Fin n) ℤ)
    (p : ℕ) [Fact p.Prime] :
    completeCubicSum F p 0 = (p : ℂ) *
      (Nat.card {x : Fin n → ZMod p // eval₂ (Int.castRingHom (ZMod p)) x F=0} : ℂ) -
      (p : ℂ)^n := by
  rw [PrimeSumAdapter.completeCubicSum_eq_finiteFieldCompleteSum]
  simpa only [Pi.zero_apply,Int.cast_zero,ZMod.card,eval_map] using
    completeSum_zero ZMod.stdAddChar (PrimeSumAdapter.stdAddChar_ne_one p)
      (map (Int.castRingHom (ZMod p)) F)

/-- An integer frequency divisible coordinatewise by p gives exactly the
zero-frequency sum, without any homogeneity assumption. -/
theorem completeCubicSum_of_frequency_mod_zero (F : MvPolynomial (Fin n) ℤ)
    (p : ℕ) [Fact p.Prime] (v : Fin n → ℤ)
    (hv : (fun i => (v i : ZMod p))=0) :
    completeCubicSum F p v = (p : ℂ) *
      (Nat.card {x : Fin n → ZMod p // eval₂ (Int.castRingHom (ZMod p)) x F=0} : ℂ) -
      (p : ℂ)^n := by
  rw [PrimeSumAdapter.completeCubicSum_eq_finiteFieldCompleteSum,hv]
  simpa only [ZMod.card,eval_map] using
    completeSum_zero ZMod.stdAddChar (PrimeSumAdapter.stdAddChar_ne_one p)
      (map (Int.castRingHom (ZMod p)) F)

/-- The divided affine-count identity, with p-1 proved nonzero. -/
theorem completeCubicSum_nonzero (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous d) (p : ℕ) [Fact p.Prime] (v : Fin n → ℤ)
    (hv : (fun i => (v i : ZMod p)) ≠ 0) :
    completeCubicSum F p v =
      ((p : ℂ)^2 * (Nat.card {x : Fin n → ZMod p //
        eval₂ (Int.castRingHom (ZMod p)) x F=0 ∧
        dotProduct (fun i => (v i : ZMod p)) x=0} : ℂ) -
      (p : ℂ) * (Nat.card {x : Fin n → ZMod p //
        eval₂ (Int.castRingHom (ZMod p)) x F=0} : ℂ))/((p : ℂ)-1) := by
  have hp1 : (p : ℂ)-1 ≠ 0 := sub_ne_zero.mpr (by
    exact_mod_cast (Fact.out : p.Prime).ne_one)
  apply (eq_div_iff hp1).mpr
  rw [mul_comm]
  exact completeCubicSum_nonzero_mul F hF p v hv

end CubicTenVariables.PrimeScalarAveraging
