import CubicTenVariables.SquarefullWeightedSums
import CubicTenVariables.CubicPrimeFrogOneBound
import CubicTenVariables.PrimeFactorEpsilonBound
import Mathlib.Data.Nat.Factorization.Induction

/-! Exact CRT and squarefree bounds for the full gcd-weighted Hessian root mass. -/

noncomputable section
namespace CubicTenVariables.GcdWeightedHessianCRT
open MvPolynomial HessianTheorem11 SquarefreeResidueFactors PrimeFrogZeroMass
open CRTCharacters WeightedHessianRootCRT SquarefullWeightedSums
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {v m n : ℕ}

theorem vectorGcd_eq_of_dvd_sub (d : ℕ) (x y : Fin v → ℤ)
    (h : ∀ i, (d : ℤ) ∣ x i - y i) : vectorGcd d x = vectorGcd d y := by
  have hdiv (x y : Fin v → ℤ) (h : ∀ i, (d : ℤ) ∣ x i-y i) :
      vectorGcd d x ∣ vectorGcd d y := by
    apply Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
    apply (dvd_content_iff _ y).mpr
    intro i
    have hx : ((vectorGcd d x : ℕ) : ℤ) ∣ x i :=
      (dvd_content_iff _ x).mp (Nat.gcd_dvd_right _ _) i
    have hd : ((vectorGcd d x : ℕ) : ℤ) ∣ (d : ℤ) := by
      exact_mod_cast Nat.gcd_dvd_left d (content x)
    have hh := dvd_sub hx (hd.trans (h i))
    simpa only [sub_sub_cancel] using hh
  exact Nat.dvd_antisymm (hdiv x y h) (hdiv y x (fun i => by
    simpa only [neg_sub] using dvd_neg.mpr (h i)))

theorem vectorGcd_eq_of_cast_eq (d : ℕ) (x y : Fin v → ℤ)
    (h : ∀ i, (x i : ZMod d) = (y i : ZMod d)) :
    vectorGcd d x = vectorGcd d y := by
  apply vectorGcd_eq_of_dvd_sub
  intro i
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, h i, sub_self]

theorem vectorGcd_mul (hc : m.Coprime n) (x : Fin v → ℤ) :
    vectorGcd (m*n) x = vectorGcd m x * vectorGcd n x := hc.mul_gcd _

/-- Evaluation on integral representatives commutes with any actual residue map. -/
theorem cast_eval_lift_map (F : MvPolynomial (Fin v) ℤ)
    (d e : ℕ) [NeZero d] [NeZero e] (f : ZMod d →+* ZMod e)
    (x : Fin v → ZMod d) :
    (eval (integerLift d x) F : ZMod e) =
      (eval (integerLift e (fun i => f (x i))) F : ZMod e) := by
  rw [cast_eval_integerLift F e]
  have h := congrArg f (cast_eval_integerLift F d x)
  simpa only [map_intCast, WeightedCRTAdapters.map_eval₂_int] using h

theorem vectorGcd_lift_map (d e : ℕ) [NeZero d] [NeZero e]
    (f : ZMod d →+* ZMod e) (x : Fin v → ZMod d) :
    vectorGcd e (integerLift d x) = vectorGcd e (integerLift e (fun i => f (x i))) := by
  apply vectorGcd_eq_of_cast_eq
  intro i
  simpa only [eval_X] using cast_eval_lift_map (X i : MvPolynomial (Fin v) ℤ) d e f x

theorem vectorGcd_gradient_map (F : MvPolynomial (Fin v) ℤ)
    (d e : ℕ) [NeZero d] [NeZero e] (f : ZMod d →+* ZMod e)
    (x : Fin v → ZMod d) :
    vectorGcd e (fun i => eval (integerLift d x) (pderiv i F)) =
      vectorGcd e (fun i => eval (integerLift e (fun j => f (x j))) (pderiv i F)) :=
  vectorGcd_eq_of_cast_eq e _ _ (fun i => cast_eval_lift_map (pderiv i F) d e f x)

/-- Both literal gcd factors split at the actual CRT projections. -/
theorem rootWeight_mul (F : MvPolynomial (Fin v) ℤ) [NeZero m] [NeZero n]
    (hc : m.Coprime n) (x : Fin v → ZMod (m*n)) :
    rootWeight F (m*n) x =
      rootWeight F m (fun i => leftProjection hc (x i)) *
        rootWeight F n (fun i => rightProjection hc (x i)) := by
  unfold rootWeight
  rw [vectorGcd_mul hc, vectorGcd_mul hc,
    vectorGcd_gradient_map F (m*n) m (leftProjection hc) x,
    vectorGcd_gradient_map F (m*n) n (rightProjection hc) x,
    vectorGcd_lift_map (m*n) m (leftProjection hc) x,
    vectorGcd_lift_map (m*n) n (rightProjection hc) x]
  ring

/-- Exact CRT for the full gcd-weighted root mass, with no degree hypothesis. -/
theorem gcdRootMass_mul (F : MvPolynomial (Fin v) ℤ) [NeZero m] [NeZero n]
    (hc : m.Coprime n) :
    gcdRootMass F (m*n) = gcdRootMass F m * gcdRootMass F n := by
  unfold gcdRootMass
  calc
    _ = ∑ x : Fin v → ZMod (m*n),
        (if eval₂ (Int.castRingHom (ZMod m)) (fun i => leftProjection hc (x i)) F = 0 then
          kernelWeight F m (fun i => leftProjection hc (x i)) *
            (rootWeight F m (fun i => leftProjection hc (x i)) : ℝ) else 0) *
        (if eval₂ (Int.castRingHom (ZMod n)) (fun i => rightProjection hc (x i)) F = 0 then
          kernelWeight F n (fun i => rightProjection hc (x i)) *
            (rootWeight F n (fun i => rightProjection hc (x i)) : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [PolynomialResidueCRT.zero_crt_iff F hc, kernelWeight_mul F hc,
        rootWeight_mul F hc, Nat.cast_mul]
      split_ifs <;> simp_all [mul_comm, mul_left_comm, mul_assoc]
    _ = _ := WeightedCRTAdapters.sum_crt_product hc
      (fun x => if eval₂ (Int.castRingHom (ZMod m)) x F = 0 then
        kernelWeight F m x * (rootWeight F m x : ℝ) else 0)
      (fun x => if eval₂ (Int.castRingHom (ZMod n)) x F = 0 then
        kernelWeight F n x * (rootWeight F n x : ℝ) else 0)

@[simp] theorem gcdRootMass_one (F : MvPolynomial (Fin v) ℤ) : gcdRootMass F 1 = 1 := by
  have hk (x : Fin v → ZMod 1) : HessianKernelCRT.hessianKernelCard F 1 x = 1 := by
    unfold HessianKernelCRT.hessianKernelCard
    have hz (z : Fin v → ZMod 1) :
        (hessian (map (Int.castRingHom (ZMod 1)) F) x).mulVec z = 0 := Subsingleton.elim _ _
    simp only [hz, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_true,
      Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card, one_pow]
  have hz (x : Fin v → ZMod 1) : eval₂ (Int.castRingHom (ZMod 1)) x F = 0 :=
    Subsingleton.elim _ _
  simp [gcdRootMass, hz, kernelWeight, hk, rootWeight, vectorGcd]

/-- A totalized scalar function, used only for the elementary factorization induction. -/
private def totalMass (F : MvPolynomial (Fin v) ℤ) (d : ℕ) : ℝ :=
  if hd : d = 0 then 0 else @gcdRootMass v F d ⟨hd⟩

private theorem totalMass_eq (F : MvPolynomial (Fin v) ℤ) (d : ℕ) [NeZero d] :
    totalMass F d = gcdRootMass F d := by simp only [totalMass, dif_neg (NeZero.ne d)]

private theorem totalMass_mul (F : MvPolynomial (Fin v) ℤ)
    (m n : ℕ) (hc : m.Coprime n) : totalMass F (m*n) = totalMass F m * totalMass F n := by
  by_cases hm : m = 0
  · subst m; simp [totalMass]
  by_cases hn : n = 0
  · subst n; simp [totalMass]
  letI : NeZero m := ⟨hm⟩
  letI : NeZero n := ⟨hn⟩
  simpa only [totalMass_eq] using gcdRootMass_mul F hc

private theorem totalMass_squarefree (F : MvPolynomial (Fin v) ℤ)
    (d : ℕ) (hd : Squarefree d) : totalMass F d = ∏ p ∈ d.primeFactors, totalMass F p := by
  have h := Nat.multiplicative_factorization (totalMass F) (totalMass_mul F)
    (by rw [totalMass_eq, gcdRootMass_one]) hd.ne_zero
  rw [Nat.prod_factorization_eq_prod_primeFactors] at h
  rw [h]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.factorization_eq_one_of_squarefree hd (Nat.prime_of_mem_primeFactors hp)
    (Nat.dvd_of_mem_primeFactors hp), pow_one]

/-- The prime j=1 theorem is a bound for exactly this literal full gcd mass. -/
theorem exists_uniform_prime_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : ℕ) (hp : p.Prime),
      letI : NeZero p := ⟨hp.ne_zero⟩
      gcdRootMass F p ≤ C*(p : ℝ)^((21 : ℝ)/2) := by
  obtain ⟨C,hC,hbound⟩ := CubicPrimeFrogOneBound.exists_uniform_sqrt_bound F hF hA
  refine ⟨C,hC,?_⟩
  intro p hp
  letI : NeZero p := ⟨hp.ne_zero⟩
  simpa only [PrimeFrogOneMass.oneMass, PrimeFrogOneMass.optionalRootWeight_true_true,
    Finset.sum_filter, gcdRootMass, kernelWeight, mul_comm] using hbound p hp true true

/-- One constant covers every positive squarefree modulus, including one.
All primes are included; no literature or prime-exception input occurs. -/
theorem exists_uniform_squarefree_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d : ℕ) [NeZero d], Squarefree d →
      gcdRootMass F d ≤ C*(d : ℝ)^((21 : ℝ)/2+ε) := by
  obtain ⟨C,hC,hprime⟩ := exists_uniform_prime_bound F hF hA
  let K : ℕ := ⌈C⌉₊
  have hK : C ≤ (K : ℝ) := Nat.le_ceil C
  have hK1 : 1 ≤ K := Nat.one_le_ceil_iff.mpr (zero_lt_one.trans_le hC)
  obtain ⟨B,hB,hcoeff⟩ := PrimeFactorEpsilonBound.exists_uniform_prime_factor_bound K hK1 ε hε
  refine ⟨B,hB,?_⟩
  intro d hd0 hd
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hdpos
  have hlocal (p : ℕ) (hp : p ∈ d.primeFactors) :
      totalMass F p ≤ (K : ℝ)*(p : ℝ)^((21 : ℝ)/2) := by
    have hp' := Nat.prime_of_mem_primeFactors hp
    letI : NeZero p := ⟨hp'.ne_zero⟩
    rw [totalMass_eq]
    exact (hprime p hp').trans
      (mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg (Nat.cast_nonneg p) _))
  have hc : (∏ p ∈ d.primeFactors, (K : ℝ)) ≤ B*(d : ℝ)^ε := by
    have h := hcoeff d hdpos
    have he : ((∏ p ∈ d.primeFactors, K*d.factorization p : ℕ) : ℝ) =
        ∏ p ∈ d.primeFactors, (K : ℝ) := by
      rw [Nat.cast_prod]
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.factorization_eq_one_of_squarefree hd (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp), Nat.mul_one]
    rwa [he] at h
  have hpowers : (∏ p ∈ d.primeFactors, (p : ℝ)^((21 : ℝ)/2)) =
      (d : ℝ)^((21 : ℝ)/2) := by
    rw [Real.finset_prod_rpow _ _ (fun p _ => Nat.cast_nonneg p)]
    congr 1
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd]
  rw [← totalMass_eq, totalMass_squarefree F d hd]
  calc
    _ ≤ ∏ p ∈ d.primeFactors, (K : ℝ)*(p : ℝ)^((21 : ℝ)/2) := by
      apply Finset.prod_le_prod
      · intro p hp
        letI : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
        rw [totalMass_eq]
        exact gcdRootMass_nonneg F p
      · exact hlocal
    _ = (∏ p ∈ d.primeFactors, (K : ℝ)) * (d : ℝ)^((21 : ℝ)/2) := by
      rw [Finset.prod_mul_distrib, hpowers]
    _ ≤ (B*(d : ℝ)^ε) * (d : ℝ)^((21 : ℝ)/2) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hdR.le _)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hdR]; congr 2; ring

end CubicTenVariables.GcdWeightedHessianCRT
