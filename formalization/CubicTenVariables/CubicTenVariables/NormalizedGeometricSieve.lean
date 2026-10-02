import CubicTenVariables.PolynomialDivisorBound
import CubicTenVariables.NormalizedModulusFibres
import CubicTenVariables.ResidueBoxCount
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Finite counting for normalized polynomial relations in translated boxes.
The base coordinates and every defining equation are literal. -/

noncomputable section
namespace CubicTenVariables.NormalizedGeometricSieve
open scoped BigOperators

/-- The coefficient variables are the selected base coordinates. -/
def relation {n d : ℕ} (β : Fin d ↪ Fin n)
    (P : Fin n → Polynomial (MvPolynomial (Fin d) ℤ)) (i : Fin n) :
    MvPolynomial (Fin n) ℤ :=
  (P i).eval₂ (MvPolynomial.rename β).toRingHom (MvPolynomial.X i)

def specialize {n d : ℕ} (P : Fin n → Polynomial (MvPolynomial (Fin d) ℤ))
    (y : Fin d → ℤ) (i : Fin n) : Polynomial ℤ :=
  (P i).map (MvPolynomial.eval y)

def projectedPoint {n d : ℕ} {R : Type*} (β : Fin d ↪ Fin n)
    (j : Fin n) (x : Fin n → R) : Fin (d+1) → R :=
  Fin.cons (x j) (fun i => x (β i))

theorem eval_relation {n d : ℕ} (β : Fin d ↪ Fin n)
    (P : Fin n → Polynomial (MvPolynomial (Fin d) ℤ)) (i : Fin n)
    (x : Fin n → ℤ) :
    MvPolynomial.eval x (relation β P i) =
      (specialize P (fun k => x (β k)) i).eval (x i) := by
  unfold relation specialize
  rw [Polynomial.eval_map,Polynomial.hom_eval₂,MvPolynomial.eval_X]
  congr 1
  apply RingHom.ext
  intro Q
  exact MvPolynomial.eval_rename β x Q

theorem specialize_degree {n d : ℕ}
    (P : Fin n → Polynomial (MvPolynomial (Fin d) ℤ)) (y : Fin d → ℤ)
    (i : Fin n) : (specialize P y i).natDegree ≤ (P i).natDegree :=
  Polynomial.natDegree_map_le

theorem specialize_coeff {n d : ℕ}
    (P : Fin n → Polynomial (MvPolynomial (Fin d) ℤ)) (y : Fin d → ℤ)
    (i : Fin n) (k : ℕ) (C : ℤ) (h : (P i).coeff k = MvPolynomial.C C) :
    (specialize P y i).coeff k = C := by
  simp [specialize,Polynomial.coeff_map,h]

theorem relation_eq_of_projectedPoint_eq {n d : ℕ} (β : Fin d ↪ Fin n)
    (P : Fin n → Polynomial (MvPolynomial (Fin d) ℤ)) (j : Fin n)
    (x y : Fin n → ℤ) (h : projectedPoint β j x=projectedPoint β j y) :
    MvPolynomial.eval x (relation β P j)=MvPolynomial.eval y (relation β P j) := by
  have hj : x j=y j := congrFun h 0
  have hb : (fun k => x (β k))=(fun k => y (β k)) :=
    funext fun k => congrFun h k.succ
  rw [eval_relation,eval_relation,hj,hb]

/-- The projected box has d+1 coordinates even if j is a base coordinate. -/
theorem projected_card_le {n d : ℕ} (β : Fin d ↪ Fin n) (j : Fin n)
    (S : Finset (Fin n → ℤ)) (m : ℕ) [NeZero m]
    (b : Fin n → ℤ) (u : Fin n → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hbox : ∀ x ∈ S, ∀ i, |(x i : ℝ)-u i| ≤ L)
    (hres : ∀ x ∈ S, ∀ i, (x i : ZMod m)=(b i : ZMod m)) :
    ((S.image (projectedPoint β j)).card : ℝ) ≤ (4*L/(m : ℝ)+3)^(d+1) := by
  classical
  apply ResidueBoxCount.card_le_of_constant_residue m _ (projectedPoint β j u) L hL
  · intro y hy i
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    refine Fin.cases ?_ (fun k => ?_) i
    · exact hbox x hx j
    · exact hbox x hx (β k)
  · intro y hy z hz i
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    refine Fin.cases ?_ (fun k => ?_) i
    · exact (hres x hx j).trans (hres w hw j).symm
    · exact (hres x hx (β k)).trans (hres w hw (β k)).symm

/-- Uniform subpower bound for the explicit modular fiber constant. -/
theorem exists_fiber_factor_bound (n D : ℕ) (hD : 1 ≤ D)
    (C : ℤ) (hC : C ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ q : ℕ, 1 ≤ q →
      (((7*C.natAbs*D^q.primeFactors.card)^n : ℕ) : ℝ) ≤ K*(q : ℝ)^ε := by
  classical
  let η : ℝ := ε / ((n : ℝ)+1)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨A,hA,hbound⟩ :=
    PrimeFactorEpsilonBound.exists_uniform_prime_factor_bound D hD η hη
  have hCa : 1 ≤ C.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hC)
  have hc : 1 ≤ (7*C.natAbs : ℕ) := by omega
  have hcR : 1 ≤ ((7*C.natAbs : ℕ) : ℝ) := by exact_mod_cast hc
  let K : ℝ := (((7*C.natAbs : ℕ) : ℝ)*A)^n
  have hK : 1 ≤ K := one_le_pow₀ (one_le_mul_of_one_le_of_one_le hcR hA)
  refine ⟨K,hK,?_⟩
  intro q hq
  have hq0 : q ≠ 0 := by omega
  have hqR : 1 ≤ (q : ℝ) := by exact_mod_cast hq
  have hpow : D^q.primeFactors.card ≤ ∏ p ∈ q.primeFactors, D*q.factorization p := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod'
    intro p hp
    have he := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hq0
      (Nat.dvd_of_mem_primeFactors hp)
    exact Nat.le_mul_of_pos_right D he
  have hweight : ((D^q.primeFactors.card : ℕ) : ℝ) ≤ A*(q : ℝ)^η :=
    (show ((D^q.primeFactors.card : ℕ) : ℝ) ≤
      ((∏ p ∈ q.primeFactors, D*q.factorization p : ℕ) : ℝ)
      by exact_mod_cast hpow).trans (hbound q hq)
  have hexp : η*(n : ℝ) ≤ ε := by
    have he : ((n : ℝ)+1)*η=ε := by dsimp [η]; field_simp
    nlinarith
  calc
    _ = ((((7*C.natAbs : ℕ) : ℝ))*((D^q.primeFactors.card : ℕ) : ℝ))^n := by
      push_cast
      rfl
    _ ≤ ((((7*C.natAbs : ℕ) : ℝ))*A*(q : ℝ)^η)^n := by
      apply pow_le_pow_left₀ (by positivity)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hweight (Nat.cast_nonneg _)
    _ = K*(q : ℝ)^(η*(n : ℝ)) := by
      rw [mul_pow,Real.rpow_mul_natCast (Nat.cast_nonneg q)]
    _ ≤ K*(q : ℝ)^ε := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hqR hexp) (zero_le_one.trans hK)

theorem card_fixed_base_modulus_le {n d : ℕ} (β : Fin d ↪ Fin n)
    (P : Fin n → Polynomial (MvPolynomial (Fin d) ℤ))
    (k : Fin n → ℕ) (D : ℕ) (C : ℤ) (hD : 1 ≤ D) (hC : C ≠ 0)
    (hdeg : ∀ i, i ∉ Set.range β → (P i).natDegree ≤ D)
    (hcoeff : ∀ i, i ∉ Set.range β → (P i).coeff (k i)=MvPolynomial.C C)
    (S : Finset (Fin n → ℤ)) (z : Fin n → ℤ)
    (q m : ℕ) (hq : Squarefree q) [NeZero m] (hcop : q.Coprime m)
    (b : Fin n → ℤ) (u : Fin n → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hsize : 1+L/(m : ℝ) ≤ (q : ℝ))
    (hfixed : ∀ x ∈ S, ∀ i, x (β i)=z (β i))
    (hbox : ∀ x ∈ S, ∀ i, |(x i : ℝ)-u i| ≤ L)
    (hres : ∀ x ∈ S, ∀ i, (x i : ZMod m)=(b i : ZMod m))
    (hroot : ∀ x ∈ S, ∀ i, (q : ℤ) ∣ MvPolynomial.eval x (relation β P i)) :
    S.card ≤ (7*C.natAbs*D^q.primeFactors.card)^n := by
  classical
  let J : Finset (Fin n) := Finset.univ.image β
  have hJ (i : Fin n) : i ∈ J ↔ i ∈ Set.range β := by simp [J]
  refine NormalizedModulusFibres.card_le_abs_coeff S J z
    (specialize P (fun i => z (β i))) k D C hD hC
    (fun i hi => (specialize_degree P _ i).trans (hdeg i (by simpa only [← hJ] using hi)))
    (fun i hi => specialize_coeff P _ i (k i) C (hcoeff i (by simpa only [← hJ] using hi)))
    q m hq hcop b u L hL hsize ?_ hbox hres ?_
  · intro x hx i hi
    obtain ⟨j,rfl⟩ := (hJ i).mp hi
    exact hfixed x hx j
  · intro x hx i _
    have heval := Polynomial.eval₂_at_apply
      (p := specialize P (fun j => z (β j)) i) (Int.castRingHom (ZMod q)) (x i)
    simp only [Int.coe_castRingHom] at heval
    rw [heval]
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    have he := hroot x hx i
    rw [eval_relation] at he
    have hb : (fun j => x (β j))=(fun j => z (β j)) := funext (hfixed x hx)
    simpa only [hb] using he

theorem card_fixed_base_zeros_le {n d : ℕ} (β : Fin d ↪ Fin n)
    (P : Fin n → Polynomial (MvPolynomial (Fin d) ℤ))
    (k : Fin n → ℕ) (D : ℕ) (C : ℤ) (hD : 1 ≤ D) (hC : C ≠ 0)
    (hdeg : ∀ i, i ∉ Set.range β → (P i).natDegree ≤ D)
    (hcoeff : ∀ i, i ∉ Set.range β → (P i).coeff (k i)=MvPolynomial.C C)
    (S : Finset (Fin n → ℤ)) (z : Fin n → ℤ)
    (hfixed : ∀ x ∈ S, ∀ i, x (β i)=z (β i))
    (hroot : ∀ x ∈ S, ∀ i, MvPolynomial.eval x (relation β P i)=0) :
    S.card ≤ D^n := by
  classical
  let J : Finset (Fin n) := Finset.univ.image β
  have hJ (i : Fin n) : i ∈ J ↔ i ∈ Set.range β := by simp [J]
  apply NormalizedModulusFibres.card_exact_zeros_le S J z
    (specialize P (fun i => z (β i))) k D C hD hC
    (fun i hi => (specialize_degree P _ i).trans (hdeg i (by simpa only [← hJ] using hi)))
    (fun i hi => specialize_coeff P _ i (k i) C (hcoeff i (by simpa only [← hJ] using hi)))
  · intro x hx i hi
    obtain ⟨j,rfl⟩ := (hJ i).mp hi
    exact hfixed x hx j
  · intro x hx i _
    have he := hroot x hx i
    rw [eval_relation] at he
    have hb : (fun j => x (β j))=(fun j => z (β j)) := funext (hfixed x hx)
    simpa only [hb] using he

/-- Fixing the base and one nonzero relation coordinate makes every
admissible modulus a divisor of one fixed nonzero integer. -/
theorem exists_fixed_key_bound {n d : ℕ} (β : Fin d ↪ Fin n)
    (P : Fin n → Polynomial (MvPolynomial (Fin d) ℤ))
    (k : Fin n → ℕ) (D : ℕ) (C : ℤ) (hD : 1 ≤ D) (hC : C ≠ 0)
    (hdeg : ∀ i, i ∉ Set.range β → (P i).natDegree ≤ D)
    (hcoeff : ∀ i, i ∉ Set.range β → (P i).coeff (k i)=MvPolynomial.C C)
    (j : Fin n) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (u : Fin n → ℝ) (L : ℝ), 1 ≤ L →
      ∀ (m : ℕ) [NeZero m] (b : Fin n → ℤ) (S0 : ℝ), 1+L/(m : ℝ) ≤ S0 →
      ∀ (S : Finset (Fin n → ℤ)) (z : Fin n → ℤ), z ∈ S →
      MvPolynomial.eval z (relation β P j) ≠ 0 →
      (∀ x ∈ S, projectedPoint β j x=projectedPoint β j z) →
      (∀ x ∈ S, ∀ i, |(x i : ℝ)-u i| ≤ L) →
      (∀ x ∈ S, ∀ i, (x i : ZMod m)=(b i : ZMod m)) →
      (∀ x ∈ S, ∃ q : ℕ, Squarefree q ∧ q.Coprime m ∧
        S0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ 2*S0 ∧
        ∀ i, (q : ℤ) ∣ MvPolynomial.eval x (relation β P i)) →
      (S.card : ℝ) ≤ K*(L+‖u‖)^ε*(2*S0)^ε := by
  classical
  obtain ⟨A,hA,hdiv⟩ := PolynomialDivisorBound.exists_translated_box_divisor_bound
    (relation β P j) ε hε
  obtain ⟨K,hK,hfactor⟩ := exists_fiber_factor_bound n D hD C hC ε hε
  refine ⟨A*K,one_le_mul_of_one_le_of_one_le hA hK,?_⟩
  intro u L hL m hm b S0 hS0 S z hz hnonzero hfixed hbox hres hadm
  let Q : Finset ℕ := (MvPolynomial.eval z (relation β P j)).natAbs.divisors.filter
    (fun (q : ℕ) => Squarefree q ∧ q.Coprime m ∧ S0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ 2*S0)
  let T (q : ℕ) := S.filter (fun x => ∀ i, (q : ℤ) ∣ MvPolynomial.eval x (relation β P i))
  have hQ (q : ℕ) (hq : q ∈ Q) : 0 < q ∧
      (q : ℤ) ∣ MvPolynomial.eval z (relation β P j) := by
    have he := (Finset.mem_filter.mp hq).1
    exact ⟨Nat.pos_of_mem_divisors he,Int.natCast_dvd.mpr (Nat.mem_divisors.mp he).1⟩
  have hcountQ : (Q.card : ℝ) ≤ A*(L+‖u‖)^ε :=
    hdiv u L hL z (hbox z hz) hnonzero Q hQ
  have hcover : S ⊆ Q.biUnion T := by
    intro x hx
    obtain ⟨q,hq,hcop,hlo,hhi,hroot⟩ := hadm x hx
    have hdvd : (q : ℤ) ∣ MvPolynomial.eval z (relation β P j) := by
      rw [← relation_eq_of_projectedPoint_eq β P j x z (hfixed x hx)]
      exact hroot j
    apply Finset.mem_biUnion.mpr
    refine ⟨q,?_,?_⟩
    · exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Int.natCast_dvd.mp hdvd,
        Int.natAbs_ne_zero.mpr hnonzero⟩,hq,hcop,hlo,hhi⟩
    · exact Finset.mem_filter.mpr ⟨hx,hroot⟩
  have hlocal (q : ℕ) (hq : q ∈ Q) : ((T q).card : ℝ) ≤ K*(2*S0)^ε := by
    obtain ⟨hqsf,hcop,hlo,hhi⟩ := (Finset.mem_filter.mp hq).2
    have hc := card_fixed_base_modulus_le β P k D C hD hC hdeg hcoeff
      (T q) z q m hqsf hcop b u L (zero_le_one.trans hL) (hS0.trans hlo)
      (fun x hx i => congrFun (hfixed x (Finset.mem_filter.mp hx).1) i.succ)
      (fun x hx => hbox x (Finset.mem_filter.mp hx).1)
      (fun x hx => hres x (Finset.mem_filter.mp hx).1)
      (fun x hx => (Finset.mem_filter.mp hx).2)
    exact (show ((T q).card : ℝ) ≤
      (((7*C.natAbs*D^q.primeFactors.card)^n : ℕ) : ℝ) by exact_mod_cast hc).trans
        ((hfactor q (hQ q hq).1).trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg q) hhi hε.le) (zero_le_one.trans hK)))
  have hcard : S.card ≤ ∑ q ∈ Q, (T q).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  calc
    (S.card : ℝ) ≤ ∑ q ∈ Q, ((T q).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ _q ∈ Q, K*(2*S0)^ε := Finset.sum_le_sum hlocal
    _ = (Q.card : ℝ)*(K*(2*S0)^ε) := by simp
    _ ≤ (A*(L+‖u‖)^ε)*(K*(2*S0)^ε) :=
      mul_le_mul_of_nonneg_right hcountQ
        (mul_nonneg (zero_le_one.trans hK) (Real.rpow_nonneg (by
          have hm0 : 0 < (m : ℝ) := by exact_mod_cast NeZero.pos m
          have he : 0 ≤ L/(m : ℝ) := div_nonneg (zero_le_one.trans hL) hm0.le
          linarith) _))
    _ = (A*K)*(L+‖u‖)^ε*(2*S0)^ε := by ring

private theorem card_le_image_card_mul {α γ : Type*} [DecidableEq α] [DecidableEq γ]
    (S : Finset α) (f : α → γ) (M : ℝ)
    (h : ∀ y ∈ S.image f, ((S.filter fun x => f x=y).card : ℝ) ≤ M) :
    (S.card : ℝ) ≤ ((S.image f).card : ℝ)*M := by
  rw [Finset.card_eq_sum_card_image f S,Nat.cast_sum]
  calc
    _ ≤ ∑ _y ∈ S.image f, M := Finset.sum_le_sum h
    _ = _ := by simp

private theorem parameter_one_le (m : ℕ) [NeZero m] (L S0 : ℝ)
    (hL : 1 ≤ L) (hS0 : 1+L/(m : ℝ) ≤ S0) : 1 ≤ S0 := by
  have hm : 0 < (m : ℝ) := by exact_mod_cast NeZero.pos m
  have hratio : 0 ≤ L/(m : ℝ) := div_nonneg (zero_le_one.trans hL) hm.le
  linarith

/-- Count all points for which one specified normalized relation is nonzero. -/
theorem exists_fixed_index_bound {n d : ℕ} (β : Fin d ↪ Fin n)
    (P : Fin n → Polynomial (MvPolynomial (Fin d) ℤ))
    (k : Fin n → ℕ) (D : ℕ) (C : ℤ) (hD : 1 ≤ D) (hC : C ≠ 0)
    (hdeg : ∀ i, i ∉ Set.range β → (P i).natDegree ≤ D)
    (hcoeff : ∀ i, i ∉ Set.range β → (P i).coeff (k i)=MvPolynomial.C C)
    (j : Fin n) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (u : Fin n → ℝ) (L : ℝ), 1 ≤ L →
      ∀ (m : ℕ) [NeZero m] (b : Fin n → ℤ) (S0 : ℝ), 1+L/(m : ℝ) ≤ S0 →
      ∀ S : Finset (Fin n → ℤ),
      (∀ x ∈ S, MvPolynomial.eval x (relation β P j) ≠ 0) →
      (∀ x ∈ S, ∀ i, |(x i : ℝ)-u i| ≤ L) →
      (∀ x ∈ S, ∀ i, (x i : ZMod m)=(b i : ZMod m)) →
      (∀ x ∈ S, ∃ q : ℕ, Squarefree q ∧ q.Coprime m ∧
        S0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ 2*S0 ∧
        ∀ i, (q : ℤ) ∣ MvPolynomial.eval x (relation β P i)) →
      (S.card : ℝ) ≤ K*(L+‖u‖)^ε*(2*S0)^ε*(4*L/(m : ℝ)+3)^(d+1) := by
  classical
  obtain ⟨K,hK,hbound⟩ := exists_fixed_key_bound β P k D C hD hC hdeg hcoeff j ε hε
  refine ⟨K,hK,?_⟩
  intro u L hL m hm b S0 hS0 S hnz hbox hres hadm
  have hS01 := parameter_one_le m L S0 hL hS0
  have hM : 0 ≤ K*(L+‖u‖)^ε*(2*S0)^ε := by
    apply mul_nonneg
    · exact mul_nonneg (zero_le_one.trans hK)
        (Real.rpow_nonneg (by linarith [norm_nonneg u]) _)
    · exact Real.rpow_nonneg (by linarith) _
  have hcard := card_le_image_card_mul S (projectedPoint β j)
    (K*(L+‖u‖)^ε*(2*S0)^ε) (by
      intro y hy
      obtain ⟨z,hz,hzy⟩ := Finset.mem_image.mp hy
      apply hbound u L hL m b S0 hS0 _ z
        (Finset.mem_filter.mpr ⟨hz,hzy⟩) (hnz z hz)
      · intro x hx
        exact (Finset.mem_filter.mp hx).2.trans hzy.symm
      · intro x hx
        exact hbox x (Finset.mem_filter.mp hx).1
      · intro x hx
        exact hres x (Finset.mem_filter.mp hx).1
      · intro x hx
        exact hadm x (Finset.mem_filter.mp hx).1)
  exact hcard.trans (by
    have he := mul_le_mul_of_nonneg_right
      (projected_card_le β j S m b u L (zero_le_one.trans hL) hbox hres) hM
    simpa only [mul_comm] using he)

private theorem base_card_le {n d : ℕ} (β : Fin d ↪ Fin n)
    (S : Finset (Fin n → ℤ)) (m : ℕ) [NeZero m]
    (b : Fin n → ℤ) (u : Fin n → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hbox : ∀ x ∈ S, ∀ i, |(x i : ℝ)-u i| ≤ L)
    (hres : ∀ x ∈ S, ∀ i, (x i : ZMod m)=(b i : ZMod m)) :
    ((S.image (fun x i => x (β i))).card : ℝ) ≤ (4*L/(m : ℝ)+3)^d := by
  classical
  apply ResidueBoxCount.card_le_of_constant_residue m _ (fun i => u (β i)) L hL
  · intro y hy i
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact hbox x hx (β i)
  · intro y hy z hz i
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    exact (hres x hx (β i)).trans (hres w hw (β i)).symm

/-- Points on the exact zero system are counted without a divisor estimate. -/
theorem card_zero_system_le {n d : ℕ} (β : Fin d ↪ Fin n)
    (P : Fin n → Polynomial (MvPolynomial (Fin d) ℤ))
    (k : Fin n → ℕ) (D : ℕ) (C : ℤ) (hD : 1 ≤ D) (hC : C ≠ 0)
    (hdeg : ∀ i, i ∉ Set.range β → (P i).natDegree ≤ D)
    (hcoeff : ∀ i, i ∉ Set.range β → (P i).coeff (k i)=MvPolynomial.C C)
    (S : Finset (Fin n → ℤ)) (m : ℕ) [NeZero m]
    (b : Fin n → ℤ) (u : Fin n → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hbox : ∀ x ∈ S, ∀ i, |(x i : ℝ)-u i| ≤ L)
    (hres : ∀ x ∈ S, ∀ i, (x i : ZMod m)=(b i : ZMod m))
    (hzero : ∀ x ∈ S, ∀ i, MvPolynomial.eval x (relation β P i)=0) :
    (S.card : ℝ) ≤ (D : ℝ)^n*(4*L/(m : ℝ)+3)^d := by
  classical
  have hcard := card_le_image_card_mul S (fun x i => x (β i)) ((D : ℝ)^n) (by
    intro y hy
    obtain ⟨z,hz,hzy⟩ := Finset.mem_image.mp hy
    have he := card_fixed_base_zeros_le β P k D C hD hC hdeg hcoeff
      (S.filter (fun x => (fun i => x (β i))=y)) z
      (fun x hx i => congrFun ((Finset.mem_filter.mp hx).2.trans hzy.symm) i)
      (fun x hx => hzero x (Finset.mem_filter.mp hx).1)
    exact_mod_cast he)
  exact hcard.trans (by
    have he := mul_le_mul_of_nonneg_right (base_card_le β S m b u L hL hbox hres)
      (pow_nonneg (Nat.cast_nonneg D) n)
    simpa only [mul_comm] using he)

/-- The normalized admissible-point sieve, including points on the exact
zero system. Constants precede every center, radius, progression and modulus
interval. The two subpower factors are left separate for source rescaling. -/
theorem exists_bound {n d : ℕ} (β : Fin d ↪ Fin n)
    (P : Fin n → Polynomial (MvPolynomial (Fin d) ℤ))
    (k : Fin n → ℕ) (D : ℕ) (C : ℤ) (hD : 1 ≤ D) (hC : C ≠ 0)
    (hdeg : ∀ i, i ∉ Set.range β → (P i).natDegree ≤ D)
    (hcoeff : ∀ i, i ∉ Set.range β → (P i).coeff (k i)=MvPolynomial.C C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (u : Fin n → ℝ) (L : ℝ), 1 ≤ L →
      ∀ (m : ℕ) [NeZero m] (b : Fin n → ℤ) (S0 : ℝ), 1+L/(m : ℝ) ≤ S0 →
      ∀ S : Finset (Fin n → ℤ),
      (∀ x ∈ S, ∀ i, |(x i : ℝ)-u i| ≤ L) →
      (∀ x ∈ S, ∀ i, (x i : ZMod m)=(b i : ZMod m)) →
      (∀ x ∈ S, ∃ q : ℕ, Squarefree q ∧ q.Coprime m ∧
        S0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ 2*S0 ∧
        ∀ i, (q : ℤ) ∣ MvPolynomial.eval x (relation β P i)) →
      (S.card : ℝ) ≤ K*(L+‖u‖)^ε*(2*S0)^ε*(4*L/(m : ℝ)+3)^(d+1) := by
  classical
  choose K hK hbound using fun j => exists_fixed_index_bound β P k D C hD hC
    hdeg hcoeff j ε hε
  have hK0 (j : Fin n) : 0 ≤ K j := zero_le_one.trans (hK j)
  have hsum : 0 ≤ ∑ j, K j := Finset.sum_nonneg fun j _ => hK0 j
  have hDn : 1 ≤ (D : ℝ)^n := one_le_pow₀ (by exact_mod_cast hD)
  refine ⟨(D : ℝ)^n+∑ j, K j,by linarith,?_⟩
  intro u L hL m hm b S0 hS0 S hbox hres hadm
  let Z := S.filter (fun x => ∀ i, MvPolynomial.eval x (relation β P i)=0)
  let T (j : Fin n) := S.filter (fun x => MvPolynomial.eval x (relation β P j)≠0)
  let M : ℝ := (L+‖u‖)^ε*(2*S0)^ε*(4*L/(m : ℝ)+3)^(d+1)
  have hS01 := parameter_one_le m L S0 hL hS0
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast NeZero.pos m
  have hratio : 0 ≤ 4*L/(m : ℝ) := div_nonneg (by linarith) hm0.le
  have hB1 : 1 ≤ 4*L/(m : ℝ)+3 := by linarith
  have hscale1 : 1 ≤ (L+‖u‖)^ε*(2*S0)^ε :=
    one_le_mul_of_one_le_of_one_le
      (Real.one_le_rpow (by linarith [norm_nonneg u]) hε.le)
      (Real.one_le_rpow (by linarith) hε.le)
  have hB : (4*L/(m : ℝ)+3)^d ≤ M := by
    exact (pow_le_pow_right₀ hB1 (Nat.le_succ d)).trans
      (le_mul_of_one_le_left (pow_nonneg (zero_le_one.trans hB1) _) hscale1)
  have hZ : (Z.card : ℝ) ≤ (D : ℝ)^n*M := by
    apply (card_zero_system_le β P k D C hD hC hdeg hcoeff Z m b u L
      (zero_le_one.trans hL) (fun x hx => hbox x (Finset.mem_filter.mp hx).1)
      (fun x hx => hres x (Finset.mem_filter.mp hx).1)
      (fun x hx => (Finset.mem_filter.mp hx).2)).trans
    exact mul_le_mul_of_nonneg_left hB (pow_nonneg (Nat.cast_nonneg D) _)
  have hT (j : Fin n) : ((T j).card : ℝ) ≤ K j*M := by
    have he := hbound j u L hL m b S0 hS0 (T j)
      (fun x hx => (Finset.mem_filter.mp hx).2)
      (fun x hx => hbox x (Finset.mem_filter.mp hx).1)
      (fun x hx => hres x (Finset.mem_filter.mp hx).1)
      (fun x hx => hadm x (Finset.mem_filter.mp hx).1)
    simpa only [M,mul_assoc] using he
  have hcover : S ⊆ Z ∪ Finset.univ.biUnion T := by
    intro x hx
    by_cases hz : ∀ i, MvPolynomial.eval x (relation β P i)=0
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx,hz⟩)
    · push_neg at hz
      obtain ⟨j,hj⟩ := hz
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨j,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hx,hj⟩⟩)
  have hcard : S.card ≤ Z.card+∑ j, (T j).card :=
    (Finset.card_le_card hcover).trans ((Finset.card_union_le (s := Z) (t := Finset.univ.biUnion T)).trans
      (Nat.add_le_add_left Finset.card_biUnion_le _))
  calc
    (S.card : ℝ) ≤ (Z.card : ℝ)+∑ j, ((T j).card : ℝ) := by exact_mod_cast hcard
    _ ≤ (D : ℝ)^n*M+∑ j, K j*M := add_le_add hZ (Finset.sum_le_sum fun j _ => hT j)
    _ = ((D : ℝ)^n+∑ j, K j)*(L+‖u‖)^ε*(2*S0)^ε*(4*L/(m : ℝ)+3)^(d+1) := by
      rw [← Finset.sum_mul,← add_mul]
      simp only [M,mul_assoc]

end CubicTenVariables.NormalizedGeometricSieve
