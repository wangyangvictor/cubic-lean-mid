import CubicTenVariables.ResidueBoxCount
import CubicTenVariables.CRTCharacters
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Squarefree

/-! Literal univariate roots modulo a squarefree integer, including primes
dividing a specified coefficient. No geometry or literature input is used. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.SquarefreePolynomialRoots
open Polynomial CRTCharacters
open scoped BigOperators

def rootCount (P : Polynomial ℤ) (q : ℕ) : ℕ :=
  Nat.card {x : ZMod q // P.eval₂ (Int.castRingHom (ZMod q)) x=0}

theorem rootCount_eq_card (P : Polynomial ℤ) (q : ℕ) [NeZero q] :
    rootCount P q = (Finset.univ.filter fun x : ZMod q =>
      P.eval₂ (Int.castRingHom (ZMod q)) x=0).card := by
  classical
  simp only [rootCount,Nat.card_eq_fintype_card,Fintype.card_subtype]

@[simp] theorem rootCount_one (P : Polynomial ℤ) : rootCount P 1=1 := by
  have hz (x : ZMod 1) : P.eval₂ (Int.castRingHom (ZMod 1)) x=0 := Subsingleton.elim _ _
  simp [rootCount,hz]

theorem map_eval₂_int {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (P : Polynomial ℤ) (x : R) :
    f (P.eval₂ (Int.castRingHom R) x)=P.eval₂ (Int.castRingHom S) (f x) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [eval₂_add,map_add,hP,hQ]
  | monomial k a => simp

theorem root_crt_iff (P : Polynomial ℤ) {a b : ℕ} (hab : a.Coprime b)
    (x : ZMod (a*b)) :
    P.eval₂ (Int.castRingHom (ZMod (a*b))) x=0 ↔
      P.eval₂ (Int.castRingHom (ZMod a)) (leftProjection hab x)=0 ∧
      P.eval₂ (Int.castRingHom (ZMod b)) (rightProjection hab x)=0 := by
  constructor
  · intro hx
    constructor
    · simpa only [map_eval₂_int,map_zero] using congrArg (leftProjection hab) hx
    · simpa only [map_eval₂_int,map_zero] using congrArg (rightProjection hab) hx
  · rintro ⟨ha,hb⟩
    apply (ZMod.chineseRemainder hab).injective
    apply Prod.ext
    · change leftProjection hab _=leftProjection hab 0
      simpa only [map_eval₂_int,map_zero] using ha
    · change rightProjection hab _=rightProjection hab 0
      simpa only [map_eval₂_int,map_zero] using hb

def rootCrtEquiv (P : Polynomial ℤ) {a b : ℕ} (hab : a.Coprime b) :
    {x : ZMod (a*b) // P.eval₂ (Int.castRingHom (ZMod (a*b))) x=0} ≃
      ({x : ZMod a // P.eval₂ (Int.castRingHom (ZMod a)) x=0} ×
       {x : ZMod b // P.eval₂ (Int.castRingHom (ZMod b)) x=0}) :=
  (Equiv.subtypeEquiv (ZMod.chineseRemainder hab).toEquiv
    (root_crt_iff P hab)).trans Equiv.subtypeProdEquivProd

theorem rootCount_mul (P : Polynomial ℤ) {a b : ℕ} (hab : a.Coprime b) :
    rootCount P (a*b)=rootCount P a*rootCount P b := by
  rw [rootCount,Nat.card_congr (rootCrtEquiv P hab),Nat.card_prod]
  rfl

theorem squarefree_product (f : ℕ → ℕ)
    (hmul : ∀a b,a.Coprime b → f (a*b)=f a*f b) (hone : f 1=1)
    (q : ℕ) (hq : Squarefree q) : f q=∏p∈q.primeFactors,f p := by
  have h := Nat.multiplicative_factorization f hmul hone hq.ne_zero
  rw [Nat.prod_factorization_eq_prod_primeFactors] at h
  rw [h]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.factorization_eq_one_of_squarefree hq (Nat.prime_of_mem_primeFactors hp)
    (Nat.dvd_of_mem_primeFactors hp),pow_one]

theorem rootCount_squarefree (P : Polynomial ℤ) (q : ℕ) (hq : Squarefree q) :
    rootCount P q=∏p∈q.primeFactors,rootCount P p :=
  squarefree_product _ (fun _ _ h => rootCount_mul P h) (rootCount_one P) q hq

/-- A nonzero reduction has at most the original degree many roots. -/
theorem rootCount_prime_le_degree (P : Polynomial ℤ) (p : ℕ) [Fact p.Prime]
    (hP : P.map (Int.castRingHom (ZMod p)) ≠ 0) : rootCount P p ≤ P.natDegree := by
  classical
  rw [rootCount_eq_card]
  apply (Polynomial.card_le_degree_of_subset_roots (p := P.map (Int.castRingHom (ZMod p))) ?_).trans
    Polynomial.natDegree_map_le
  intro x hx
  rw [Polynomial.mem_roots hP]
  exact (Polynomial.eval_map _ _).trans (Finset.mem_filter.mp hx).2

theorem rootCount_le_modulus (P : Polynomial ℤ) (q : ℕ) [NeZero q] : rootCount P q≤q := by
  have h := Nat.card_le_card_of_injective
    (fun x : {x : ZMod q // P.eval₂ (Int.castRingHom (ZMod q)) x=0} => x.val)
    Subtype.val_injective
  simpa only [rootCount,Nat.card_eq_fintype_card,ZMod.card] using h

/-- Any specified coefficient works; it need not be the leading one. The
bad-prime factor is the literal gcd, with no excluded primes. D is positive
because the assertion with D=0 fails for a nonzero constant divisible by p. -/
theorem rootCount_prime_le (P : Polynomial ℤ) (D k : ℕ) (C : ℤ)
    (hD : 1≤D) (hdeg : P.natDegree≤D) (hcoeff : P.coeff k=C)
    (p : ℕ) [Fact p.Prime] : rootCount P p≤Nat.gcd C.natAbs p*D := by
  have hp : p.Prime := Fact.out
  by_cases hbad : p∣C.natAbs
  · rw [Nat.gcd_eq_right_iff_dvd.mpr hbad]
    exact (rootCount_le_modulus P p).trans (Nat.le_mul_of_pos_right _ hD)
  · have hmod : P.map (Int.castRingHom (ZMod p))≠0 := by
      intro hzero
      have hc := congrArg (fun R : Polynomial (ZMod p) => R.coeff k) hzero
      simp only [Polynomial.coeff_map,hcoeff,Polynomial.coeff_zero,Int.coe_castRingHom] at hc
      have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd C p).mp hc
      exact hbad (Int.natCast_dvd.mp hd)
    have hg : Nat.gcd C.natAbs p=1 :=
      (hp.coprime_iff_not_dvd.mpr hbad).symm.gcd_eq_one
    rw [hg,one_mul]
    exact (rootCount_prime_le_degree P p hmod).trans hdeg

/-- Uniform coefficient-controlled root count, including modulus one. -/
theorem rootCount_le (P : Polynomial ℤ) (D k : ℕ) (C : ℤ)
    (hD : 1≤D) (hdeg : P.natDegree≤D) (hcoeff : P.coeff k=C)
    (q : ℕ) (hq : Squarefree q) :
    rootCount P q ≤ Nat.gcd C.natAbs q*D^q.primeFactors.card := by
  rw [rootCount_squarefree P q hq]
  have hg : Nat.gcd C.natAbs q=∏p∈q.primeFactors,Nat.gcd C.natAbs p := by
    apply squarefree_product (fun a => Nat.gcd C.natAbs a) _ (by simp) q hq
    intro a b hab
    simpa only [Nat.gcd_comm] using hab.mul_gcd C.natAbs
  calc
    _ ≤ ∏p∈q.primeFactors,(Nat.gcd C.natAbs p*D) := by
      apply Finset.prod_le_prod'
      intro p hp
      letI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
      exact rootCount_prime_le P D k C hD hdeg hcoeff p
    _ = _ := by rw [Finset.prod_mul_distrib,←hg,Finset.prod_const]

theorem rootCount_le_leadingCoeff (P : Polynomial ℤ) (D : ℕ)
    (hD : 1≤D) (hdeg : P.natDegree≤D) (q : ℕ) (hq : Squarefree q) :
    rootCount P q ≤ Nat.gcd P.leadingCoeff.natAbs q*D^q.primeFactors.card :=
  rootCount_le P D P.natDegree P.leadingCoeff hD hdeg (by simp) q hq

/-- A fixed nonzero coefficient gives a bound uniform in all the other
coefficients and in the squarefree modulus. -/
theorem rootCount_le_abs_coeff (P : Polynomial ℤ) (D k : ℕ) (C : ℤ)
    (hC : C≠0) (hD : 1≤D) (hdeg : P.natDegree≤D) (hcoeff : P.coeff k=C)
    (q : ℕ) (hq : Squarefree q) : rootCount P q≤C.natAbs*D^q.primeFactors.card := by
  apply (rootCount_le P D k C hD hdeg hcoeff q hq).trans
  exact Nat.mul_le_mul_right _ (Nat.le_of_dvd (Int.natAbs_pos.mpr hC) (Nat.gcd_dvd_left _ _))

/-- Literal evaluation of an integral argument agrees with integer divisibility. -/
theorem eval₂_intCast_eq_zero_iff (P : Polynomial ℤ) (q : ℕ) (y : ℤ) :
    P.eval₂ (Int.castRingHom (ZMod q)) (y : ZMod q)=0 ↔ (q : ℤ)∣P.eval y := by
  change P.eval₂ (Int.castRingHom (ZMod q)) ((Int.castRingHom (ZMod q)) y)=0 ↔ _
  rw [Polynomial.eval₂_at_apply]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _

/-- The two literal congruences determine a class modulo the coprime product. -/
theorem intCast_eq_of_coprime {q m : ℕ} (hcop : q.Coprime m) (x y : ℤ)
    (hq : (x : ZMod q)=(y : ZMod q)) (hm : (x : ZMod m)=(y : ZMod m)) :
    (x : ZMod (q*m))=(y : ZMod (q*m)) := by
  apply (ZMod.chineseRemainder hcop).injective
  apply Prod.ext
  · change leftProjection hcop _=leftProjection hcop _
    simpa only [map_intCast] using hq
  · change rightProjection hcop _=rightProjection hcop _
    simpa only [map_intCast] using hm

/-- Each simultaneous residue class has at most seven points in the stated
arbitrarily centered interval. The constant is uniform in both classes. -/
theorem card_progression_fiber_le (q m : ℕ) [NeZero q] [NeZero m]
    (hcop : q.Coprime m) (S : Finset ℤ) (b : ℤ) (u L : ℝ)
    (hL : 0≤L) (hsize : L≤(q*m : ℕ))
    (hbox : ∀y∈S,|(y : ℝ)-u|≤L)
    (hres : ∀y∈S,(y : ZMod m)=(b : ZMod m)) (a : ZMod q) :
    (S.filter fun y : ℤ => (y : ZMod q)=a).card≤7 := by
  classical
  let T := S.filter fun y : ℤ => (y : ZMod q)=a
  let e : ℤ → (Fin 1 → ℤ) := fun y _ => y
  have he : Function.Injective e := fun _ _ h => congrFun h 0
  have hcard : (T.image e).card=T.card := Finset.card_image_of_injective T he
  have hb := ResidueBoxCount.card_le_of_constant_residue (q*m) (T.image e)
    (fun _ => u) L hL (by
      intro x hx i
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      exact hbox y (Finset.mem_filter.mp hy).1) (by
      intro x hx y hy i
      obtain ⟨x₀,hx₀,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨y₀,hy₀,rfl⟩ := Finset.mem_image.mp hy
      exact intCast_eq_of_coprime hcop x₀ y₀
        ((Finset.mem_filter.mp hx₀).2.trans (Finset.mem_filter.mp hy₀).2.symm)
        ((hres x₀ (Finset.mem_filter.mp hx₀).1).trans (hres y₀ (Finset.mem_filter.mp hy₀).1).symm))
  rw [hcard,pow_one] at hb
  have hqm : 0<((q*m : ℕ) : ℝ) := by exact_mod_cast NeZero.pos (q*m)
  have hratio : L/((q*m : ℕ) : ℝ)≤1 := (div_le_one hqm).mpr hsize
  have hseven : (T.card : ℝ)≤7 := by
    have heq : 4*L/((q*m : ℕ) : ℝ)=4*(L/((q*m : ℕ) : ℝ)) := by ring
    rw [heq] at hb
    linarith
  exact_mod_cast hseven

/-- Root congruence and a coprime progression are imposed simultaneously.
The family S is arbitrary and finite; no integer or aligned center is needed. -/
theorem card_lifts_le_rootCount (P : Polynomial ℤ) (q m : ℕ)
    [NeZero q] [NeZero m] (hcop : q.Coprime m)
    (S : Finset ℤ) (b : ℤ) (u L : ℝ) (hL : 0≤L)
    (hsize : 1+L/(m : ℝ)≤(q : ℝ))
    (hbox : ∀y∈S,|(y : ℝ)-u|≤L)
    (hres : ∀y∈S,(y : ZMod m)=(b : ZMod m))
    (hroot : ∀y∈S,P.eval₂ (Int.castRingHom (ZMod q)) (y : ZMod q)=0) :
    S.card≤7*rootCount P q := by
  classical
  have hm : 0<(m : ℝ) := by exact_mod_cast NeZero.pos m
  have hlength : L≤((q*m : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    exact (div_le_iff₀ hm).mp (by linarith)
  rw [rootCount_eq_card]
  apply Finset.card_le_mul_card_image_of_maps_to
    (fun y hy => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hroot y hy⟩) 7
  intro a _ha
  exact card_progression_fiber_le q m hcop S b u L hL hlength hbox hres a

/-- The full squarefree progression estimate, with one explicit absolute
constant and the fixed coefficient controlling every bad prime. -/
theorem card_lifts_le (P : Polynomial ℤ) (D k : ℕ) (C : ℤ)
    (hD : 1≤D) (hdeg : P.natDegree≤D) (hcoeff : P.coeff k=C)
    (q m : ℕ) (hq : Squarefree q) [NeZero m] (hcop : q.Coprime m)
    (S : Finset ℤ) (b : ℤ) (u L : ℝ) (hL : 0≤L)
    (hsize : 1+L/(m : ℝ)≤(q : ℝ))
    (hbox : ∀y∈S,|(y : ℝ)-u|≤L)
    (hres : ∀y∈S,(y : ZMod m)=(b : ZMod m))
    (hroot : ∀y∈S,P.eval₂ (Int.castRingHom (ZMod q)) (y : ZMod q)=0) :
    S.card≤7*Nat.gcd C.natAbs q*D^q.primeFactors.card := by
  letI : NeZero q := ⟨hq.ne_zero⟩
  exact (card_lifts_le_rootCount P q m hcop S b u L hL hsize hbox hres hroot).trans
    (by simpa only [Nat.mul_assoc] using
      Nat.mul_le_mul_left 7 (rootCount_le P D k C hD hdeg hcoeff q hq))

/-- The progression constant may depend only on the fixed nonzero
coefficient and positive degree bound, not on the remaining coefficients. -/
theorem card_lifts_le_abs_coeff (P : Polynomial ℤ) (D k : ℕ) (C : ℤ)
    (hC : C≠0) (hD : 1≤D) (hdeg : P.natDegree≤D) (hcoeff : P.coeff k=C)
    (q m : ℕ) (hq : Squarefree q) [NeZero m] (hcop : q.Coprime m)
    (S : Finset ℤ) (b : ℤ) (u L : ℝ) (hL : 0≤L)
    (hsize : 1+L/(m : ℝ)≤(q : ℝ))
    (hbox : ∀y∈S,|(y : ℝ)-u|≤L)
    (hres : ∀y∈S,(y : ZMod m)=(b : ZMod m))
    (hroot : ∀y∈S,P.eval₂ (Int.castRingHom (ZMod q)) (y : ZMod q)=0) :
    S.card≤7*C.natAbs*D^q.primeFactors.card := by
  apply (card_lifts_le P D k C hD hdeg hcoeff q m hq hcop S b u L hL hsize
    hbox hres hroot).trans
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 7
    (Nat.le_of_dvd (Int.natAbs_pos.mpr hC) (Nat.gcd_dvd_left _ _)))

end CubicTenVariables.SquarefreePolynomialRoots
