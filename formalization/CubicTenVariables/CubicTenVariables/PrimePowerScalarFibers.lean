import CubicTenVariables.PrimePowerKernelProfile
import CubicTenVariables.SmoothResidueIteration
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Scalar congruence fibers at one additional prime digit

An old pivot is an integer not divisible by p^m. At modulus p^(m+1),
every right-hand side divisible by p^m has exactly the old pivot's kernel
size many preimages, and all these preimages reduce to zero modulo p.
These facts require no odd-prime assumption.
-/

noncomputable section
namespace CubicTenVariables.PrimePowerScalarFibers
open PrimePowerKernelProfile

/-- Below the current precision an old pivot has its actual valuation. -/
theorem valuation_lt (p m : ℕ) (hp : p.Prime) (a : ℤ)
    (ha : ¬ (p : ℤ)^m ∣ a) : a ≠ 0 ∧ a.natAbs.factorization p < m := by
  have ha0 : a ≠ 0 := fun h => ha (h ▸ dvd_zero _)
  refine ⟨ha0, Nat.lt_of_not_ge ?_⟩
  intro hle
  have hd := (hp.pow_dvd_iff_le_factorization (Int.natAbs_ne_zero.mpr ha0)).mpr hle
  apply ha
  simpa only [Nat.cast_pow] using (Int.natCast_dvd.mpr hd)

theorem truncatedValuation_succ (p m : ℕ) (hp : p.Prime) (a : ℤ)
    (ha : ¬ (p : ℤ)^m ∣ a) :
    truncatedValuation p (m+1) a = truncatedValuation p m a := by
  obtain ⟨ha0,hv⟩ := valuation_lt p m hp a ha
  simp only [truncatedValuation, if_neg ha0,
    Nat.min_eq_left (show a.natAbs.factorization p ≤ m+1 by omega),
    Nat.min_eq_left (Nat.le_of_lt hv)]

/-- Bézout gives an actual scalar solution for every multiple of the gcd. -/
theorem exists_scalar_eq_of_gcd_dvd (q k : ℕ) (a : ℤ)
    (h : Nat.gcd a.natAbs q ∣ k) (b : ZMod q) :
    ∃ x : ZMod q, (a : ZMod q)*x = (k : ZMod q)*b := by
  have hg : Int.gcd a (q : ℤ) ∣ k := by simpa only [Int.gcd_def, Int.natAbs_natCast] using h
  obtain ⟨u,v,huv⟩ := Int.gcd_dvd_iff.mp hg
  have hz : (k : ZMod q) = (a : ZMod q)*(u : ZMod q) := by
    have hh := congrArg (fun z : ℤ => (z : ZMod q)) huv
    simpa only [Int.cast_natCast, Int.cast_add, Int.cast_mul, ZMod.natCast_self,
      zero_mul, add_zero] using hh
  exact ⟨(u : ZMod q)*b, by rw [← mul_assoc, ← hz]⟩

theorem exists_scalar_eq (p m : ℕ) (hp : p.Prime) (a : ℤ)
    (ha : ¬ (p : ℤ)^m ∣ a) (b : ZMod (p^(m+1))) :
    ∃ x : ZMod (p^(m+1)), (a : ZMod (p^(m+1)))*x =
      (p : ZMod (p^(m+1)))^m*b := by
  have hg : Nat.gcd a.natAbs (p^(m+1)) ∣ p^m := by
    rw [gcd_primePower p (m+1) hp a, truncatedValuation_succ p m hp a ha]
    exact pow_dvd_pow p (truncatedValuation_le p m a)
  simpa only [Nat.cast_pow] using exists_scalar_eq_of_gcd_dvd (p^(m+1)) (p^m) a hg b

/-- Every affine scalar fiber at this precision has the same exact size. -/
theorem card_scalar_fiber (p m : ℕ) (hp : p.Prime) (a : ℤ)
    (ha : ¬ (p : ℤ)^m ∣ a) (b : ZMod (p^(m+1))) :
    Nat.card {x : ZMod (p^(m+1)) // (a : ZMod (p^(m+1)))*x =
      (p : ZMod (p^(m+1)))^m*b} = p^(truncatedValuation p m a) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let f : ZMod (p^(m+1)) →+ ZMod (p^(m+1)) :=
    { toFun := fun x => (a : ZMod (p^(m+1)))*x
      map_zero' := mul_zero _
      map_add' := fun x y => mul_add _ x y }
  obtain ⟨x,hx⟩ := exists_scalar_eq p m hp a ha b
  have he : Nat.card {z : ZMod (p^(m+1)) // f z =
        (p : ZMod (p^(m+1)))^m*b} = Nat.card f.ker := by
    change Nat.card (f ⁻¹' {(p : ZMod (p^(m+1)))^m*b}) = _
    rw [← hx]
    exact Nat.card_congr (f.fiberEquivKer x)
  change Nat.card {z : ZMod (p^(m+1)) // (a : ZMod (p^(m+1)))*z =
    (p : ZMod (p^(m+1)))^m*b} =
    Nat.card {z : ZMod (p^(m+1)) // (a : ZMod (p^(m+1)))*z = 0} at he
  rw [he, ModularKernelCardinality.card_scalar_kernel_int,
    gcd_primePower p (m+1) hp a, truncatedValuation_succ p m hp a ha]

/-- An old pivot annihilates a product at precision m only if the other
factor is divisible by p. -/
theorem prime_dvd_of_pow_dvd_mul (p m : ℕ) (hp : p.Prime) (a x : ℤ)
    (ha : ¬ (p : ℤ)^m ∣ a) (hx : (p : ℤ)^m ∣ a*x) : (p : ℤ) ∣ x := by
  by_contra hnot
  have hc : IsCoprime (p : ℤ) x :=
    (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr hnot
  exact ha (hc.pow_left.dvd_of_dvd_mul_right hx)

/-- Every solution in an old-pivot fiber has zero prime reduction. -/
theorem reduction_eq_zero_of_scalar_eq (p m : ℕ) (hp : p.Prime) (a : ℤ)
    (ha : ¬ (p : ℤ)^m ∣ a) (x b : ZMod (p^(m+1)))
    (hx : (a : ZMod (p^(m+1)))*x = (p : ZMod (p^(m+1)))^m*b) :
    SmoothResidueIteration.toPrime p (m+1) (by omega) x = 0 := by
  obtain ⟨z,rfl⟩ := ZMod.intCast_surjective x
  have hreduce := congrArg (PrimePowerFibers.reduction p (Nat.le_succ m)) hx
  have hz : ((a*z : ℤ) : ZMod (p^m)) = 0 := by
    simpa only [map_mul, map_intCast, map_pow, map_natCast, ← Nat.cast_pow,
      ZMod.natCast_self, zero_mul, Int.cast_mul] using hreduce
  have hd : (p : ℤ)^m ∣ a*z := by
    simpa only [Nat.cast_pow] using (ZMod.intCast_zmod_eq_zero_iff_dvd (a*z) (p^m)).mp hz
  have hpz := prime_dvd_of_pow_dvd_mul p m hp a z ha hd
  simpa only [map_intCast] using (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mpr hpz

end CubicTenVariables.PrimePowerScalarFibers
