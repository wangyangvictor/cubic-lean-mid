import TranslatedDepthSeven.PolynomialOriginOrderInternal
import TranslatedDepthSeven.StandardSmoothHigherJets

/-!
# The separated local component at a smooth rational point

The intersection of all powers of a smooth rational point ideal is prime.
This follows from the explicitly checked polynomial-jet isomorphisms and
additivity of order at the polynomial origin.  No regular-local-ring or
completion theorem is assumed.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

theorem mul_mem_iInf_pointIdeal_pow_of_standardSmooth
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (f : A →ₐ[K] K) (r : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A]
    (x y : A)
    (hxy : x * y ∈ ⨅ n : ℕ, RingHom.ker f.toRingHom ^ n) :
    x ∈ (⨅ n : ℕ, RingHom.ker f.toRingHom ^ n) ∨
      y ∈ (⨅ n : ℕ, RingHom.ker f.toRingHom ^ n) := by
  classical
  let M := RingHom.ker f.toRingHom
  let O := RingHom.ker (constantCoeff : MvPolynomial (Fin r) K →+* K)
  let u := smoothCoordinateMap f r
  by_contra hnot
  obtain ⟨hx, hy⟩ := not_or.mp hnot
  obtain ⟨a, ha⟩ : ∃ a : ℕ, x ∉ M ^ a := by
    simpa only [Submodule.mem_iInf, not_forall] using hx
  obtain ⟨b, hb⟩ : ∃ b : ℕ, y ∉ M ^ b := by
    simpa only [Submodule.mem_iInf, not_forall] using hy
  let k := a + b + 1
  have hk : 1 ≤ k := by omega
  let Jmap := smoothCoordinateJetMap f r k
  have hbij : Function.Bijective Jmap := smoothCoordinateJetMap_bijective f r k hk
  obtain ⟨pbar, hpbar⟩ := hbij.2 (Ideal.Quotient.mk (M ^ (k + 1)) x)
  obtain ⟨qbar, hqbar⟩ := hbij.2 (Ideal.Quotient.mk (M ^ (k + 1)) y)
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective pbar
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective qbar
  have hp : Ideal.Quotient.mk (M ^ (k + 1)) (u p) =
      Ideal.Quotient.mk (M ^ (k + 1)) x := hpbar
  have hq : Ideal.Quotient.mk (M ^ (k + 1)) (u q) =
      Ideal.Quotient.mk (M ^ (k + 1)) y := hqbar
  have hbase : O ≤ M.comap u := by
    intro z hz
    change f (u z) = 0
    change f (smoothCoordinateMap f r z) = 0
    rw [← AlgHom.comp_apply, comp_smoothCoordinateMap_eq_polynomialOriginAugmentation]
    exact hz
  have hmap (n : ℕ) : O ^ n ≤ (M ^ n).comap u :=
    (Ideal.pow_right_mono hbase n).trans (Ideal.le_comap_pow u n)
  have hpa : p ∉ O ^ a := by
    intro hpa
    apply ha
    have hdifference : u p - x ∈ M ^ a :=
      Ideal.pow_le_pow_right (show a ≤ k + 1 by omega) (Ideal.Quotient.eq.mp hp)
    simpa using (M ^ a).sub_mem (hmap a hpa) hdifference
  have hqb : q ∉ O ^ b := by
    intro hqb
    apply hb
    have hdifference : u q - y ∈ M ^ b :=
      Ideal.pow_le_pow_right (show b ≤ k + 1 by omega) (Ideal.Quotient.eq.mp hq)
    simpa using (M ^ b).sub_mem (hmap b hqb) hdifference
  have hproduct : p * q ∈ O ^ (k + 1) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply hbij.1
    rw [map_zero]
    change Ideal.Quotient.mk (M ^ (k + 1)) (u (p * q)) = 0
    rw [map_mul, map_mul, hp, hq, ← map_mul]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact (iInf_le (fun n : ℕ ↦ RingHom.ker f.toRingHom ^ n) (k + 1)) hxy
  exact mul_notMem_originIdeal_pow_add p q a b hpa hqb
    (Ideal.pow_le_pow_right (show a + b ≤ k + 1 by omega) hproduct)

theorem iInf_pointIdeal_pow_isPrime_of_standardSmooth
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (f : A →ₐ[K] K) (r : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A] :
    (⨅ n : ℕ, RingHom.ker f.toRingHom ^ n).IsPrime := by
  refine ⟨?_, fun {x y} hxy ↦ mul_mem_iInf_pointIdeal_pow_of_standardSmooth f r x y hxy⟩
  intro htop
  have hle : (⨅ n : ℕ, RingHom.ker f.toRingHom ^ n) ≤ RingHom.ker f.toRingHom := by
    simpa using (iInf_le (fun n : ℕ ↦ RingHom.ker f.toRingHom ^ n) 1)
  have hone : (1 : A) ∈ RingHom.ker f.toRingHom := hle (by rw [htop]; trivial)
  exact one_ne_zero (by simpa only [RingHom.mem_ker, map_one] using hone)

end

end TranslatedDepthSeven
