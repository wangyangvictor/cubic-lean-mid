import TranslatedDepthSeven.SmoothPointKrullIntersectionPrimeInternal
import TranslatedDepthSeven.AugmentedJetLocalization
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# The local ring at a standard-smooth rational point is a domain

Artin--Rees identifies the localization kernel with the intersection of
the powers of the point ideal.  Polynomial jets show that this intersection
is prime.  Thus the assertion does not depend on a regular-local-ring or
formal-completion theorem.
-/

namespace TranslatedDepthSeven

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

theorem pointLocalization_ker_eq_iInf_pow
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    [IsNoetherianRing A]
    (f : A →ₐ[K] K) (M : Ideal A) [M.IsPrime]
    (hM : M = RingHom.ker f.toRingHom) :
    RingHom.ker (algebraMap A (Localization.AtPrime M)) = ⨅ n : ℕ, M ^ n := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff M.primeCompl
      (Localization.AtPrime M) x).mp hx
    rw [Submodule.mem_iInf]
    intro n
    cases n with
    | zero => simp
    | succ k =>
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      have hfs : f s ≠ 0 := by
        intro hz
        exact s.property (by simpa [hM, RingHom.mem_ker] using hz)
      have hu : IsUnit (Ideal.Quotient.mk (M ^ (k + 1)) (s : A)) := by
        subst M
        exact isUnit_mk_augmentedJet_of_ne_zero f k s hfs
      apply hu.mul_left_cancel
      simpa only [mul_zero, ← map_mul, hs, map_zero]
  · intro hx
    have hx' : x ∈ (⨅ n : ℕ, M ^ n • ⊤ : Submodule A A) := by
      simpa only [smul_eq_mul, ← Ideal.one_eq_top, mul_one] using hx
    obtain ⟨a, ha⟩ := (M.mem_iInf_smul_pow_eq_bot_iff x).mp hx'
    have hs : 1 - (a : A) ∉ M := by
      intro hs
      have hone : (1 : A) ∈ M := by simpa using M.add_mem hs a.property
      exact M.one_notMem hone
    apply (IsLocalization.map_eq_zero_iff M.primeCompl
      (Localization.AtPrime M) x).mpr
    refine ⟨⟨1 - a, hs⟩, ?_⟩
    simpa only [sub_mul, one_mul, smul_eq_mul, sub_eq_zero] using ha.symm

theorem isDomain_pointLocalization_of_standardSmooth
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    [IsNoetherianRing A]
    (f : A →ₐ[K] K) (r : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A]
    (M : Ideal A) [M.IsPrime] (hM : M = RingHom.ker f.toRingHom) :
    IsDomain (Localization.AtPrime M) := by
  have hker : (RingHom.ker (algebraMap A (Localization.AtPrime M))).IsPrime := by
    rw [pointLocalization_ker_eq_iInf_pow f M hM, hM]
    exact iInf_pointIdeal_pow_isPrime_of_standardSmooth f r
  letI : (⊥ : Ideal (Localization.AtPrime M)).IsPrime := by
    apply (IsLocalization.isPrime_iff_isPrime_disjoint M.primeCompl
      (Localization.AtPrime M) ⊥).mpr
    refine ⟨hker, ?_⟩
    apply Set.disjoint_left.mpr
    intro a ha hzero
    have hle : RingHom.ker (algebraMap A (Localization.AtPrime M)) ≤ M := by
      rw [pointLocalization_ker_eq_iInf_pow f M hM]
      simpa only [pow_one] using (iInf_le (fun n : ℕ ↦ M ^ n) 1)
    exact ha (hle hzero)
  exact IsDomain.of_bot_isPrime _

end

end TranslatedDepthSeven
