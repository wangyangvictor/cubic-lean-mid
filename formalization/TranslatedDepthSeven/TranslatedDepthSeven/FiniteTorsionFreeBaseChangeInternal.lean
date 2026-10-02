import TranslatedDepthSeven.GradedRankSandwich
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# Finite torsion-free modules under flat domain extension

Clear the finitely many denominators in a basis of the generic fibre to
embed a finite torsion-free module in a finite free module. A flat domain
extension preserves this injection, so the extended module remains
torsion-free. Consequently every minimal prime of the extended algebra
contracts to zero in the normalizing polynomial algebra.

These are ordinary module and ideal statements. They do not assume
equidimensionality, a component catalogue, or any Hilbert certificate.
-/

namespace TranslatedDepthSeven

noncomputable section
open scoped TensorProduct nonZeroDivisors
set_option maxHeartbeats 2000000

/-- One denominator clears a finite torsion-free module into a free
module, yielding a literal injective linear map. -/
theorem exists_injective_linearMap_to_finiteFree_of_finite_torsionFree
    (R M : Type*) [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [NoZeroSMulDivisors R M] :
    ∃ n : ℕ, ∃ f : M →ₗ[R] (Fin n → R), Function.Injective f := by
  classical
  obtain ⟨N, t, ht⟩ := Module.Finite.exists_fin (R := R) (M := M)
  obtain ⟨e, _, hli, _, _, d, hd, hclear⟩ :=
    exists_genericRank_subfamily_lattice_sandwich t ht
  let n := Module.finrank (FractionRing R) (LocalizedModule R⁰ M)
  let x : Fin n → M := fun i ↦ t (e i)
  let S := Submodule.span R (Set.range x)
  let g : M →ₗ[R] S :=
    { toFun := fun a ↦ ⟨d • a, hclear a⟩
      map_add' := by intro a b; apply Subtype.ext; exact smul_add d a b
      map_smul' := by intro a b; apply Subtype.ext; exact smul_comm d a b }
  let f : M →ₗ[R] (Fin n → R) :=
    (Finsupp.linearEquivFunOnFinite R R (Fin n)).toLinearMap.comp (hli.repr.comp g)
  refine ⟨n, f, ?_⟩
  intro a b hab
  have hrepr : hli.repr (g a) = hli.repr (g b) :=
    (Finsupp.linearEquivFunOnFinite R R (Fin n)).injective hab
  have hg : g a = g b := (LinearMap.ker_eq_bot.mp hli.repr_ker) hrepr
  exact smul_right_injective M hd (congrArg Subtype.val hg)

/-- Flat scalar extension to another domain preserves torsion-freeness
for finite modules. -/
theorem noZeroSMulDivisors_baseChange_of_finite_torsionFree
    (R S M : Type*) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] [Module.Flat R S]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [NoZeroSMulDivisors R M] :
    NoZeroSMulDivisors S (S ⊗[R] M) := by
  obtain ⟨n, f, hf⟩ := exists_injective_linearMap_to_finiteFree_of_finite_torsionFree R M
  have hbase : Function.Injective (f.baseChange S) :=
    Module.Flat.lTensor_preserves_injective_linearMap f hf
  exact Function.Injective.noZeroSMulDivisors (f.baseChange S) hbase
    (map_zero _) (fun a x ↦ (f.baseChange S).map_smul a x)

/-- Minimal primes of a torsion-free algebra avoid every nonzero element
of the base domain. Thus the base injects into each reduced component. -/
theorem algebraMap_quotient_injective_of_torsionFree_minimalPrime
    (R A : Type*) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
    [NoZeroSMulDivisors R A]
    (P : Ideal A) (hP : P ∈ minimalPrimes A) :
    Function.Injective (algebraMap R (A ⧸ P)) := by
  apply (injective_iff_map_eq_zero (algebraMap R (A ⧸ P))).mpr
  intro r hr
  by_contra hrne
  have hrP : algebraMap R A r ∈ P := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact hr
  obtain ⟨a, ha, hra⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hP hrP
  have hane : a ≠ 0 := by simpa only [Ideal.mem_bot] using ha
  have hzero : r • a = 0 := by
    simpa only [Algebra.smul_def, Ideal.mem_bot] using hra
  exact hane ((smul_eq_zero.mp hzero).resolve_left hrne)

end
end TranslatedDepthSeven
