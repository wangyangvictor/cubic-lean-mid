import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.CharP.Basic
import Mathlib.Tactic

/-! Denominator clearing for equations in a rational polynomial ideal.
One fixed nonzero integer gives containment of the actual reduced zero
sets over every field in every permitted characteristic. There is no
geometric or point-counting premise. The polynomial family generating the
ideal need not even be finite; the ideal-membership proof provides the
finite algebraic certificate automatically. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.DegreeSpanReduction
open MvPolynomial
open scoped BigOperators Classical

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Membership after rational coefficient extension has an actual integral
certificate after multiplication by one nonzero integer. -/
theorem exists_integral_certificate {σ ι : Type*}
    (G : ι → MvPolynomial σ ℤ) (H : MvPolynomial σ ℤ)
    (hH : map (Int.castRingHom ℚ) H ∈
      Ideal.span (Set.range (fun i => map (Int.castRingHom ℚ) (G i)))) :
    ∃ d : ℤ, d ≠ 0 ∧ C d * H ∈ Ideal.span (Set.range G) := by
  have hm : algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℚ) H ∈
      (Ideal.span (Set.range G)).map
        (algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℚ)) := by
    simpa only [MvPolynomial.algebraMap_def, Ideal.map_span, ← Set.range_comp'] using hH
  obtain ⟨s,hs,hmem⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff
      ((nonZeroDivisors ℤ).map (C (σ := σ))) (MvPolynomial σ ℚ)
      (Ideal.span (Set.range G)) H).mp hm
  obtain ⟨d,hd,rfl⟩ := Submonoid.mem_map.mp hs
  exact ⟨d,nonZeroDivisors.ne_zero hd,hmem⟩

/-- Evaluate the literal integral certificate at a common zero. The only
coefficient condition is that the clearing integer stays nonzero. -/
theorem eval_zero_of_certificate {σ ι K : Type*} [Field K]
    (G : ι → MvPolynomial σ ℤ) (H : MvPolynomial σ ℤ) (d : ℤ)
    (hcert : C d * H ∈ Ideal.span (Set.range G)) (hd : (d : K) ≠ 0)
    (x : σ → K) (hx : ∀ i, eval x (map (Int.castRingHom K) (G i)) = 0) :
    eval x (map (Int.castRingHom K) H) = 0 := by
  have hker : Ideal.span (Set.range G) ≤ RingHom.ker (eval₂Hom (Int.castRingHom K) x) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change eval₂ (Int.castRingHom K) x (G i) = 0
    simpa only [eval₂_eq_eval_map] using hx i
  have he := hker hcert
  change eval₂ (Int.castRingHom K) x (C d * H) = 0 at he
  rw [eval₂_mul, eval₂_C, eval₂_eq_eval_map] at he
  exact (mul_eq_zero.mp he).resolve_left hd

/-- One exceptional positive integer is chosen before the characteristic,
the field, and the point. In particular the conclusion is uniform over
all finite extensions, without any finite-field assumption. -/
theorem exists_uniform_reduction {σ ι : Type*}
    (G : ι → MvPolynomial σ ℤ) (H : MvPolynomial σ ℤ)
    (hH : map (Int.castRingHom ℚ) H ∈
      Ideal.span (Set.range (fun i => map (Int.castRingHom ℚ) (G i)))) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ p : ℕ, ¬ p ∣ D →
      ∀ (K : Type*) [Field K] [CharP K p] (x : σ → K),
        (∀ i, eval x (map (Int.castRingHom K) (G i)) = 0) →
        eval x (map (Int.castRingHom K) H) = 0 := by
  obtain ⟨d,hd,hcert⟩ := exists_integral_certificate G H hH
  refine ⟨d.natAbs, Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hd), ?_⟩
  intro p hp K _ _ x hx
  apply eval_zero_of_certificate G H d hcert _ x hx
  intro hz
  have hdiv := (CharP.intCast_eq_zero_iff K p d).mp hz
  exact hp (by simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hdiv)

/-- A finite family of rational-ideal consequences has a common fixed
prime exclusion. The conclusion concerns the actual reduced equations. -/
theorem exists_uniform_family_reduction {σ ι κ : Type*} [Fintype κ]
    (G : ι → MvPolynomial σ ℤ) (H : κ → MvPolynomial σ ℤ)
    (hH : ∀ j, map (Int.castRingHom ℚ) (H j) ∈
      Ideal.span (Set.range (fun i => map (Int.castRingHom ℚ) (G i)))) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ p : ℕ, ¬ p ∣ D →
      ∀ (K : Type*) [Field K] [CharP K p] (x : σ → K),
        (∀ i, eval x (map (Int.castRingHom K) (G i)) = 0) →
        ∀ j, eval x (map (Int.castRingHom K) (H j)) = 0 := by
  choose D hD hgood using fun j => exists_uniform_reduction G (H j) (hH j)
  refine ⟨∏ j, D j, Finset.one_le_prod' (fun j _ => hD j), ?_⟩
  intro p hp K _ _ x hx j
  apply hgood j p _ K x hx
  intro hj
  apply hp
  exact hj.trans (Finset.dvd_prod_of_mem D (Finset.mem_univ j))

end CubicTenVariables.DegreeSpanReduction
