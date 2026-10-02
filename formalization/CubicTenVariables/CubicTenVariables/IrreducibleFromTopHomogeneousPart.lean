import CubicTenVariables.HomogeneousSpanCertificates
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-!
# Irreducibility from the highest homogeneous component

The component of degree `deg(f) + deg(g)` in `f*g` is the product of the
highest components. Over a field, if the highest component of a polynomial
is irreducible, every factorization has a factor of degree zero, hence a
unit. This module concerns literal polynomials and uses no AG input.
-/

set_option autoImplicit false
noncomputable section

namespace CubicTenVariables.IrreducibleFromTopHomogeneousPart

open MvPolynomial

variable {σ R : Type*} [CommRing R]

/-- The component at the sum of the degrees is exactly the product of the
two highest components; lower-degree terms make no contribution. -/
theorem homogeneousComponent_totalDegree_add_mul
    (f g : MvPolynomial σ R) :
    homogeneousComponent (f.totalDegree + g.totalDegree) (f * g) =
      homogeneousComponent f.totalDegree f * homogeneousComponent g.totalDegree g := by
  classical
  have hexpand : f * g = ∑ i ∈ Finset.range (g.totalDegree + 1),
      f * homogeneousComponent i g := by
    rw [← Finset.mul_sum, sum_homogeneousComponent]
  rw [hexpand, map_sum, Finset.sum_eq_single g.totalDegree]
  · rw [HomogeneousSpanCertificates.homogeneousComponent_mul_right
      f _ (homogeneousComponent_isHomogeneous g.totalDegree g)]
    simp
  · intro i hi hne
    have hi' : i < g.totalDegree := by
      simp only [Finset.mem_range] at hi
      omega
    rw [HomogeneousSpanCertificates.homogeneousComponent_mul_right
      f _ (homogeneousComponent_isHomogeneous i g), if_pos (by omega)]
    rw [homogeneousComponent_eq_zero _ f (by omega), zero_mul]
  · simp

/-- A nonzero polynomial has a nonzero highest homogeneous component. -/
theorem topComponent_ne_zero (f : MvPolynomial σ R) (hf : f ≠ 0) :
    homogeneousComponent f.totalDegree f ≠ 0 := by
  classical
  obtain ⟨μ, hμ, hdegree⟩ := Finset.exists_mem_eq_sup f.support
    (Finsupp.support_nonempty_iff.mpr hf) (fun μ => μ.sum fun _ e => e)
  have hdegree' : μ.degree = f.totalDegree := by
    simpa only [totalDegree, Finsupp.degree, Finsupp.weight] using hdegree.symm
  intro hz
  have hc := congrArg (coeff μ) hz
  rw [coeff_homogeneousComponent, if_pos hdegree', coeff_zero] at hc
  exact (mem_support_iff.mp hμ) hc

private theorem topComponent_eq_of_totalDegree_zero
    (f : MvPolynomial σ R) (hf : f.totalDegree = 0) :
    homogeneousComponent f.totalDegree f = f := by
  rw [hf, homogeneousComponent_zero]
  exact (totalDegree_eq_zero_iff_eq_C.mp hf).symm

section Field

variable {K : Type*} [Field K]

/-- A polynomial whose highest component is a unit already has degree
zero and is itself that component. -/
theorem isUnit_of_isUnit_topComponent (f : MvPolynomial σ K)
    (hunit : IsUnit (homogeneousComponent f.totalDegree f)) : IsUnit f := by
  have hdegree : f.totalDegree = 0 :=
    ((homogeneousComponent_isHomogeneous f.totalDegree f).totalDegree hunit.ne_zero).symm.trans
      (isUnit_iff_totalDegree_of_isReduced.mp hunit).2
  rwa [topComponent_eq_of_totalDegree_zero f hdegree] at hunit

/-- Irreducibility of the highest homogeneous component implies
irreducibility of the full polynomial, including all lower-degree terms. -/
theorem irreducible_of_irreducible_topComponent (f : MvPolynomial σ K)
    (htop : Irreducible (homogeneousComponent f.totalDegree f)) : Irreducible f := by
  have hf : f ≠ 0 := by
    intro hz
    exact htop.ne_zero (by rw [hz]; simp)
  refine ⟨?_, ?_⟩
  · intro hunit
    have hdegree := (isUnit_iff_totalDegree_of_isReduced.mp hunit).2
    exact htop.not_isUnit (by
      rw [topComponent_eq_of_totalDegree_zero f hdegree]
      exact hunit)
  · intro a b hab
    have ha : a ≠ 0 := by intro hz; exact hf (by simp [hab, hz])
    have hb : b ≠ 0 := by intro hz; exact hf (by simp [hab, hz])
    have hfactor : homogeneousComponent f.totalDegree f =
        homogeneousComponent a.totalDegree a * homogeneousComponent b.totalDegree b := by
      rw [hab, totalDegree_mul_of_isDomain ha hb]
      exact homogeneousComponent_totalDegree_add_mul a b
    exact (htop.isUnit_or_isUnit hfactor).imp
      (isUnit_of_isUnit_topComponent a) (isUnit_of_isUnit_topComponent b)

/-- A degree upper bound suffices: irreducibility forces the displayed
component to be nonzero and hence to occur at the actual total degree. -/
theorem irreducible_of_irreducible_homogeneousComponent
    (f : MvPolynomial σ K) {d : ℕ} (hdegree : f.totalDegree ≤ d)
    (htop : Irreducible (homogeneousComponent d f)) : Irreducible f := by
  have heq : f.totalDegree = d := by
    apply Nat.le_antisymm hdegree
    by_contra hlt
    exact htop.ne_zero (homogeneousComponent_eq_zero d f (Nat.lt_of_not_ge hlt))
  apply irreducible_of_irreducible_topComponent f
  rwa [heq]

/-- The same criterion after an arbitrary coefficient map to a field.
This applies directly to reductions and to their algebraic closures. -/
theorem irreducible_map_of_irreducible_homogeneousComponent
    (ρ : R →+* K) (f : MvPolynomial σ R) {d : ℕ}
    (hdegree : f.totalDegree ≤ d)
    (htop : Irreducible (map ρ (homogeneousComponent d f))) :
    Irreducible (map ρ f) := by
  have hmap : homogeneousComponent d (map ρ f) = map ρ (homogeneousComponent d f) := by
    classical
    ext μ
    simp only [coeff_homogeneousComponent, coeff_map]
    split_ifs <;> simp
  apply irreducible_of_irreducible_homogeneousComponent (map ρ f)
    ((Finset.sup_mono (support_map_subset _ _)).trans hdegree)
  rwa [hmap]

end Field
end CubicTenVariables.IrreducibleFromTopHomogeneousPart
