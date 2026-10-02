import TranslatedDepthSeven.AffineTransformBounds
import TranslatedDepthSeven.PublishedCountingTheorems

/-!
# Top homogeneous parts under integral affine transforms

For the literal substitution `X i ↦ base i + m * X i`, translation does
not affect the top homogeneous part and dilation multiplies a degree-`d`
top part by `m ^ d`.  This file proves that statement for the exact
`Published.IsTopHomogeneousPart` predicate used by the affine Salberger
interface.  It also transports absolute irreducibility, since the scalar is
nonzero when `m` is positive.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped BigOperators

open Finset MvPolynomial Polynomial

private theorem starCoefficient_sum {n : ℕ}
    (base : IntVector n) (d : ℕ) (s : Finset ℕ)
    (g : ℕ → MvPolynomial (Fin n) ℤ) :
    starCoefficient (∑ k ∈ s, g k) base d =
      ∑ k ∈ s, starCoefficient (g k) base d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
      simp only [sum_insert hk, starCoefficient_add, ih]

/-- At or above the total degree, the order-`d` star coefficient is exactly
the degree-`d` homogeneous component. -/
theorem starCoefficient_eq_homogeneousComponent_of_totalDegree_le
    {n d : ℕ} (base : IntVector n) (f : MvPolynomial (Fin n) ℤ)
    (hdegree : f.totalDegree ≤ d) :
    starCoefficient f base d = MvPolynomial.homogeneousComponent d f := by
  classical
  conv_lhs => rw [← f.sum_homogeneousComponent]
  rw [starCoefficient_sum]
  by_cases heq : f.totalDegree = d
  · rw [Finset.sum_eq_single d]
    · exact starCoefficient_eq_of_isHomogeneous
        (MvPolynomial.homogeneousComponent d f) base d
        (MvPolynomial.homogeneousComponent_isHomogeneous d f)
    · intro k hk hkd
      apply starCoefficient_eq_zero_of_totalDegree_lt
      have hklt : k < d := by
        simp only [Finset.mem_range, heq] at hk
        exact lt_of_le_of_ne (Nat.le_of_lt_succ hk) hkd
      exact lt_of_le_of_lt
        (MvPolynomial.homogeneousComponent_isHomogeneous k f).totalDegree_le
        hklt
    · simp [heq]
  · have hlt : f.totalDegree < d := Nat.lt_of_le_of_ne hdegree heq
    rw [MvPolynomial.homogeneousComponent_eq_zero d f hlt]
    apply Finset.sum_eq_zero
    intro k hk
    apply starCoefficient_eq_zero_of_totalDegree_lt
    have hklt : k < d := by
      simp only [Finset.mem_range] at hk
      exact (Nat.le_of_lt_succ hk).trans_lt hlt
    exact lt_of_le_of_lt
      (MvPolynomial.homogeneousComponent_isHomogeneous k f).totalDegree_le
      hklt

/-- The degree-`d` homogeneous component of a positive integral affine
transform is the original degree-`d` component multiplied by `m ^ d`, when
`d` is the total degree. -/
theorem homogeneousComponent_integralAffineTransform_of_totalDegree_eq
    {n d : ℕ} (base : IntVector n) (m : ℕ)
    (f : MvPolynomial (Fin n) ℤ) (hdegree : f.totalDegree = d)
    (htop : MvPolynomial.homogeneousComponent d f ≠ 0) :
    MvPolynomial.homogeneousComponent d
        (integralAffineTransform base m f) =
      MvPolynomial.homogeneousComponent d f *
        MvPolynomial.C ((m : ℤ) ^ d) := by
  classical
  rw [integralAffineTransform_eq_sum_starCoefficient, map_sum]
  rw [Finset.sum_eq_single d]
  · have hstar :
        starCoefficient f base d = MvPolynomial.homogeneousComponent d f :=
      starCoefficient_eq_homogeneousComponent_of_totalDegree_le base f hdegree.le
    have hhom : (starCoefficient f base d).IsHomogeneous d :=
      starCoefficient_isHomogeneous f base d
    have hterm :
        (starCoefficient f base d * MvPolynomial.C ((m : ℤ) ^ d)).IsHomogeneous d :=
      by simpa [mul_comm] using
        (MvPolynomial.isHomogeneous_C (Fin n) ((m : ℤ) ^ d)).mul hhom
    rw [MvPolynomial.homogeneousComponent_of_mem (m := d) hterm,
      if_pos rfl, hstar]
  · intro k hk hkd
    have hkstar : (starCoefficient f base k).IsHomogeneous k :=
      starCoefficient_isHomogeneous f base k
    have hterm :
        (starCoefficient f base k * MvPolynomial.C ((m : ℤ) ^ k)).IsHomogeneous k :=
      by simpa [mul_comm] using
        (MvPolynomial.isHomogeneous_C (Fin n) ((m : ℤ) ^ k)).mul hkstar
    rw [MvPolynomial.homogeneousComponent_of_mem (m := d) hterm]
    simp [Ne.symm hkd]
  · intro hdnot
    have hmem : d ∈ (symbolicLinePolynomial f base).support := by
      rw [Polynomial.mem_support_iff]
      change starCoefficient f base d ≠ 0
      rw [starCoefficient_eq_homogeneousComponent_of_totalDegree_le
        base f hdegree.le]
      exact htop
    exact (hdnot hmem).elim

/-- The `IsTopHomogeneousPart` predicate forces the displayed degree to be
the literal total degree of the integral polynomial. -/
theorem totalDegree_eq_of_isTopHomogeneousPart
    {n d : ℕ} {f : MvPolynomial (Fin n) ℤ}
    {h : MvPolynomial (Fin n) ℚ}
    (htop : Published.IsTopHomogeneousPart f h d) :
    f.totalDegree = d := by
  have hcomponent : MvPolynomial.homogeneousComponent d f ≠ 0 := by
    intro hz
    exact htop.2.1 (by rw [htop.1, hz, map_zero])
  apply Nat.le_antisymm
  · rw [← MvPolynomial.mem_restrictTotalDegree]
    rw [← f.sum_homogeneousComponent]
    apply Submodule.sum_mem
    intro k hk
    by_cases hkd : k ≤ d
    · rw [MvPolynomial.mem_restrictTotalDegree]
      exact
        (MvPolynomial.homogeneousComponent_isHomogeneous k f).totalDegree_le.trans hkd
    · rw [htop.2.2 k (Nat.lt_of_not_ge hkd)]
      exact Submodule.zero_mem _
  · by_contra hnot
    have hlt : f.totalDegree < d := Nat.lt_of_not_ge hnot
    exact hcomponent (MvPolynomial.homogeneousComponent_eq_zero d f hlt)

/-- Exact transport of a rational top homogeneous part under the integral
substitution `X i ↦ base i + m * X i`. -/
theorem isTopHomogeneousPart_integralAffineTransform
    {n d : ℕ} (base : IntVector n) {m : ℕ} (hm : 0 < m)
    {f : MvPolynomial (Fin n) ℤ} {h : MvPolynomial (Fin n) ℚ}
    (htop : Published.IsTopHomogeneousPart f h d) :
    Published.IsTopHomogeneousPart
      (integralAffineTransform base m f)
      (MvPolynomial.C ((m : ℚ) ^ d) * h) d := by
  have hdegree : f.totalDegree = d := totalDegree_eq_of_isTopHomogeneousPart htop
  have hcomponent : MvPolynomial.homogeneousComponent d f ≠ 0 := by
    intro hz
    exact htop.2.1 (by rw [htop.1, hz, map_zero])
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨?_, mul_ne_zero (MvPolynomial.C_ne_zero.mpr (pow_ne_zero d hmQ)) htop.2.1, ?_⟩
  · rw [homogeneousComponent_integralAffineTransform_of_totalDegree_eq
      base m f hdegree hcomponent]
    simp only [map_mul, map_pow, map_natCast]
    rw [htop.1]
    ring
  · intro k hdk
    apply MvPolynomial.homogeneousComponent_eq_zero
    rw [totalDegree_integralAffineTransform hm, hdegree]
    exact hdk

/-- A positive integral affine transform preserves absolute irreducibility
of the top homogeneous part, together with the exact top-part identity. -/
theorem isTopHomogeneousPart_and_isAbsolutelyIrreducible_integralAffineTransform
    {n d : ℕ} (base : IntVector n) {m : ℕ} (hm : 0 < m)
    {f : MvPolynomial (Fin n) ℤ} {h : MvPolynomial (Fin n) ℚ}
    (htop : Published.IsTopHomogeneousPart f h d)
    (hirr : Published.IsAbsolutelyIrreducible h) :
    Published.IsTopHomogeneousPart
        (integralAffineTransform base m f)
        (MvPolynomial.C ((m : ℚ) ^ d) * h) d ∧
      Published.IsAbsolutelyIrreducible
        (MvPolynomial.C ((m : ℚ) ^ d) * h) := by
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  exact ⟨isTopHomogeneousPart_integralAffineTransform base hm htop,
    hirr.const_mul _ (pow_ne_zero d hmQ)⟩

end

end TranslatedDepthSeven
