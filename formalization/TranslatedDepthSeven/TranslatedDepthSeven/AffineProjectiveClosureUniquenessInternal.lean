import TranslatedDepthSeven.AffineIdealProjectiveClosureInternal
import TranslatedDepthSeven.ProjectiveAffineChartBridge

/-!
# Uniqueness of the homogeneous closure from one affine chart

A homogeneous prime which does not contain the homogenizing coordinate is
the projective closure of its standard affine chart.  The proof is entirely
algebraic: on every fixed homogeneous piece, dehomogenization is inverted by
homogenization, and primality lets chart membership be tested after clearing
a power of the homogenizing coordinate.

This is the saturation bridge needed to identify explicit homogeneous
linear sections with the kernel-defined projective closure used by the
bounded affine-chart projection theorem.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000

universe u

/-- Two homogeneous primes avoiding the homogenizing coordinate are equal
when their standard affine-chart ideals are equal. -/
theorem homogeneousPrime_eq_of_map_dehomogenization_eq
    {K : Type u} [Field K] {n : ℕ}
    (I J : Ideal (MvPolynomial (Option (Fin n)) K))
    (hIhom : I.IsHomogeneous
      (homogeneousSubmodule (Option (Fin n)) K))
    (hJhom : J.IsHomogeneous
      (homogeneousSubmodule (Option (Fin n)) K))
    (hIprime : I.IsPrime) (hJprime : J.IsPrime)
    (hIX : X (none : Option (Fin n)) ∉ I)
    (hJX : X (none : Option (Fin n)) ∉ J)
    (hchart : I.map multivariateDehomogenization.toRingHom =
      J.map multivariateDehomogenization.toRingHom) :
    I = J := by
  apply le_antisymm
  · intro f hf
    rw [← f.sum_homogeneousComponent]
    apply Ideal.sum_mem
    intro k _hk
    let p := homogeneousComponent k f
    have hpHom : p.IsHomogeneous k :=
      homogeneousComponent_isHomogeneous k f
    have hpI : p ∈ I := by
      have h := hIhom k hf
      change (MvPolynomial.decomposition.decompose' f k :
        MvPolynomial (Option (Fin n)) K) ∈ I at h
      simpa only [MvPolynomial.decomposition.decompose'_apply, p] using h
    have hpChart : multivariateDehomogenization p ∈
        J.map multivariateDehomogenization.toRingHom := by
      rw [← hchart]
      exact Ideal.mem_map_of_mem multivariateDehomogenization.toRingHom hpI
    have hpDegree :
        (multivariateDehomogenization p).totalDegree ≤ k :=
      (multivariateHomogenization_dehomogenization_of_isHomogeneous
        p hpHom).1
    have hpJ :
        multivariateHomogenization (multivariateDehomogenization p) k ∈ J :=
      (mem_map_dehomogenization_iff_homogenization_mem
        J hJhom hJprime hJX
        (multivariateDehomogenization p) hpDegree).1 hpChart
    rwa [(multivariateHomogenization_dehomogenization_of_isHomogeneous
      p hpHom).2] at hpJ
  · intro f hf
    rw [← f.sum_homogeneousComponent]
    apply Ideal.sum_mem
    intro k _hk
    let p := homogeneousComponent k f
    have hpHom : p.IsHomogeneous k :=
      homogeneousComponent_isHomogeneous k f
    have hpJ : p ∈ J := by
      have h := hJhom k hf
      change (MvPolynomial.decomposition.decompose' f k :
        MvPolynomial (Option (Fin n)) K) ∈ J at h
      simpa only [MvPolynomial.decomposition.decompose'_apply, p] using h
    have hpChart : multivariateDehomogenization p ∈
        I.map multivariateDehomogenization.toRingHom := by
      rw [hchart]
      exact Ideal.mem_map_of_mem multivariateDehomogenization.toRingHom hpJ
    have hpDegree :
        (multivariateDehomogenization p).totalDegree ≤ k :=
      (multivariateHomogenization_dehomogenization_of_isHomogeneous
        p hpHom).1
    have hpI :
        multivariateHomogenization (multivariateDehomogenization p) k ∈ I :=
      (mem_map_dehomogenization_iff_homogenization_mem
        I hIhom hIprime hIX
        (multivariateDehomogenization p) hpDegree).1 hpChart
    rwa [(multivariateHomogenization_dehomogenization_of_isHomogeneous
      p hpHom).2] at hpI

/-- Consecutive-coordinate form of uniqueness from the standard chart. -/
theorem homogeneousPrime_eq_of_map_standardDehomogenization_eq
    {K : Type u} [Field K] {n : ℕ}
    (I J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hIhom : I.IsHomogeneous
      (homogeneousSubmodule (Fin (n + 1)) K))
    (hJhom : J.IsHomogeneous
      (homogeneousSubmodule (Fin (n + 1)) K))
    (hIprime : I.IsPrime) (hJprime : J.IsPrime)
    (hIX : X (0 : Fin (n + 1)) ∉ I)
    (hJX : X (0 : Fin (n + 1)) ∉ J)
    (hchart : I.map (standardDehomogenizationHom K n) =
      J.map (standardDehomogenizationHom K n)) :
    I = J := by
  let E := MvPolynomial.renameEquiv K (_root_.finSuccEquiv n)
  let I' := I.map E
  let J' := J.map E
  obtain ⟨hI'hom, hI'prime, hI'X⟩ :=
    finSuccRename_homogeneousPrime_avoids_none I hIhom hIprime hIX
  obtain ⟨hJ'hom, hJ'prime, hJ'X⟩ :=
    finSuccRename_homogeneousPrime_avoids_none J hJhom hJprime hJX
  have hI'chart :
      I'.map multivariateDehomogenization.toRingHom =
        I.map (standardDehomogenizationHom K n) :=
    map_standardDehomogenizationHom_finSuccRename I
  have hJ'chart :
      J'.map multivariateDehomogenization.toRingHom =
        J.map (standardDehomogenizationHom K n) :=
    map_standardDehomogenizationHom_finSuccRename J
  have hIJ' : I' = J' := by
    apply homogeneousPrime_eq_of_map_dehomogenization_eq
      I' J' hI'hom hJ'hom hI'prime hJ'prime hI'X hJ'X
    rw [hI'chart, hJ'chart, hchart]
  have hIback : I'.map E.symm = I := by
    exact Ideal.map_of_equiv E.toRingEquiv
  have hJback : J'.map E.symm = J := by
    exact Ideal.map_of_equiv E.toRingEquiv
  rw [← hIback, ← hJback, hIJ']

/-- A homogeneous prime model whose standard chart is the affine ideal is
literally its kernel-defined projective closure. -/
theorem eq_affineIdealProjectiveClosure_of_prime_homogeneous_chart
    {n : ℕ}
    (J : Ideal (MvPolynomial (Fin n) ℚ))
    (hJprime : J.IsPrime)
    (P : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
    (hPprime : P.IsPrime)
    (hPhom : P.IsHomogeneous
      (homogeneousSubmodule (Fin (n + 1)) ℚ))
    (hPX : X (0 : Fin (n + 1)) ∉ P)
    (hchart : P.map (standardDehomogenizationHom ℚ n) = J) :
    P = affineIdealProjectiveClosure J := by
  apply homogeneousPrime_eq_of_map_standardDehomogenization_eq
    P (affineIdealProjectiveClosure J)
    hPhom (affineIdealProjectiveClosure_isHomogeneous J)
    hPprime (affineIdealProjectiveClosure_isPrime J hJprime)
    hPX (affineIdealProjectiveClosure_X_zero_not_mem J hJprime)
  rw [hchart,
    map_affineIdealProjectiveClosure_standardDehomogenization J]

end

end TranslatedDepthSeven
