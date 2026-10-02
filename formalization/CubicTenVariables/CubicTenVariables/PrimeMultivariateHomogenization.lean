import TranslatedDepthSeven.HomogeneousChartPolynomialEmbedding
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex

/-!
Homogenization to the actual total degree preserves a prime principal ideal.
The proof identifies the homogenized ideal with the kernel of the scaling map
into a polynomial ring over the original affine quotient. No geometric input
is used.
-/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PrimeMultivariateHomogenization

open MvPolynomial TranslatedDepthSeven
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K] {n : ℕ}

/-- Multiplication is compatible with lossless fixed-degree homogenization. -/
theorem homogenization_mul (f h : MvPolynomial (Fin n) K) (a b : ℕ)
    (hf : f.totalDegree ≤ a) (hh : h.totalDegree ≤ b) :
    multivariateHomogenization (f * h) (a + b) =
      multivariateHomogenization f a * multivariateHomogenization h b := by
  apply multivariateDehomogenization_injective_of_isHomogeneous
    (multivariateHomogenization_isHomogeneous _ _)
    ((multivariateHomogenization_isHomogeneous f a).mul
      (multivariateHomogenization_isHomogeneous h b))
  rw [map_mul, multivariateDehomogenization_homogenization f a hf,
    multivariateDehomogenization_homogenization h b hh,
    multivariateDehomogenization_homogenization (f * h) (a + b)
      (le_trans (totalDegree_mul f h) (Nat.add_le_add hf hh))]

/-- Affine divisibility lifts to each homogeneous piece, when the divisor
is homogenized to its actual total degree. -/
theorem homogenization_dvd_of_dehomogenization_dvd
    (f : MvPolynomial (Fin n) K)
    {g : MvPolynomial (Option (Fin n)) K} {k : ℕ}
    (hg : g.IsHomogeneous k) (hdiv : f ∣ multivariateDehomogenization g) :
    multivariateHomogenization f f.totalDegree ∣ g := by
  have hrecover := multivariateHomogenization_dehomogenization_of_isHomogeneous g hg
  by_cases hz : multivariateDehomogenization g = 0
  · have hgzero : g = 0 := by
      apply multivariateDehomogenization_injective_of_isHomogeneous hg
        (isHomogeneous_zero _ _ k)
      simpa using hz
    rw [hgzero]
    exact dvd_zero _
  obtain ⟨h, heq⟩ := hdiv
  have hfzero : f ≠ 0 := by intro hf; apply hz; simp [heq, hf]
  have hhzero : h ≠ 0 := by intro hh; apply hz; simp [heq, hh]
  have hdegree : f.totalDegree + h.totalDegree ≤ k := by
    rw [heq, totalDegree_mul_of_isDomain hfzero hhzero] at hrecover
    exact hrecover.1
  rw [← hrecover.2, heq,
    multivariateHomogenization_raise_degree (f * h)
      (le_of_eq (totalDegree_mul_of_isDomain hfzero hhzero)) hdegree,
    homogenization_mul f h _ _ le_rfl le_rfl]
  exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _

/-- The homogenized principal ideal is exactly the kernel of the scaled
evaluation in the affine quotient, even without a primality assumption. -/
theorem homogenization_ideal_eq_kernel (f : MvPolynomial (Fin n) K) :
    Ideal.span {multivariateHomogenization f f.totalDegree} =
      RingHom.ker (homogeneousScalingHom
        ((Ideal.Quotient.mkₐ K (Ideal.span {f})).comp
          multivariateDehomogenization)).toRingHom := by
  classical
  let J : Ideal (MvPolynomial (Fin n) K) := Ideal.span {f}
  let D : MvPolynomial (Option (Fin n)) K →ₐ[K]
      (MvPolynomial (Fin n) K ⧸ J) :=
    (Ideal.Quotient.mkₐ K J).comp multivariateDehomogenization
  change Ideal.span {multivariateHomogenization f f.totalDegree} =
    RingHom.ker (homogeneousScalingHom D).toRingHom
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro a ha
    rcases Set.mem_singleton_iff.mp ha with rfl
    change homogeneousScalingHom D (multivariateHomogenization f f.totalDegree) = 0
    rw [homogeneousScalingHom_apply_of_isHomogeneous D _
      (multivariateHomogenization_isHomogeneous f f.totalDegree)]
    have hD : D (multivariateHomogenization f f.totalDegree) = 0 := by
      change Ideal.Quotient.mk J
        (multivariateDehomogenization (multivariateHomogenization f f.totalDegree)) = 0
      rw [multivariateDehomogenization_homogenization f f.totalDegree le_rfl]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    simp [hD]
  · intro g hg
    change homogeneousScalingHom D g = 0 at hg
    have hcomponents : ∀ k, homogeneousComponent k g ∈
        Ideal.span {multivariateHomogenization f f.totalDegree} := by
      intro k
      have hcoeff := congrArg (fun p => Polynomial.coeff p k) hg
      dsimp only at hcoeff
      rw [homogeneousScalingHom_coeff, Polynomial.coeff_zero] at hcoeff
      have hmem : multivariateDehomogenization (homogeneousComponent k g) ∈ J :=
        Ideal.Quotient.eq_zero_iff_mem.mp hcoeff
      apply Ideal.mem_span_singleton.mpr
      exact homogenization_dvd_of_dehomogenization_dvd f
        (homogeneousComponent_isHomogeneous k g) (Ideal.mem_span_singleton.mp hmem)
    rw [← g.sum_homogeneousComponent]
    exact Ideal.sum_mem _ fun k _ => hcomponents k

/-- Homogenization to the actual total degree preserves a prime principal
ideal over an arbitrary field. -/
theorem isPrime (f : MvPolynomial (Fin n) K) (d : ℕ)
    (hd : f.totalDegree = d) (hprime : (Ideal.span {f}).IsPrime) :
    (Ideal.span {multivariateHomogenization f d}).IsPrime := by
  letI : (Ideal.span {f}).IsPrime := hprime
  rw [← hd, homogenization_ideal_eq_kernel]
  exact RingHom.ker_isPrime _

end CubicTenVariables.PrimeMultivariateHomogenization
