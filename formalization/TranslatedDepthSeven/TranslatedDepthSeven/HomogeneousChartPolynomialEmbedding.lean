import TranslatedDepthSeven.ProjectiveAffineChartBridge
import TranslatedDepthSeven.HomogeneousCone
import Mathlib.RingTheory.Algebraic.Integral

/-!
# The cone domain inside the polynomial ring over a chart

If `R` is the quotient ring of the chart `X_none = 1`, the substitution
`X_i ↦ T * z_i` embeds the homogeneous cone domain in `R[T]`.  Injectivity
is checked coefficient by coefficient: the coefficient of `T^k` is the
dehomogenization of the degree-k homogeneous component.  Homogeneous
membership in the chart reflects to the original prime ideal because the
homogenizing coordinate is not in that prime.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000

universe u

variable {K : Type u} [Field K]

/-- Multiply every coordinate of a polynomial-algebra map by a new
indeterminate. -/
def homogeneousScalingHom {σ : Type*} {R : Type*} [CommRing R] [Algebra K R]
    (D : MvPolynomial σ K →ₐ[K] R) :
    MvPolynomial σ K →ₐ[K] Polynomial R :=
  MvPolynomial.aeval fun i ↦ Polynomial.X * Polynomial.C (D (MvPolynomial.X i))

/-- A degree-k homogeneous form acquires exactly the factor `T^k`. -/
theorem homogeneousScalingHom_apply_of_isHomogeneous
    {σ : Type*} {R : Type*} [CommRing R] [Algebra K R]
    (D : MvPolynomial σ K →ₐ[K] R)
    (f : MvPolynomial σ K) {k : ℕ} (hf : f.IsHomogeneous k) :
    homogeneousScalingHom D f = Polynomial.C (D f) * Polynomial.X ^ k := by
  have hE :
      (MvPolynomial.aeval (fun i ↦ Polynomial.C (D (MvPolynomial.X i))) :
        MvPolynomial σ K →ₐ[K] Polynomial R) =
      Polynomial.CAlgHom.comp D := by
    ext i
    simp
  have hscale := eval_smul_of_isHomogeneous
    (MvPolynomial.map (algebraMap K (Polynomial R)) f)
    (fun i ↦ Polynomial.C (D (MvPolynomial.X i))) Polynomial.X k
    (hf.map (algebraMap K (Polynomial R)))
  simp only [MvPolynomial.eval_map] at hscale
  change homogeneousScalingHom D f = Polynomial.X ^ k *
    (MvPolynomial.aeval (fun i ↦ Polynomial.C (D (MvPolynomial.X i))) :
      MvPolynomial σ K →ₐ[K] Polynomial R) f at hscale
  rw [hE] at hscale
  simpa only [AlgHom.comp_apply, Polynomial.CAlgHom_apply, mul_comm] using hscale

/-- Every coefficient of the scaled polynomial is the image of the
corresponding homogeneous component. -/
theorem homogeneousScalingHom_coeff
    {σ : Type*} {R : Type*} [CommRing R] [Algebra K R]
    (D : MvPolynomial σ K →ₐ[K] R)
    (f : MvPolynomial σ K) (k : ℕ) :
    (homogeneousScalingHom D f).coeff k = D (homogeneousComponent k f) := by
  classical
  have hsum : homogeneousScalingHom D f =
      ∑ j ∈ Finset.range (f.totalDegree + 1),
        Polynomial.C (D (homogeneousComponent j f)) * Polynomial.X ^ j := by
    conv_lhs => rw [← f.sum_homogeneousComponent]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact homogeneousScalingHom_apply_of_isHomogeneous D
      (homogeneousComponent j f) (homogeneousComponent_isHomogeneous j f)
  rw [hsum, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  by_cases hk : k ∈ Finset.range (f.totalDegree + 1)
  · simp [hk]
  · have hkdegree : f.totalDegree < k := by
      simp only [Finset.mem_range] at hk
      omega
    simp [hk, homogeneousComponent_eq_zero k f hkdegree]

/-- Evaluation in the literal affine-chart quotient. -/
def optionChartQuotientEvaluation {n : ℕ}
    (I : Ideal (MvPolynomial (Option (Fin n)) K)) :
    MvPolynomial (Option (Fin n)) K →ₐ[K]
      (MvPolynomial (Fin n) K ⧸ I.map multivariateDehomogenization.toRingHom) :=
  (Ideal.Quotient.mkₐ K (I.map multivariateDehomogenization.toRingHom)).comp
    multivariateDehomogenization

/-- The kernel of the scaled chart map is precisely the homogeneous
projective prime. -/
theorem homogeneousScalingHom_optionChart_ker
    {n : ℕ} (I : Ideal (MvPolynomial (Option (Fin n)) K))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Option (Fin n)) K))
    (hprime : I.IsPrime)
    (hX : MvPolynomial.X (none : Option (Fin n)) ∉ I) :
    RingHom.ker (homogeneousScalingHom (optionChartQuotientEvaluation I)).toRingHom = I := by
  classical
  ext f
  change homogeneousScalingHom (optionChartQuotientEvaluation I) f = 0 ↔ f ∈ I
  constructor
  · intro hf
    have hcomponents : ∀ k, homogeneousComponent k f ∈ I := by
      intro k
      have hcoef := congrArg (fun p ↦ Polynomial.coeff p k) hf
      dsimp only at hcoef
      rw [homogeneousScalingHom_coeff, Polynomial.coeff_zero] at hcoef
      have hchart : multivariateDehomogenization (homogeneousComponent k f) ∈
          I.map multivariateDehomogenization.toRingHom := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        exact hcoef
      have hrecover := multivariateHomogenization_dehomogenization_of_isHomogeneous
        (homogeneousComponent k f) (homogeneousComponent_isHomogeneous k f)
      have hmem := (mem_map_dehomogenization_iff_homogenization_mem
        I hI hprime hX (multivariateDehomogenization (homogeneousComponent k f))
        hrecover.1).mp hchart
      rwa [hrecover.2] at hmem
    rw [← f.sum_homogeneousComponent]
    exact I.sum_mem fun k hk ↦ hcomponents k
  · intro hf
    apply Polynomial.ext
    intro k
    rw [homogeneousScalingHom_coeff, Polynomial.coeff_zero]
    have hkI : homogeneousComponent k f ∈ I := by
      have hk := hI k hf
      change (MvPolynomial.decomposition.decompose' f k :
        MvPolynomial (Option (Fin n)) K) ∈ I at hk
      simpa only [MvPolynomial.decomposition.decompose'_apply] using hk
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_map_of_mem multivariateDehomogenization.toRingHom hkI

/-- The concrete cone-to-chart-polynomial embedding. -/
def optionConeChartPolynomialEmbedding
    {n : ℕ} (I : Ideal (MvPolynomial (Option (Fin n)) K))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Option (Fin n)) K))
    (hprime : I.IsPrime)
    (hX : MvPolynomial.X (none : Option (Fin n)) ∉ I) :
    (MvPolynomial (Option (Fin n)) K ⧸ I) →ₐ[K]
      Polynomial (MvPolynomial (Fin n) K ⧸
        I.map multivariateDehomogenization.toRingHom) :=
  Ideal.Quotient.liftₐ I (homogeneousScalingHom (optionChartQuotientEvaluation I))
    (by
      intro f hf
      have hmem : f ∈ RingHom.ker
          (homogeneousScalingHom (optionChartQuotientEvaluation I)).toRingHom := by
        rw [homogeneousScalingHom_optionChart_ker I hI hprime hX]
        exact hf
      exact hmem)

theorem optionConeChartPolynomialEmbedding_injective
    {n : ℕ} (I : Ideal (MvPolynomial (Option (Fin n)) K))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Option (Fin n)) K))
    (hprime : I.IsPrime)
    (hX : MvPolynomial.X (none : Option (Fin n)) ∉ I) :
    Function.Injective (optionConeChartPolynomialEmbedding I hI hprime hX) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [← homogeneousScalingHom_optionChart_ker I hI hprime hX]
  exact hx

end

end TranslatedDepthSeven
