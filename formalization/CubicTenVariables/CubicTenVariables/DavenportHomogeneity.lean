import HessianTheorem11.HessianLinearity
import HessianTheorem11.ReducedDeterminantalTangent
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Algebra.Polynomial.Roots

/-! Homogeneity of the rational exact-rank locus's vanishing ideal.

Nonzero dilation preserves the exact Hessian rank. A polynomial vanishing on
such a dilation-stable set has every homogeneous component vanishing there:
substitute `T*x`, use infinitely many nonzero scalars, then take coefficients.
The statements concern the actual rational point set and its vanishing ideal.
They assert neither a dimension bound nor an integer-point counting estimate.

The short coefficient-extraction and minimal-prime proofs below are adapted
from the existing project files `TranslatedDepthSeven/HomogeneousCone.lean`,
`HomogeneousChartPolynomialEmbedding.lean`, `HomogeneousMinimalComponents.lean`,
and `FiniteEquationMinimalComponents.lean`. They are repeated as a small
independently checked slice to avoid those files' much larger import graph.
-/

noncomputable section
namespace CubicTenVariables.DavenportHomogeneity
open MvPolynomial HessianTheorem11

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem eval_smul_of_isHomogeneous
    {R σ : Type*} [CommSemiring R]
    (f : MvPolynomial σ R) (x : σ → R) (a : R) (d : ℕ)
    (hf : f.IsHomogeneous d) :
    eval (fun i => a * x i) f = a ^ d * eval x f := by
  induction hf using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simp [ihp, ihq, mul_add]
  | monomial m r hm =>
      rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
      simp only [mul_pow, Finsupp.prod, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum]
      have hsum : ∑ i ∈ m.support, m i = d := by
        simpa only [Finsupp.weight_apply, Pi.one_apply, nsmul_eq_mul,
          mul_one, Finsupp.sum] using hm
      rw [hsum]
      ac_rfl

section ScalingPolynomial
variable {K : Type*} [Field K] {σ : Type*}

/-- Substitution of a new indeterminate times each coordinate. -/
def homogeneousScalingHom (x : σ → K) : MvPolynomial σ K →ₐ[K] Polynomial K :=
  aeval fun i => Polynomial.X * Polynomial.C (x i)

private theorem homogeneousScalingHom_apply_of_isHomogeneous
    (x : σ → K) (f : MvPolynomial σ K) {k : ℕ} (hf : f.IsHomogeneous k) :
    homogeneousScalingHom x f = Polynomial.C (eval x f) * Polynomial.X ^ k := by
  have hE :
      (aeval (fun i => Polynomial.C (x i)) : MvPolynomial σ K →ₐ[K] Polynomial K) =
      Polynomial.CAlgHom.comp (aeval x) := by
    ext i
    simp
  have hscale := eval_smul_of_isHomogeneous
    (MvPolynomial.map (algebraMap K (Polynomial K)) f)
    (fun i => Polynomial.C (x i)) Polynomial.X k
    (hf.map (algebraMap K (Polynomial K)))
  simp only [MvPolynomial.eval_map] at hscale
  change homogeneousScalingHom x f = Polynomial.X ^ k *
    (aeval (fun i => Polynomial.C (x i)) : MvPolynomial σ K →ₐ[K] Polynomial K) f
    at hscale
  rw [hE] at hscale
  simpa only [AlgHom.comp_apply, Polynomial.CAlgHom_apply, aeval_eq_eval, mul_comm]
    using hscale

/-- The coefficients of the scaled polynomial are exactly evaluations of
the homogeneous components of the original polynomial. -/
theorem homogeneousScalingHom_coeff (x : σ → K) (f : MvPolynomial σ K) (k : ℕ) :
    (homogeneousScalingHom x f).coeff k = eval x (homogeneousComponent k f) := by
  classical
  have hsum : homogeneousScalingHom x f =
      ∑ j ∈ Finset.range (f.totalDegree + 1),
        Polynomial.C (eval x (homogeneousComponent j f)) * Polynomial.X ^ j := by
    conv_lhs => rw [← f.sum_homogeneousComponent]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact homogeneousScalingHom_apply_of_isHomogeneous x
      (homogeneousComponent j f) (homogeneousComponent_isHomogeneous j f)
  rw [hsum, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  by_cases hk : k ∈ Finset.range (f.totalDegree + 1)
  · simp [hk]
  · have hkdegree : f.totalDegree < k := by
      simp only [Finset.mem_range] at hk
      omega
    simp [hk, homogeneousComponent_eq_zero k f hkdegree]

end ScalingPolynomial

section InfiniteField
variable {K : Type*} [Field K] [Infinite K] {σ : Type*}

omit [Infinite K] in
/-- Evaluating the existing coefficient-extraction polynomial at `c` is
literal evaluation of the original polynomial at the dilated point. -/
theorem eval_homogeneousScalingHom (x : σ → K) (f : MvPolynomial σ K) (c : K) :
    (homogeneousScalingHom x f).eval c = eval (c • x) f := by
  have hcomp : (Polynomial.aeval c).comp (homogeneousScalingHom x) =
      aeval (c • x) := by
    ext i
    simp [homogeneousScalingHom, Pi.smul_apply, smul_eq_mul]
    ring
  exact congrArg (fun g : MvPolynomial σ K →ₐ[K] K => g f) hcomp

/-- The vanishing ideal of a point set stable under nonzero dilations is
homogeneous. Stability at scalar zero is not needed. -/
theorem vanishingIdeal_isHomogeneous_of_nonzero_smul
    (Z : Set (σ → K))
    (hscale : ∀ (c : K), c ≠ 0 → ∀ x ∈ Z, c • x ∈ Z) :
    (vanishingIdeal K Z).IsHomogeneous (homogeneousSubmodule σ K) := by
  classical
  intro d f hf
  change (MvPolynomial.decomposition.decompose' f d : MvPolynomial σ K) ∈ _
  rw [MvPolynomial.decomposition.decompose'_apply]
  intro x hx
  let p : Polynomial K := homogeneousScalingHom x f
  have hpval (c : K) (hc : c ≠ 0) : p.eval c = 0 := by
    rw [show p = homogeneousScalingHom x f from rfl,
      eval_homogeneousScalingHom]
    exact hf (c • x) (hscale c hc x hx)
  have hpX : p * Polynomial.X = 0 := by
    apply Polynomial.funext
    intro c
    by_cases hc : c = 0
    · simp [hc]
    · simp [hpval c hc]
  have hp : p = 0 := (mul_eq_zero.mp hpX).resolve_right Polynomial.X_ne_zero
  have hc := congrArg (fun q : Polynomial K => q.coeff d) hp
  simpa only [p, homogeneousScalingHom_coeff, Polynomial.coeff_zero] using hc

/-- Minimal primes of this actual vanishing ideal are homogeneous too. -/
theorem minimalPrime_isHomogeneous_of_nonzero_smul
    (Z : Set (σ → K))
    (hscale : ∀ (c : K), c ≠ 0 → ∀ x ∈ Z, c • x ∈ Z)
    {P : Ideal (MvPolynomial σ K)} (hP : P ∈ (vanishingIdeal K Z).minimalPrimes) :
    P.IsHomogeneous (homogeneousSubmodule σ K) := by
  let 𝒜 := homogeneousSubmodule σ K
  have hI := vanishingIdeal_isHomogeneous_of_nonzero_smul Z hscale
  have hPprime : P.IsPrime := Ideal.minimalPrimes_isPrime hP
  have hIcore : vanishingIdeal K Z ≤ (P.homogeneousCore 𝒜).toIdeal :=
    hI.toIdeal_homogeneousCore_eq_self.symm.trans_le
      (Ideal.homogeneousCore_mono 𝒜 hP.1.2)
  have hcoreP : (P.homogeneousCore 𝒜).toIdeal ≤ P :=
    Ideal.toIdeal_homogeneousCore_le 𝒜 P
  have hPcore : P ≤ (P.homogeneousCore 𝒜).toIdeal :=
    hP.2 ⟨hPprime.homogeneousCore, hIcore⟩ hcoreP
  rw [Ideal.IsHomogeneous.iff_eq]
  exact le_antisymm hcoreP hPcore

end InfiniteField

section RationalRankLocus
variable {n r : ℕ}

/-- A nonzero rational dilation preserves the full Hessian's exact rank. -/
theorem hessian_rank_smul_eq
    (F : MvPolynomial (Fin n) ℚ) (hF : F.IsHomogeneous 3)
    (c : ℚ) (hc : c ≠ 0) (x : Fin n → ℚ) :
    (hessian F (c • x)).rank = (hessian F x).rank := by
  classical
  rw [hessian_smul hF, Matrix.smul_eq_diagonal_mul]
  apply Matrix.rank_mul_eq_right_of_isUnit_det
  rw [Matrix.det_diagonal]
  exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun _ _ => hc)

/-- Homogeneity for the reduced rational exact-rank locus, without any
geometric closure, smoothness, anisotropy, or dimension premise. -/
theorem rank_locus_vanishingIdeal_isHomogeneous
    (F : MvPolynomial (Fin n) ℚ) (hF : F.IsHomogeneous 3) (r : ℕ) :
    (vanishingIdeal ℚ {x : Fin n → ℚ | (hessian F x).rank = r}).IsHomogeneous
      (homogeneousSubmodule (Fin n) ℚ) := by
  apply vanishingIdeal_isHomogeneous_of_nonzero_smul
  intro c hc x hx
  exact (hessian_rank_smul_eq F hF c hc x).trans hx

/-- Every minimal-prime component of the rational rank locus is homogeneous. -/
theorem rank_locus_minimalPrime_isHomogeneous
    (F : MvPolynomial (Fin n) ℚ) (hF : F.IsHomogeneous 3)
    {P : Ideal (MvPolynomial (Fin n) ℚ)}
    (hP : P ∈ (vanishingIdeal ℚ {x : Fin n → ℚ | (hessian F x).rank = r}).minimalPrimes) :
    P.IsHomogeneous (homogeneousSubmodule (Fin n) ℚ) := by
  apply minimalPrime_isHomogeneous_of_nonzero_smul _ _ hP
  intro c hc x hx
  exact (hessian_rank_smul_eq F hF c hc x).trans hx

/-- The literal finite list of minimal primes of an ideal of the rational
polynomial ring. No choice of equations or geometric closure is involved. -/
def finiteMinimalPrimes (I : Ideal (MvPolynomial (Fin n) ℚ)) :
    Finset (Ideal (MvPolynomial (Fin n) ℚ)) :=
  I.finite_minimalPrimes_of_isNoetherianRing.toFinset

@[simp] theorem mem_finiteMinimalPrimes_iff
    (I P : Ideal (MvPolynomial (Fin n) ℚ)) :
    P ∈ finiteMinimalPrimes I ↔ P ∈ I.minimalPrimes := by
  simp [finiteMinimalPrimes]

/-- Every rational point in the exact-rank locus lies in one member of its
actual finite list of minimal-prime components. -/
theorem rank_locus_point_in_finite_minimalPrime
    (F : MvPolynomial (Fin n) ℚ) (x : Fin n → ℚ)
    (hx : (hessian F x).rank = r) :
    ∃ P ∈ finiteMinimalPrimes
        (vanishingIdeal ℚ {y : Fin n → ℚ | (hessian F y).rank = r}),
      ∀ f ∈ P, eval x f = 0 := by
  let Z : Set (Fin n → ℚ) := {y | (hessian F y).rank = r}
  have hle : vanishingIdeal ℚ Z ≤ vanishingIdeal ℚ {x} :=
    vanishingIdeal_anti_mono (Set.singleton_subset_iff.mpr hx)
  obtain ⟨P, hP, hPx⟩ := Ideal.exists_minimalPrimes_le hle
  refine ⟨P, (mem_finiteMinimalPrimes_iff _ _).mpr hP, ?_⟩
  intro f hf
  exact (hPx hf) x rfl

end RationalRankLocus
end CubicTenVariables.DavenportHomogeneity
