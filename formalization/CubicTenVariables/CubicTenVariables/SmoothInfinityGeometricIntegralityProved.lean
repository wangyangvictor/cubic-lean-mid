import CubicTenVariables.Literature.GenericFiberGeometricIntegrality
import CubicTenVariables.PrimeMultivariateHomogenization
import TranslatedDepthSeven.SmoothRationalPointGeometricDomainInternal
import TranslatedDepthSeven.ProjectiveConeHilbertShift
import TranslatedDepthSeven.DehomogenizationBaseChange
import TranslatedDepthSeven.ProjectiveAffineChartBridge
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-!
Concrete hypersurface adapters for the internally proved smooth-rational-point
geometric-integrality theorem. No geometric-integrality premise is introduced.
-/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.SmoothInfinityGeometricIntegralityProved

open MvPolynomial TranslatedDepthSeven
open scoped TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

/-- A prime affine hypersurface with one nonzero partial at a rational zero
remains prime over every extension field, in arbitrary characteristic. -/
theorem coefficientExtension_isPrime_of_partial
    {K L : Type*} [Field K] [Field L] [Algebra K L] {N : ℕ}
    (f : MvPolynomial (Fin N) K)
    (hprime : (Ideal.span {f}).IsPrime)
    (z : Fin N → K) (hz : eval z f = 0)
    (i : Fin N) (hi : eval z (pderiv i f) ≠ 0) :
    (Ideal.span {map (algebraMap K L) f}).IsPrime := by
  classical
  let J : Ideal (MvPolynomial (Fin N) K) := Ideal.span {f}
  letI : J.IsPrime := hprime
  let equations : Fin 1 → MvPolynomial (Fin N) K := fun _ => f
  let cols : Fin 1 → Fin N := fun _ => i
  have hcols : Function.Injective cols := fun _ _ _ => Subsingleton.elim _ _
  have hspan : Ideal.span (Set.range equations) = J := by
    congr 1
    ext x
    simp [equations]
  have hD : selectedJacobianDeterminant equations cols = pderiv i f := by
    simp [selectedJacobianDeterminant, equations, cols]
  let a : MvPolynomial (Fin N) K ⧸ J := Ideal.Quotient.mk J (pderiv i f)
  have hstd : Algebra.IsStandardSmoothOfRelativeDimension (N - 1) K
      (Localization.Away a) := by
    have h := local_equations_selectedJacobian_standardSmooth_principalOpen
      J equations cols hcols 1 (by rw [hspan]) (by intro g hg; simpa [hspan])
    change Algebra.IsStandardSmoothOfRelativeDimension (N - 1) K
      (Localization.Away ((Ideal.Quotient.mk J) (1 * selectedJacobianDeterminant equations cols))) at h
    rw [one_mul, hD] at h
    exact h
  have hzJ : J ≤ RingHom.ker (aeval z).toRingHom := by
    apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    simpa using hz
  let aug := affineQuotientRationalPoint J z hzJ
  have ha : aug a ≠ 0 := hi
  have ha0 : a ≠ 0 := by intro h; exact ha (by simp [h])
  have hM : Submonoid.powers a ≤ nonZeroDivisors (MvPolynomial (Fin N) K ⧸ J) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors ha0
  let B := Localization.Away a
  letI : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B hM
  letI : Algebra.IsStandardSmoothOfRelativeDimension (N - 1) K B := hstd
  let g : (MvPolynomial (Fin N) K ⧸ J) →ₐ[K] B := IsScalarTower.toAlgHom K _ _
  have hg : Function.Injective g := IsLocalization.injective B hM
  let augB : B →ₐ[K] K := IsLocalization.liftAlgHom
    (M := Submonoid.powers a) (f := aug) (fun y => by
      obtain ⟨m, hm⟩ := y.property
      apply isUnit_iff_ne_zero.mpr
      change aug (y : MvPolynomial (Fin N) K ⧸ J) ≠ 0
      rw [← hm, map_pow]
      exact pow_ne_zero m ha)
  letI : IsDomain (L ⊗[K] (MvPolynomial (Fin N) K ⧸ J)) :=
    tensorProduct_isDomain_of_injective_into_standardSmooth_rationalPoint
      g hg augB (N - 1) L
  have hmap : J.map (map (algebraMap K L)) =
      Ideal.span {map (algebraMap K L) f} := by
    simp only [J, Ideal.map_span, Set.image_singleton]
  rw [← hmap]
  apply (Ideal.Quotient.isDomain_iff_prime _).mp
  exact (polynomialQuotientTensorAlgEquiv (L := L) J).toMulEquiv.isDomain _

/-- The same criterion for any finite variable set. -/
theorem coefficientExtension_isPrime_of_partial_finite
    {K L σ : Type*} [Field K] [Field L] [Algebra K L] [Fintype σ]
    (f : MvPolynomial σ K) (hprime : (Ideal.span {f}).IsPrime)
    (z : σ → K) (hz : eval z f = 0)
    (i : σ) (hi : eval z (pderiv i f) ≠ 0) :
    (Ideal.span {map (algebraMap K L) f}).IsPrime := by
  classical
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let E := MvPolynomial.renameEquiv K e
  letI : (Ideal.span {f}).IsPrime := hprime
  have hf : (Ideal.span {rename e f}).IsPrime := by
    have hh : ((Ideal.span {f}).map E).IsPrime := inferInstance
    simpa only [Ideal.map_span, Set.image_singleton, E, renameEquiv_apply] using hh
  have hz' : eval (z ∘ e.symm) (rename e f) = 0 := by
    simpa [eval_rename, Function.comp_def] using hz
  have hi' : eval (z ∘ e.symm) (pderiv (e i) (rename e f)) ≠ 0 := by
    rw [pderiv_rename e.injective]
    simpa [eval_rename, Function.comp_def] using hi
  have hp := coefficientExtension_isPrime_of_partial (L := L)
    (rename e f) hf (z ∘ e.symm) hz' (e i) hi'
  let I : Ideal (MvPolynomial σ L) := Ideal.span {map (algebraMap K L) f}
  let EL := MvPolynomial.renameEquiv L e
  have hmap : I.map EL = Ideal.span {map (algebraMap K L) (rename e f)} := by
    simp only [I, Ideal.map_span, Set.image_singleton, EL, renameEquiv_apply, map_rename]
  letI : (I.map EL).IsPrime := hmap ▸ hp
  have hc : ((I.map EL).comap EL).IsPrime := inferInstance
  simpa only [Ideal.comap_map_of_bijective _ EL.bijective] using hc

/-- The point on the hyperplane at infinity represented by `x`. -/
def infinityPoint {K σ : Type*} [Zero K] (x : σ → K) : Option σ → K
  | none => 0
  | some i => x i

/-- On the hyperplane at infinity only the top homogeneous component survives. -/
theorem eval_homogenization_infinity
    {K σ : Type*} [Field K] (f : MvPolynomial σ K) (d : ℕ) (x : σ → K) :
    eval (infinityPoint x) (multivariateHomogenization f d) =
      eval x (homogeneousComponent d f) := by
  classical
  rw [multivariateHomogenization, map_sum]
  rw [Finset.sum_eq_single d]
  · simp [infinityPoint, eval_rename, Function.comp_def]
  · intro k hk hkd
    have hlt : k < d := by simp only [Finset.mem_range] at hk; omega
    simp [infinityPoint, Nat.ne_of_gt (Nat.sub_pos_of_lt hlt)]
  · simp

/-- Old-coordinate partials at infinity are exactly the partials of the top form. -/
theorem eval_pderiv_homogenization_infinity
    {K σ : Type*} [Field K] (f : MvPolynomial σ K) (d : ℕ) (x : σ → K) (i : σ) :
    eval (infinityPoint x) (pderiv (some i) (multivariateHomogenization f d)) =
      eval x (pderiv i (homogeneousComponent d f)) := by
  classical
  rw [multivariateHomogenization, map_sum, map_sum]
  rw [Finset.sum_eq_single d]
  · simp [pderiv_rename (Option.some_injective σ), infinityPoint,
      eval_rename, Function.comp_def]
  · intro k hk hkd
    have hlt : k < d := by simp only [Finset.mem_range] at hk; omega
    simp [infinityPoint, Nat.ne_of_gt (Nat.sub_pos_of_lt hlt)]
  · simp

/-- A geometrically prime homogenization gives a prime affine chart. The
positive degree prevents the dehomogenized equation from being a unit. -/
theorem coefficientExtension_isPrime_of_homogenization
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n d : ℕ}
    (f : MvPolynomial (Fin n) K) (hfd : f.totalDegree = d) (hd : 0 < d)
    (hprime : (Ideal.span {map (algebraMap K L)
      (multivariateHomogenization f d)}).IsPrime) :
    (Ideal.span {map (algebraMap K L) f}).IsPrime := by
  classical
  let J : Ideal (MvPolynomial (Option (Fin n)) L) :=
    Ideal.span {map (algebraMap K L) (multivariateHomogenization f d)}
  have hhom : J.IsHomogeneous (homogeneousSubmodule (Option (Fin n)) L) := by
    apply Ideal.homogeneous_span
    intro g hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    exact ⟨d, (multivariateHomogenization_isHomogeneous f d).map (algebraMap K L)⟩
  have hdehom : multivariateDehomogenization
      (map (algebraMap K L) (multivariateHomogenization f d)) =
        map (algebraMap K L) f := by
    have h := DFunLike.congr_fun
      (multivariateDehomogenization_comp_map (σ := Fin n) (algebraMap K L))
      (multivariateHomogenization f d)
    change multivariateDehomogenization
      (map (algebraMap K L) (multivariateHomogenization f d)) =
        map (algebraMap K L) (multivariateDehomogenization (multivariateHomogenization f d)) at h
    rw [multivariateDehomogenization_homogenization f d hfd.le] at h
    exact h
  have hJmap : J.map multivariateDehomogenization.toRingHom =
      Ideal.span {map (algebraMap K L) f} := by
    simp only [J, Ideal.map_span, Set.image_singleton, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, hdehom]
  have hdegree : (map (algebraMap K L) f).totalDegree = d := by
    simpa only [totalDegree, support_map_of_injective f (algebraMap K L).injective] using hfd
  have hunit : ¬ IsUnit (map (algebraMap K L) f) := by
    intro h
    have hzero := (isUnit_iff_totalDegree_of_isReduced.mp h).2
    omega
  have hX : X (none : Option (Fin n)) ∉ J := by
    intro h
    have hone : (1 : MvPolynomial (Fin n) L) ∈ J.map multivariateDehomogenization.toRingHom := by
      simpa using Ideal.mem_map_of_mem multivariateDehomogenization.toRingHom h
    rw [hJmap, Ideal.mem_span_singleton] at hone
    exact hunit (isUnit_of_dvd_one hone)
  rw [← hJmap]
  exact map_multivariateDehomogenization_isPrime J hhom hprime hX

/-- The literal former literature premise, now proved from the smooth
rational point on the integral homogenized hypersurface. -/
theorem proved : Literature.SmoothInfinityGeometricIntegrality := by
  intro K _ n d f hd hfd hdom hpoint
  obtain ⟨x, _hx, hxzero, i, hi⟩ := hpoint
  have hprime : (Ideal.span {f}).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp hdom
  have hhomprime := PrimeMultivariateHomogenization.isPrime f d hfd hprime
  have hpL := coefficientExtension_isPrime_of_partial_finite
    (L := AlgebraicClosure K) (multivariateHomogenization f d) hhomprime
    (infinityPoint x)
    (by rw [eval_homogenization_infinity]; exact hxzero)
    (some i) (by rw [eval_pderiv_homogenization_infinity]; exact hi)
  exact (Ideal.Quotient.isDomain_iff_prime _).mpr
    (coefficientExtension_isPrime_of_homogenization f hfd hd hpL)

end CubicTenVariables.SmoothInfinityGeometricIntegralityProved
