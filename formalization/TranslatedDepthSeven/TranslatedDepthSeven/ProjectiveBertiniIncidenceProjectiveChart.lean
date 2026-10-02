import TranslatedDepthSeven.HomogeneousChartPolynomialEmbedding
import TranslatedDepthSeven.ProjectiveBertiniIncidenceProjectiveSaturation

namespace TranslatedDepthSeven

noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

theorem bertini_homogeneous_dehomogenization_mem_clears_coordinate
    {K : Type*} [Field K] {n k : ℕ}
    (I : Ideal (MvPolynomial (Option (Fin n)) K))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Option (Fin n)) K))
    (f : MvPolynomial (Option (Fin n)) K) (hf : f.IsHomogeneous k)
    (hmem : multivariateDehomogenization f ∈ I.map multivariateDehomogenization.toRingHom) :
    ∃ m : ℕ, X (none : Option (Fin n)) ^ m * f ∈ I := by
  obtain ⟨D, g, hg, hgI, hgf⟩ :=
    exists_homogeneous_preimage_mem_of_mem_map_dehomogenization I hI hmem
  have hfRec := multivariateHomogenization_dehomogenization_of_isHomogeneous f hf
  have hgRec := multivariateHomogenization_dehomogenization_of_isHomogeneous g hg
  have heq : X (none : Option (Fin n)) ^ (max k D - k) * f =
      X (none : Option (Fin n)) ^ (max k D - D) * g := by
    calc
      _ = multivariateHomogenization (multivariateDehomogenization f) (max k D) := by
        rw [multivariateHomogenization_raise_degree
          (multivariateDehomogenization f) hfRec.1 (le_max_left k D), hfRec.2]
      _ = X (none : Option (Fin n)) ^ (max k D - D) * g := by
        rw [← hgf, multivariateHomogenization_raise_degree
          (multivariateDehomogenization g) hgRec.1 (le_max_right k D), hgRec.2]
  exact ⟨max k D - k, heq ▸ I.mul_mem_left _ hgI⟩

/-- A prime dehomogenized ideal has a prime homogeneous closure, and the
closure differs from the original homogeneous ideal only by powers of the
homogenizing coordinate. No primeness of the original ideal is required. -/
theorem bertini_exists_prime_homogeneous_chart_saturation
    {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Option (Fin n)) K))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Option (Fin n)) K))
    (hchart : (I.map multivariateDehomogenization.toRingHom).IsPrime) :
    ∃ J : Ideal (MvPolynomial (Option (Fin n)) K),
      J.IsPrime ∧ J.IsHomogeneous (homogeneousSubmodule (Option (Fin n)) K) ∧
      I ≤ J ∧ X (none : Option (Fin n)) ∉ J ∧
      ∀ f ∈ J, ∃ m : ℕ, X (none : Option (Fin n)) ^ m * f ∈ I := by
  classical
  letI := hchart
  let D := optionChartQuotientEvaluation I
  let H := homogeneousScalingHom D
  let J := RingHom.ker H.toRingHom
  have hJI : I ≤ J := by
    intro f hf
    change H f = 0
    apply Polynomial.ext
    intro k
    rw [homogeneousScalingHom_coeff, Polynomial.coeff_zero]
    have hk : homogeneousComponent k f ∈ I := by
      have hh := hI k hf
      change (MvPolynomial.decomposition.decompose' f k :
        MvPolynomial (Option (Fin n)) K) ∈ I at hh
      simpa only [MvPolynomial.decomposition.decompose'_apply] using hh
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_map_of_mem multivariateDehomogenization.toRingHom hk)
  have hJhom : J.IsHomogeneous (homogeneousSubmodule (Option (Fin n)) K) := by
    intro k f hf
    change (MvPolynomial.decomposition.decompose' f k :
      MvPolynomial (Option (Fin n)) K) ∈ J
    rw [MvPolynomial.decomposition.decompose'_apply]
    change H (homogeneousComponent k f) = 0
    have hcoef := congrArg (fun p ↦ Polynomial.coeff p k) hf
    change (H f).coeff k = (0 : Polynomial _).coeff k at hcoef
    rw [homogeneousScalingHom_coeff, Polynomial.coeff_zero] at hcoef
    rw [homogeneousScalingHom_apply_of_isHomogeneous D _
      (homogeneousComponent_isHomogeneous k f), hcoef, Polynomial.C_0, zero_mul]
  have hX : X (none : Option (Fin n)) ∉ J := by
    intro h
    have hval : H (X (none : Option (Fin n))) = Polynomial.X := by
      simp [H, homogeneousScalingHom, D, optionChartQuotientEvaluation,
        multivariateDehomogenization_X_none]
    exact Polynomial.X_ne_zero (hval.symm.trans h)
  refine ⟨J, RingHom.ker_isPrime H.toRingHom, hJhom, hJI, hX, ?_⟩
  intro f hf
  let Q := MvPolynomial (Option (Fin n)) K ⧸ I
  let a : Q := Ideal.Quotient.mk I (X none)
  let φ : MvPolynomial (Option (Fin n)) K →+* Localization.Away a :=
    (algebraMap Q (Localization.Away a)).comp (Ideal.Quotient.mk I)
  have hzero : φ f = 0 := by
    rw [← f.sum_homogeneousComponent, map_sum]
    apply Finset.sum_eq_zero
    intro k hk
    have hcoef := congrArg (fun p ↦ Polynomial.coeff p k) hf
    change (H f).coeff k = (0 : Polynomial _).coeff k at hcoef
    rw [homogeneousScalingHom_coeff, Polynomial.coeff_zero] at hcoef
    have hmem : multivariateDehomogenization (homogeneousComponent k f) ∈
        I.map multivariateDehomogenization.toRingHom :=
      Ideal.Quotient.eq_zero_iff_mem.mp hcoef
    obtain ⟨m, hm⟩ := bertini_homogeneous_dehomogenization_mem_clears_coordinate
      I hI (homogeneousComponent k f) (homogeneousComponent_isHomogeneous k f) hmem
    change algebraMap Q (Localization.Away a) (Ideal.Quotient.mk I (homogeneousComponent k f)) = 0
    apply (IsLocalization.map_eq_zero_iff (Submonoid.powers a) (Localization.Away a) _).mpr
    refine ⟨⟨a ^ m, ⟨m, rfl⟩⟩, ?_⟩
    simpa only [a, map_mul, map_pow] using Ideal.Quotient.eq_zero_iff_mem.mpr hm
  obtain ⟨⟨_, m, rfl⟩, hm⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers a) (Localization.Away a)
      (Ideal.Quotient.mk I f)).mp hzero
  refine ⟨m, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  simpa only [map_mul, map_pow] using hm

end
end TranslatedDepthSeven
