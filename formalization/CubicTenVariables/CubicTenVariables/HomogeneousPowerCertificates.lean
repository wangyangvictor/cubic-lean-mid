import TranslatedDepthSeven.HomogeneousLinearElimination

/-!
# Coordinate powers after cutting a homogeneous normalization

Setting the linear normalization parameters to zero leaves a finite-dimensional
homogeneous quotient. Its coordinate classes are nilpotent, so powers of the
original coordinates lie in the cut ideal. These are fixed certificates before
any lower-degree perturbation of the equations is chosen.
-/

noncomputable section
namespace CubicTenVariables.HomogeneousPowerCertificates

open MvPolynomial TranslatedDepthSeven
attribute [local instance] MvPolynomial.gradedAlgebra

universe u v
variable {K : Type u} [Field K] {σ : Type v}

/-- The zero fibre of the actual linear normalization forms. -/
def cutIdeal (I : Ideal (MvPolynomial σ K))
    (D : HomogeneousLinearNormalizationData I) : Ideal (MvPolynomial σ K) :=
  I ⊔ Ideal.span (Set.range D.forms)

theorem cutIdeal_isHomogeneous (I : Ideal (MvPolynomial σ K))
    (D : HomogeneousLinearNormalizationData I)
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) :
    (cutIdeal I D).IsHomogeneous (homogeneousSubmodule σ K) := by
  apply hI.sup
  apply Ideal.homogeneous_span
  rintro _ ⟨i, rfl⟩
  exact ⟨1, D.forms_isHomogeneous i⟩

theorem finite_cut_quotient (I : Ideal (MvPolynomial σ K))
    (D : HomogeneousLinearNormalizationData I) :
    Module.Finite K (MvPolynomial σ K ⧸ cutIdeal I D) := by
  let J := cutIdeal I D
  have hIJ : I ≤ J := le_sup_left
  let q := Ideal.Quotient.factorₐ K hIJ
  have hq : q.Finite :=
    AlgHom.Finite.of_surjective q (Ideal.Quotient.factor_surjective hIJ)
  have hcomp : q.comp D.hom =
      (Algebra.ofId K (MvPolynomial σ K ⧸ J)).comp
        (MvPolynomial.aeval (fun _ : Fin D.parameterCount => (0 : K))) := by
    apply MvPolynomial.algHom_ext
    intro i
    have hmem : D.forms i ∈ J :=
      (show Ideal.span (Set.range D.forms) ≤ J from le_sup_right)
        (Ideal.subset_span (Set.mem_range_self i))
    simpa [q, HomogeneousLinearNormalizationData.hom] using
      (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  have hfinite := hq.comp D.hom_finite
  rw [hcomp] at hfinite
  have hbase := AlgHom.Finite.of_comp_finite hfinite
  change (algebraMap K (MvPolynomial σ K ⧸ J)).Finite at hbase
  exact RingHom.finite_algebraMap.mp hbase

theorem homogeneousComponent_eval_X_monic (i : σ) (p : Polynomial K)
    (hp : p.Monic) :
    homogeneousComponent p.natDegree (p.eval₂ C (X i)) = (X i) ^ p.natDegree := by
  classical
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum]
  rw [map_sum]
  have hpow (k : ℕ) :
      homogeneousComponent p.natDegree ((X i : MvPolynomial σ K) ^ k) =
        if p.natDegree = k then X i ^ k else 0 := by
    apply homogeneousComponent_of_mem
    simpa using (isHomogeneous_X K i).pow k
  simp_rw [homogeneousComponent_C_mul, hpow]
  rw [Finset.sum_eq_single p.natDegree]
  · simp [hp.coeff_natDegree]
  · intro b hb hne
    simp [Ne.symm hne]
  · intro hnot
    have hcoeff : p.coeff p.natDegree = 0 := Polynomial.notMem_support_iff.mp hnot
    rw [hp.coeff_natDegree] at hcoeff
    exact (one_ne_zero hcoeff).elim

/-- In a finite-dimensional homogeneous quotient, some positive power of
each original coordinate vanishes. Properness is unnecessary. -/
theorem exists_coordinate_power_mem (J : Ideal (MvPolynomial σ K))
    (hJ : J.IsHomogeneous (homogeneousSubmodule σ K))
    [Module.Finite K (MvPolynomial σ K ⧸ J)] (i : σ) :
    ∃ d : ℕ, 0 < d ∧ (X i : MvPolynomial σ K) ^ d ∈ J := by
  letI : Algebra.IsIntegral K (MvPolynomial σ K ⧸ J) :=
    Algebra.IsIntegral.of_finite K (MvPolynomial σ K ⧸ J)
  obtain ⟨p, hp, hz⟩ := Algebra.IsIntegral.isIntegral
    (R := K) (Ideal.Quotient.mk J (X i))
  have hmem : p.eval₂ C (X i) ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa using (Polynomial.hom_eval₂ p C (Ideal.Quotient.mk J) (X i)).trans hz
  have htop := hJ p.natDegree hmem
  change (MvPolynomial.decomposition.decompose' (p.eval₂ C (X i))
    p.natDegree : MvPolynomial σ K) ∈ J at htop
  rw [MvPolynomial.decomposition.decompose'_apply,
    homogeneousComponent_eval_X_monic i p hp] at htop
  refine ⟨p.natDegree + 1, Nat.succ_pos _, ?_⟩
  rw [pow_succ]
  exact J.mul_mem_right _ htop

/-- Fixed positive coordinate powers in the zero fibre of any finite linear
normalization of a homogeneous ideal. -/
theorem exists_cut_coordinate_powers (I : Ideal (MvPolynomial σ K))
    (D : HomogeneousLinearNormalizationData I)
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) :
    ∃ d : σ → ℕ, (∀ i, 0 < d i) ∧
      ∀ i, (X i : MvPolynomial σ K) ^ d i ∈ cutIdeal I D := by
  letI := finite_cut_quotient I D
  have h := exists_coordinate_power_mem (cutIdeal I D) (cutIdeal_isHomogeneous I D hI)
  choose d hd hmem using h
  exact ⟨d, hd, hmem⟩

end CubicTenVariables.HomogeneousPowerCertificates
