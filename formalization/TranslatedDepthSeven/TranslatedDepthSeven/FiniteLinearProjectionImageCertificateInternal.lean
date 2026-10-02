import TranslatedDepthSeven.LinearProjectionImageDegreeInternal
import TranslatedDepthSeven.ProjectiveHilbertDegreeCertificationInternal

/-!
# Dimension and degree of a finite homogeneous linear image

The image is the quotient by the literal kernel. Finiteness and injectivity
of its map to the source preserve Krull dimension. The internal Hilbert
theorem supplies the image degree, and the homogeneous-piece injection
bounds it by the source degree. A retained nonzero linear coordinate
excludes the empty projective image.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

theorem kernel_homogeneousLinearCoordinateMap_isHomogeneous
    {K σ τ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K))
    (hIhom : I.IsHomogeneous (homogeneousSubmodule σ K))
    (forms : τ → MvPolynomial σ K)
    (hforms : ∀ i, (forms i).IsHomogeneous 1) :
    (RingHom.ker ((Ideal.Quotient.mkₐ K I).comp (aeval forms)).toRingHom).IsHomogeneous
      (homogeneousSubmodule τ K) := by
  intro k p hp
  rw [← DirectSum.Decomposition.decompose'_eq]
  rw [MvPolynomial.decomposition.decompose'_apply]
  rw [RingHom.mem_ker] at hp ⊢
  change Ideal.Quotient.mk I (aeval forms p) = 0 at hp
  change Ideal.Quotient.mk I (aeval forms (homogeneousComponent k p)) = 0
  have hcomponent := hIhom k (Ideal.Quotient.eq_zero_iff_mem.mp hp)
  rw [← DirectSum.Decomposition.decompose'_eq,
    MvPolynomial.decomposition.decompose'_apply] at hcomponent
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [← homogeneousComponent_aeval_degreeOne forms hforms p k]
  exact hcomponent

/-- A finite homogeneous linear image retaining one nonzero coordinate has
the source dimension and degree no larger than the source degree. All
dimension and Hilbert assertions are proved here, not supplied as inputs. -/
theorem finite_homogeneousLinearImage_exists_projectiveDimensionDegree_le
    {K : Type*} [Field K] [CharZero K] {N M r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hIprime : I.IsPrime)
    (hIhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K))
    (hsource : HasProjectiveDimensionDegree I r d)
    (forms : Fin (M + 1) → MvPolynomial (Fin (N + 1)) K)
    (hforms : ∀ i, (forms i).IsHomogeneous 1)
    (hfinite : ((Ideal.Quotient.mkₐ K I).comp (aeval forms)).Finite)
    (j : Fin (M + 1)) (hj : forms j ∉ I) :
    ∃ e : ℕ, e ≤ d ∧ HasProjectiveDimensionDegree
      (RingHom.ker ((Ideal.Quotient.mkₐ K I).comp (aeval forms)).toRingHom) r e := by
  letI : I.IsPrime := hIprime
  let h := (Ideal.Quotient.mkₐ K I).comp (aeval forms)
  let J := RingHom.ker h.toRingHom
  have hJprime : J.IsPrime := RingHom.ker_isPrime h
  letI : J.IsPrime := hJprime
  have hJhom : J.IsHomogeneous (homogeneousSubmodule (Fin (M + 1)) K) :=
    kernel_homogeneousLinearCoordinateMap_isHomogeneous I hIhom forms hforms
  have hJirr : ¬ projectiveIrrelevantIdeal K M ≤ J := by
    intro hle
    have hX : X j ∈ J := hle (Ideal.subset_span ⟨j, rfl⟩)
    apply hj
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hh := RingHom.mem_ker.mp hX
    change Ideal.Quotient.mk I (aeval forms (X j)) = 0 at hh
    rw [MvPolynomial.aeval_X] at hh
    exact hh
  obtain ⟨s, e, P, hP⟩ := projectiveHilbertDegreeCertification_internal K M J hJprime hJhom hJirr
  have hproj : HasProjectiveDimensionDegree J s e := hP.toPublished
  let A := MvPolynomial (Fin (N + 1)) K ⧸ I
  let B := MvPolynomial (Fin (M + 1)) K ⧸ J
  let q : B →ₐ[K] A := Ideal.kerLiftAlg h
  letI : Algebra B A := q.toRingHom.toAlgebra
  letI : FaithfulSMul B A :=
    (faithfulSMul_iff_algebraMap_injective B A).mpr (Ideal.kerLiftAlg_injective h)
  haveI : Module.Finite B A := kerLiftAlg_finite_of_finite h hfinite
  letI : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  have hdim : ringKrullDim B = ringKrullDim A :=
    ringKrullDim_eq_of_isIntegral_injective_parameterCount
  change ringKrullDim (MvPolynomial (Fin (M + 1)) K ⧸ J) =
    ringKrullDim (MvPolynomial (Fin (N + 1)) K ⧸ I) at hdim
  rw [hproj.1, hsource.1] at hdim
  have hs : s = r := by
    have hh : s + 1 = r + 1 := by exact_mod_cast hdim
    omega
  subst s
  exact ⟨e, projectiveDegree_homogeneousLinearImage_le I forms hforms hsource hproj, hproj⟩

end
end TranslatedDepthSeven
