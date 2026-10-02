import TranslatedDepthSeven.ProjectiveConeSectionInternal
import TranslatedDepthSeven.IsolatedVertexQuotientPersistentAggregate
import TranslatedDepthSeven.FiniteHomogeneousIdealGenerators
import TranslatedDepthSeven.PrimeProjectiveSaturation
import Mathlib.RingTheory.KrullDimension.Field

/-!
# Integral projective cone bases from Hilbert certification

This removes the separate cone-base geometry premise.  Homogeneity descends
by setting the added coordinate to zero, and primality contracts.  The base
cannot contain the irrelevant ideal: otherwise its quotient is a field,
and the cone has affine dimension one, whereas the source certificate gives
dimension at least two.  Prime saturation then applies to the base.

The only input is the already displayed projective Hilbert-degree theorem.
Its certificate on the base is identified by the internal forward-cone
theorem and uniqueness of dimension and degree.  In particular we do not use
the false assertion that saturation always contracts from a polynomial ring.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 400000

/-- Setting the cone coordinate to zero recovers the literal base ideal. -/
theorem map_projectiveConeFinIdeal_restrictFirst_zero
    (N : ℕ) (J : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) :
    (projectiveConeFinIdeal ℚ N J).map
      (MvPolynomial.aeval (Fin.cases 0 MvPolynomial.X)) = J := by
  unfold projectiveConeFinIdeal projectiveConeIdealExtension
  change Ideal.map
      (MvPolynomial.aeval (Fin.cases 0 MvPolynomial.X) :
        MvPolynomial (Fin ((N + 1) + 1)) ℚ →ₐ[ℚ]
          MvPolynomial (Fin (N + 1)) ℚ).toRingHom
      (Ideal.map
        (MvPolynomial.renameEquiv ℚ (_root_.finSuccEquiv (N + 1)).symm).toRingEquiv.toRingHom
        (Ideal.map (MvPolynomial.rename some).toRingHom J)) = J
  rw [Ideal.map_map, Ideal.map_map]
  have hcomp :
      ((MvPolynomial.aeval (Fin.cases 0 MvPolynomial.X) :
          MvPolynomial (Fin ((N + 1) + 1)) ℚ →ₐ[ℚ]
            MvPolynomial (Fin (N + 1)) ℚ).toRingHom.comp
        (MvPolynomial.renameEquiv ℚ (_root_.finSuccEquiv (N + 1)).symm).toRingEquiv.toRingHom).comp
          (MvPolynomial.rename some).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      simp
  rw [hcomp, Ideal.map_id]

/-- Homogeneity descends to the base by the zero-coordinate restriction. -/
theorem isHomogeneous_of_projectiveConeFinIdeal
    (N : ℕ) (J : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hcone : (projectiveConeFinIdeal ℚ N J).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin ((N + 1) + 1)) ℚ)) :
    J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) := by
  obtain ⟨M, f, degree, hfHom, hfSpan⟩ :=
    exists_fin_homogeneous_generating_family _ hcone
  rw [← map_projectiveConeFinIdeal_restrictFirst_zero N J, ← hfSpan,
    Ideal.map_span]
  apply Ideal.homogeneous_span
  rintro g ⟨_, ⟨i, rfl⟩, rfl⟩
  exact ⟨degree i, restrictFirstPolynomialToZero_isHomogeneous (hfHom i)⟩

/-- The homogeneous coordinate ideal is the kernel of the constant term. -/
theorem projectiveIrrelevantIdeal_eq_ker_constantCoeff
    (N : ℕ) :
    projectiveIrrelevantIdeal ℚ N =
      RingHom.ker (MvPolynomial.constantCoeff (σ := Fin (N + 1)) (R := ℚ)) := by
  rw [projectiveIrrelevantIdeal, ← mvPolynomialIrrelevantIdeal_eq_span_X]
  ext f
  change f ∈ HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) ↔
    MvPolynomial.constantCoeff f = 0
  rw [HomogeneousIdeal.mem_irrelevant_iff]
  change GradedRing.projZeroRingHom
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) f = 0 ↔
    MvPolynomial.constantCoeff f = 0
  rw [projZeroRingHom_homogeneousSubmodule_apply, MvPolynomial.C_eq_zero]

/-- A proper prime containing all coordinates has zero-dimensional affine
quotient.  This applies to the irrelevant prime, including a one-variable
homogeneous ring. -/
theorem ringKrullDim_quotient_eq_zero_of_irrelevant_le
    (N : ℕ) (J : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hprime : J.IsPrime) (hirr : projectiveIrrelevantIdeal ℚ N ≤ J) :
    ringKrullDim (MvPolynomial (Fin (N + 1)) ℚ ⧸ J) = 0 := by
  have hmax : (projectiveIrrelevantIdeal ℚ N).IsMaximal := by
    rw [projectiveIrrelevantIdeal_eq_ker_constantCoeff]
    apply RingHom.ker_isMaximal_of_surjective
    intro a
    exact ⟨MvPolynomial.C a, by simp⟩
  have hJ : projectiveIrrelevantIdeal ℚ N = J :=
    hmax.eq_of_le hprime.ne_top hirr
  letI : J.IsMaximal := hJ ▸ hmax
  letI := Ideal.Quotient.field J
  exact ringKrullDim_eq_zero_of_field _

/-- A projective cone of positive projective dimension has a nonempty
projective base.  The explicit dimension hypothesis is essential here. -/
theorem projectiveCone_base_irrelevant_not_le
    (N r d : ℕ) (J : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hprime : J.IsPrime)
    (hcone : HasProjectiveDimensionDegree
      (projectiveConeFinIdeal ℚ N J) (r + 1) d) :
    ¬ projectiveIrrelevantIdeal ℚ N ≤ J := by
  intro hirr
  have hzero := ringKrullDim_quotient_eq_zero_of_irrelevant_le N J hprime hirr
  have hoption : ringKrullDim
      (MvPolynomial (Option (Fin (N + 1))) ℚ ⧸ projectiveConeIdealExtension J) =
        (1 : WithBot ℕ∞) := by
    simpa using ringKrullDim_projectiveConeIdealExtension_eq_succ
      ℚ J hprime (r := 0) (by simpa using hzero)
  have hrename := ringKrullDim_eq_of_ringEquiv
    (renameQuotientAlgEquiv ℚ (_root_.finSuccEquiv (N + 1)).symm
      (projectiveConeIdealExtension J)).toRingEquiv
  have hdim : (((r + 1) + 1 : ℕ) : WithBot ℕ∞) = 1 := by
    simpa using hcone.1.symm.trans (hrename.symm.trans hoption)
  have hnat : (r + 1) + 1 = 1 := by exact_mod_cast hdim
  omega

/-- Cone-base geometry is a consequence of the already available
projective Hilbert-degree certification; it is not a separate AG premise. -/
theorem integralProjectiveConeBaseGeometryDescent_of_projectiveHilbertDegreeCertification
    (hHilbert : StandardAG.ProjectiveHilbertDegreeCertification ℚ) :
    StandardAG.IntegralProjectiveConeBaseGeometryDescent := by
  intro N r d J hcone
  have hprime : J.IsPrime :=
    (projectiveConeFinIdeal_isPrime_iff ℚ N J).mp hcone.2.2.1
  have hhom := isHomogeneous_of_projectiveConeFinIdeal N J hcone.1
  have hirr := projectiveCone_base_irrelevant_not_le N r d J hprime hcone.2.2.2
  obtain ⟨s, e, P, hP⟩ := hHilbert N J hprime hhom hirr
  have hbase := hP.toPublished
  have hforward := hasProjectiveDimensionDegree_projectiveConeFinIdeal
    ℚ N s e J hhom hprime hbase
  have hs : s = r := by
    have hdim := hforward.1.symm.trans hcone.2.2.2.1
    have hnat : (s + 1) + 1 = (r + 1) + 1 := by exact_mod_cast hdim
    omega
  subst s
  have he : e = d :=
    projectiveDegree_eq_of_hasProjectiveDimensionDegree hforward hcone.2.2.2
  subst e
  exact ⟨hhom, prime_isSaturatedByProjectiveIrrelevantIdeal hprime hirr,
    hprime, hbase⟩

end

end TranslatedDepthSeven
