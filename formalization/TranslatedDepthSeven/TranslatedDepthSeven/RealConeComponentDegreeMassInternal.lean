import TranslatedDepthSeven.RealCoefficientMinimalComponentDimensionInternal
import TranslatedDepthSeven.ProjectiveHilbertDegreeCertificationInternal
import TranslatedDepthSeven.HomogeneousComponentDegreeMassInternal
import TranslatedDepthSeven.RankSevenDegreeOneSmoothStarCounting
import TranslatedDepthSeven.CoefficientExtensionHomogeneousIdeal

/-!
# Real components of an integral rational projective cone

Finite normalization and torsion-free base change show that every actual
real minimal component has the original affine cone dimension. Internal
Hilbert certification supplies its degree. The Hilbert function is
unchanged by coefficient extension, and the checked top-dimensional
component inequality bounds the sum of reduced component degrees.

The statement needs an upper bound for this sum, not equality. Therefore
neither geometric reducedness nor a Galois description of the components
is needed in this proof.
-/

namespace TranslatedDepthSeven

noncomputable section
open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

theorem homogeneousPrimeRealConeComponentDegreeMass_internal :
    StandardAG.HomogeneousPrimeRealConeComponentDegreeMass := by
  classical
  intro N r d I hIprime hIhom hIdegree
  let J := realCoefficientExtensionOfRationalIdeal I
  have hJhom : J.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℝ) :=
    isHomogeneous_map_mvPolynomialMap (algebraMap ℚ ℝ) I hIhom
  obtain ⟨D⟩ := exists_homogeneousLinearNormalizationData (N + 1) I hIprime hIhom
  have hcomponent : ∀ P ∈ finiteMinimalPrimes J,
      ∃ e : ℕ, HasProjectiveDimensionDegree P r e := by
    intro P hP
    have hpmin := (mem_finiteMinimalPrimes_iff _ _).mp hP
    have hprime : P.IsPrime := hpmin.1.1
    have hhom := isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous hJhom hpmin
    have hdim : ringKrullDim (MvPolynomial (Fin (N + 1)) ℝ ⧸ P) =
        (r : WithBot ℕ∞) + 1 :=
      (realCoefficient_minimalComponent_dimension_eq_source I hIprime D P hpmin).trans
        hIdegree.1
    have hirr : ¬ projectiveIrrelevantIdeal ℝ N ≤ P := by
      intro hle
      have hzero := ringKrullDim_quotient_eq_zero_of_irrelevant_le_over_field N P hprime hle
      have hpos : (0 : WithBot ℕ∞) < (r : WithBot ℕ∞) + 1 := by
        exact_mod_cast Nat.succ_pos r
      rw [← hdim, hzero] at hpos
      exact lt_irrefl _ hpos
    obtain ⟨s, e, Q, hQ⟩ := projectiveHilbertDegreeCertification_internal ℝ
      N P hprime hhom hirr
    have hsr : s = r := by
      have heq : (s : WithBot ℕ∞) + 1 = (r : WithBot ℕ∞) + 1 := hQ.1.symm.trans hdim
      have hn : s + 1 = r + 1 := by exact_mod_cast heq
      omega
    subst s
    exact ⟨e, hQ.toPublished⟩
  have hchoose : ∀ P : Ideal (MvPolynomial (Fin (N + 1)) ℝ),
      ∃ e : ℕ, P ∈ finiteMinimalPrimes J → HasProjectiveDimensionDegree P r e := by
    intro P
    by_cases hP : P ∈ finiteMinimalPrimes J
    · obtain ⟨e, he⟩ := hcomponent P hP
      exact ⟨e, fun _ ↦ he⟩
    · exact ⟨0, fun h ↦ False.elim (hP h)⟩
  choose componentDegree hdegree using hchoose
  refine ⟨componentDegree, ?_, ?_⟩
  · intro P hP
    have hpmin := (mem_finiteMinimalPrimes_iff _ _).mp hP
    have hhom := isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous hJhom hpmin
    exact ⟨(hdegree P hP).2.1,
      hasAffineDimensionDegree_of_homogeneous_hasProjectiveDimensionDegree
        P hhom hpmin.1.1 r (componentDegree P) (hdegree P hP)⟩
  · let ι := ↥(finiteMinimalPrimes J)
    have hmass := sum_projectiveDegrees_le_of_distinct_prime_components J
      (fun P : ι ↦ P.1) (fun P : ι ↦ componentDegree P.1)
      Subtype.val_injective
      (fun P ↦ ((mem_finiteMinimalPrimes_iff _ _).mp P.2).1.1)
      (fun P ↦ isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous hJhom
        ((mem_finiteMinimalPrimes_iff _ _).mp P.2))
      (fun P ↦ hdegree P.1 P.2)
      (fun P ↦ ((mem_finiteMinimalPrimes_iff _ _).mp P.2).1.2)
      (real_hasProjectiveHilbertDimensionDegree_of_rational I hIdegree)
    change (∑ P : ↥(finiteMinimalPrimes J), componentDegree P.1) ≤ d at hmass
    rw [Finset.sum_coe_sort] at hmass
    exact hmass

end
end TranslatedDepthSeven
