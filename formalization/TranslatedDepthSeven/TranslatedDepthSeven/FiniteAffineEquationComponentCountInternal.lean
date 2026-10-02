import TranslatedDepthSeven.CanonicalHomogeneousComponentBezoutInternal
import TranslatedDepthSeven.ProjectiveAffineChartBridge
import TranslatedDepthSeven.RankSevenSourceSectionVertexInternal

/-!
# All affine components of arbitrary bounded-degree equations

Homogenization adds one variable. Every minimal prime of the affine chart
comes from a minimal homogeneous prime avoiding the first variable. The
dimension-weighted projective Bezout sum therefore bounds their number,
without any homogeneity assumption on the original affine equations.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 300000

theorem exists_minimalPrime_standardChart_eq
    {n : ℕ} (J : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
    (hJhom : J.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) ℚ))
    (P : Ideal (MvPolynomial (Fin n) ℚ))
    (hP : P ∈ finiteMinimalPrimes (J.map rationalDehomogenizeAtZeroHom)) :
    ∃ Q ∈ finiteMinimalPrimes J, X (0 : Fin (n + 1)) ∉ Q ∧
      Q.map rationalDehomogenizeAtZeroHom = P := by
  let f := @rationalDehomogenizeAtZeroHom n
  letI : P.IsPrime := isPrime_of_mem_finiteMinimalPrimes hP
  have hJpre : J ≤ P.comap f :=
    Ideal.map_le_iff_le_comap.mp (le_of_mem_finiteMinimalPrimes hP)
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le hJpre
  have hQhom := isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous hJhom hQ
  have hQprime := Ideal.minimalPrimes_isPrime hQ
  have hQX : X (0 : Fin (n + 1)) ∉ Q := by
    intro hx
    have hxP := hQP hx
    change f (X 0) ∈ P at hxP
    have hone : (1 : MvPolynomial (Fin n) ℚ) ∈ P := by
      simpa [f, rationalDehomogenizeAtZeroHom] using hxP
    exact (isPrime_of_mem_finiteMinimalPrimes hP).one_notMem hone
  refine ⟨Q, (mem_finiteMinimalPrimes_iff _ _).mpr hQ, hQX, ?_⟩
  have hmap_le : Q.map f ≤ P := Ideal.map_le_iff_le_comap.mpr hQP
  have hmapprime := rationalStandardAffineChart_isPrime Q hQhom hQprime hQX
  have hPmin := (mem_finiteMinimalPrimes_iff _ _).mp hP
  exact le_antisymm hmap_le (hPmin.2
    ⟨hmapprime, Ideal.map_mono hQ.1.2⟩ hmap_le)

theorem standardChart_component_card_le_projectiveWeight_sum
    {n B : ℕ} (hB : 1 ≤ B)
    (J : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
    (hJhom : J.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) ℚ)) :
    (finiteMinimalPrimes (J.map rationalDehomogenizeAtZeroHom)).card ≤
      ∑ Q ∈ finiteMinimalPrimes J, projectiveDimensionDegreeWeight B Q := by
  classical
  let S := (finiteMinimalPrimes J).filter (fun Q ↦ X (0 : Fin (n + 1)) ∉ Q)
  have hsub : finiteMinimalPrimes (J.map rationalDehomogenizeAtZeroHom) ⊆
      S.image (fun Q ↦ Q.map rationalDehomogenizeAtZeroHom) := by
    intro P hP
    obtain ⟨Q, hQ, hQX, hQP⟩ := exists_minimalPrime_standardChart_eq J hJhom P hP
    exact Finset.mem_image.mpr ⟨Q, Finset.mem_filter.mpr ⟨hQ, hQX⟩, hQP⟩
  have hpositive (Q) (hQ : Q ∈ S) : 1 ≤ projectiveDimensionDegreeWeight B Q := by
    obtain ⟨hQmin, hQX⟩ := Finset.mem_filter.mp hQ
    have hQhom := isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous hJhom
      ((mem_finiteMinimalPrimes_iff _ _).mp hQmin)
    have hirr : ¬ projectiveIrrelevantIdeal ℚ n ≤ Q := by
      intro h
      exact hQX (h (Ideal.subset_span ⟨0, rfl⟩))
    obtain ⟨r, d, HP, hc⟩ := projectiveHilbertDegreeCertification_internal ℚ
      n Q (isPrime_of_mem_finiteMinimalPrimes hQmin) hQhom hirr
    rw [projectiveDimensionDegreeWeight_eq hc.toPublished]
    have hdpos := hc.toPublished.2.1
    exact Nat.mul_le_mul (by omega : 1 ≤ d) (Nat.one_le_pow _ _ hB)
  calc
    _ ≤ (S.image (fun Q ↦ Q.map rationalDehomogenizeAtZeroHom)).card :=
      Finset.card_le_card hsub
    _ ≤ S.card := Finset.card_image_le
    _ = ∑ Q ∈ S, 1 := by simp
    _ ≤ ∑ Q ∈ S, projectiveDimensionDegreeWeight B Q := Finset.sum_le_sum hpositive
    _ ≤ ∑ Q ∈ finiteMinimalPrimes J, projectiveDimensionDegreeWeight B Q :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ ↦ Nat.zero_le _)

theorem finiteAffineEquation_component_card_le
    {n B : ℕ} (hB : 1 ≤ B)
    (family : Finset (MvPolynomial (Fin n) ℚ))
    (hdegree : ∀ f ∈ family, f.totalDegree ≤ B) :
    (finiteMinimalPrimes (finiteEquationIdeal family)).card ≤ B ^ n := by
  classical
  let H := (finiteFamilyHomogenization family B).image
    (MvPolynomial.rename (_root_.finSuccEquiv n).symm)
  have hH : ∀ f ∈ H, f.IsHomogeneous B := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
    exact (finiteFamilyHomogenization_isHomogeneous family B hg).rename_isHomogeneous
  have hJhom : (finiteEquationIdeal H).IsHomogeneous
      (homogeneousSubmodule (Fin (n + 1)) ℚ) := by
    apply Ideal.homogeneous_span
    intro f hf
    exact ⟨B, hH f hf⟩
  have hchart : (finiteEquationIdeal H).map rationalDehomogenizeAtZeroHom =
      finiteEquationIdeal family := by
    rw [← map_dehomogenization_map_finSuccRename]
    change ((finiteEquationIdeal ((finiteFamilyHomogenization family B).image
      (MvPolynomial.rename (_root_.finSuccEquiv n).symm))).map
        (MvPolynomial.renameEquiv ℚ (_root_.finSuccEquiv n))).map
      multivariateDehomogenization.toRingHom = _
    rw [map_finiteEquationIdeal_image_finSuccRename_back,
      map_finiteEquationIdeal_homogenization_eq family B hdegree]
  rw [← hchart]
  exact (standardChart_component_card_le_projectiveWeight_sum hB _ hJhom).trans
    (finiteHomogeneousEquation_projectiveWeight_sum_le hB H
      (fun f hf ↦ ⟨B, le_rfl, hH f hf⟩))

end
end TranslatedDepthSeven
