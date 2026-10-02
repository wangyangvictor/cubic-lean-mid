import TranslatedDepthSeven.ProperHomogeneousHypersurfaceComponentDegreeInternal
import TranslatedDepthSeven.RealAffineChartComponentTransferInternal
import TranslatedDepthSeven.IntegralProjectiveConeBaseGeometryInternal
import TranslatedDepthSeven.ProjectiveSurfaceAffineHypersurfaceBezout
import TranslatedDepthSeven.HilbertAffineChange

/-!
# Surface hypersurface sections, with the remaining dimension bound explicit

The only extra intermediate hypothesis is the literal lower bound two for
the affine dimensions of the rational minimal components. Strict prime
containment gives the upper bound, Hilbert certification supplies degrees,
and the internally proved hypersurface degree inequality and real-chart
transfer give the precise surface-section conclusion. This file does not
postulate a new geometric proposition or assume a component degree bound.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

/-- Rational minimal components of a proper homogeneous surface section
have projective dimension one and total degree at most the product, once
the explicit affine-dimension lower bound is supplied. -/
theorem projectiveSurface_section_rationalComponentDegreeMass_of_dimension_lower_bound
    (hHilbertQ : StandardAG.ProjectiveHilbertDegreeCertification ℚ)
    {N d a : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (G : MvPolynomial (Fin (N + 1)) ℚ)
    (hIprime : I.IsPrime)
    (hIhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hIprojective : HasProjectiveDimensionDegree I 2 d)
    (hGhom : G.IsHomogeneous a) (hGnot : G ∉ I)
    (hlower : ∀ P ∈ finiteMinimalPrimes (I ⊔ Ideal.span ({G} : Set _)),
      (2 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin (N + 1)) ℚ ⧸ P)) :
    ∃ degree : Ideal (MvPolynomial (Fin (N + 1)) ℚ) → ℕ,
      (∀ P ∈ finiteMinimalPrimes (I ⊔ Ideal.span ({G} : Set _)),
        HasProjectiveDimensionDegree P 1 (degree P)) ∧
      ∑ P ∈ finiteMinimalPrimes (I ⊔ Ideal.span ({G} : Set _)), degree P ≤ d * a := by
  classical
  let J := I ⊔ Ideal.span ({G} : Set _)
  have hGideal : (Ideal.span ({G} : Set _)).IsHomogeneous
      (homogeneousSubmodule (Fin (N + 1)) ℚ) := by
    apply Ideal.homogeneous_span
    intro f hf
    obtain rfl := Set.mem_singleton_iff.mp hf
    exact ⟨a, hGhom⟩
  have hJhom : J.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ) :=
    hIhom.sup hGideal
  have hPhom (P : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
      (hP : P ∈ finiteMinimalPrimes J) :
      P.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ) :=
    isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous hJhom
      ((mem_finiteMinimalPrimes_iff J P).mp hP)
  have hexists (P : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
      (hP : P ∈ finiteMinimalPrimes J) :
      ∃ e : ℕ, HasProjectiveDimensionDegree P 1 e := by
    have hPprime := isPrime_of_mem_finiteMinimalPrimes hP
    have hlowerP := hlower P hP
    have hirrelevant : ¬ projectiveIrrelevantIdeal ℚ N ≤ P := by
      intro hirr
      have hzero := ringKrullDim_quotient_eq_zero_of_irrelevant_le N P hPprime hirr
      rw [hzero] at hlowerP
      norm_num at hlowerP
    obtain ⟨r, e, HP, hcert⟩ := hHilbertQ N P hPprime (hPhom P hP) hirrelevant
    have hproj := hcert.toPublished
    have hJP : J ≤ P := le_of_mem_finiteMinimalPrimes hP
    have hGP : G ∈ P := hJP
      ((show Ideal.span ({G} : Set _) ≤ J from le_sup_right)
        (Ideal.subset_span (Set.mem_singleton G)))
    have hIP : I < P := lt_of_le_of_ne (le_sup_left.trans hJP) (by
      intro heq
      exact hGnot (heq.symm ▸ hGP))
    letI : I.IsPrime := hIprime
    letI : P.IsPrime := hPprime
    have hfinite : ringKrullDim (MvPolynomial (Fin (N + 1)) ℚ ⧸ I) < ⊤ := by
      rw [hIprojective.1]
      change (↑(3 : ℕ∞) : WithBot ℕ∞) < ↑(⊤ : ℕ∞)
      exact WithBot.coe_lt_coe.mpr (ENat.coe_lt_top 3)
    have hupperP := ringKrullDim_quotient_lt_of_prime_lt I P hIP hfinite
    rw [hproj.1, hIprojective.1] at hupperP
    rw [hproj.1] at hlowerP
    have hu : r + 1 < 3 := by exact_mod_cast hupperP
    have hl : 2 ≤ r + 1 := by exact_mod_cast hlowerP
    have hr : r = 1 := by omega
    exact ⟨e, hr ▸ hproj⟩
  have htotal (P : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) :
      ∃ e : ℕ, P ∈ finiteMinimalPrimes J → HasProjectiveDimensionDegree P 1 e := by
    by_cases hP : P ∈ finiteMinimalPrimes J
    · obtain ⟨e, he⟩ := hexists P hP
      exact ⟨e, fun _ ↦ he⟩
    · exact ⟨0, fun h ↦ False.elim (hP h)⟩
  choose degree hdegree using htotal
  refine ⟨degree, hdegree, ?_⟩
  have hmass := sum_projectiveDegrees_proper_homogeneous_hypersurface_le
    (r := 1) I hIprime hIprojective G hGhom hGnot
    (fun P : ↥(finiteMinimalPrimes J) ↦ P.1)
    (fun P : ↥(finiteMinimalPrimes J) ↦ degree P.1)
    Subtype.val_injective
    (fun P ↦ isPrime_of_mem_finiteMinimalPrimes P.2)
    (fun P ↦ hPhom P.1 P.2) (fun P ↦ hdegree P.1 P.2)
    (fun P ↦ le_of_mem_finiteMinimalPrimes P.2)
  simpa only [Finset.sum_coe_sort] using hmass

/-- The exact real affine-chart conclusion of the surface-hypersurface
Bezout input, with the remaining rational component-dimension lower bound
shown as an explicit intermediate hypothesis.

The degree-zero case needs no separate assumption: a nonzero homogeneous
constant makes the section ideal the whole ring, so all component clauses
are vacuous and the internally proved degree sum is zero. -/
theorem projectiveSurfaceAffineHypersurfaceBezout_of_component_dimension_lower_bound
    (hHilbertQ : StandardAG.ProjectiveHilbertDegreeCertification ℚ)
    (hRealMass : StandardAG.HomogeneousPrimeRealConeComponentDegreeMass)
    {N d a : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (G : MvPolynomial (Fin (N + 1)) ℚ)
    (hIprime : I.IsPrime)
    (hIhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hIprojective : HasProjectiveDimensionDegree I 2 d)
    (hGhom : G.IsHomogeneous a) (hGnot : G ∉ I)
    (hlower : ∀ P ∈ finiteMinimalPrimes (I ⊔ Ideal.span ({G} : Set _)),
      (2 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin (N + 1)) ℚ ⧸ P)) :
    ∃ componentDegree : Ideal (MvPolynomial (Fin N) ℝ) → ℕ,
      (∀ Q ∈ finiteMinimalPrimes (realAffineChartIntersectionIdeal I G),
        ∃ n : ℕ, n ≤ 1 ∧ 1 ≤ componentDegree Q ∧
          HasAffineHilbertDimensionDegree Q n (componentDegree Q)) ∧
      ∑ Q ∈ finiteMinimalPrimes (realAffineChartIntersectionIdeal I G),
        componentDegree Q ≤ d * a := by
  obtain ⟨degree, hdegree, hmass⟩ :=
    projectiveSurface_section_rationalComponentDegreeMass_of_dimension_lower_bound
      hHilbertQ I G hIprime hIhom hIprojective hGhom hGnot hlower
  let J := I ⊔ Ideal.span ({G} : Set _)
  have hJhom : J.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ) := by
    apply hIhom.sup
    apply Ideal.homogeneous_span
    intro f hf
    obtain rfl := Set.mem_singleton_iff.mp hf
    exact ⟨a, hGhom⟩
  have hcone (P : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
      (hP : P ∈ finiteMinimalPrimes J) : HasAffineDimensionDegree P 2 (degree P) := by
    exact hasAffineDimensionDegree_of_homogeneous_hasProjectiveDimensionDegree P
      (isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous hJhom
        ((mem_finiteMinimalPrimes_iff J P).mp hP))
      (isPrime_of_mem_finiteMinimalPrimes hP) 1 (degree P) (hdegree P hP)
  obtain ⟨cdim, cdeg, hc, hm⟩ :=
    realAffineChart_componentDimensionDegreeMass_le_of_rationalComponents
      hRealMass (r := 1) (D := d * a) J hJhom (fun _ ↦ 2) degree hcone
      (fun _ _ ↦ le_rfl) hmass
  refine ⟨cdeg, ?_, hm⟩
  intro Q hQ
  obtain ⟨hn, hQdegree⟩ := hc Q hQ
  exact ⟨cdim Q, hn, hQdegree.2.2.1, hQdegree.toHilbert⟩

end

end TranslatedDepthSeven
