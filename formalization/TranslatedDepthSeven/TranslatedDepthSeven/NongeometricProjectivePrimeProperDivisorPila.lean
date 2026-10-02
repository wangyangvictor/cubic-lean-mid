import TranslatedDepthSeven.NongeometricRationalPointsProperDivisorInternal
import TranslatedDepthSeven.ProperHomogeneousHypersurfaceCertificatesInternal
import TranslatedDepthSeven.RealConeComponentTransferInternal
import TranslatedDepthSeven.RealConeComponentDegreeMassInternal
import TranslatedDepthSeven.ProjectiveFourfoldHyperplanePila

/-!
# Uniform Pila bounds for nongeometrically integral rational primes

Only projective dimension four needs a proper section: in dimension at most
three, the source affine cone already has dimension at most four. In the
four-dimensional case, one bounded-degree homogeneous Jacobian minor contains
all rational points and is nonzero on the source prime. The internally proved
hypersurface degree inequality and real coefficient-extension theorem then
give a finite component cover of bounded total degree.

No Galois frontier, coefficient height, or component-count premise is used.
The zero-dimensional case is covered on the source cone, not by applying a
positive-dimensional hypersurface theorem to a projective zero-fold.
-/

namespace TranslatedDepthSeven

noncomputable section
open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000

/-- Pila on a literal real minimal-component cover with total degree bounded
before the ideal and affine packet are chosen. -/
theorem exists_uniform_realComponentDegreeMass_fourthPower_pilaBound
    (hPila : Pila1995TheoremA) (N E : ℕ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (J : Ideal (MvPolynomial (Fin N) ℚ))
        (dim deg : Ideal (MvPolynomial (Fin N) ℝ) → ℕ),
        (∀ R ∈ finiteMinimalPrimes (J.map (MvPolynomial.map (algebraMap ℚ ℝ))),
          dim R ≤ 4 ∧ 1 ≤ deg R ∧ HasAffineHilbertDimensionDegree R (dim R) (deg R)) →
        (∑ R ∈ finiteMinimalPrimes (J.map (MvPolynomial.map (algebraMap ℚ ℝ))),
          deg R) ≤ E →
        ∀ (m M : ℕ), 0 < m → 1 ≤ M →
        ∀ (x0 : IntVector N) (points : Finset (IntVector N)),
          (∀ z ∈ points, ∀ i, (z i).natAbs ≤ M) →
          (∀ z ∈ points, (fun i ↦ (integralAffineMap x0 z m i : ℚ)) ∈
            affineIdealZeroLocus J) →
          (points.card : ℝ) ≤ C * ((M : ℝ) + 1) ^ ((4 : ℝ) + epsilon) := by
  classical
  obtain ⟨CP, hCP, hPilaBound⟩ :=
    pila1995_hilbertDimensionAtMost_boundedDegree hPila N 4 E epsilon hepsilon
  let C : ℝ := (max 1 E : ℕ) * CP
  refine ⟨C, mul_pos (by positivity) hCP, ?_⟩
  intro J dim deg hcomponents hmass m M hm hM x0 points hbox hzero
  let components := finiteMinimalPrimes (J.map (MvPolynomial.map (algebraMap ℚ ℝ)))
  let componentPoints := fun R : Ideal (MvPolynomial (Fin N) ℝ) ↦
    points.filter fun z ↦ (fun i ↦ (integralAffineMap x0 z m i : ℝ)) ∈
      affineIdealZeroLocus R
  have hcover : points ⊆ components.biUnion componentPoints := by
    intro z hz
    obtain ⟨R, hR, hxR⟩ := exists_realMinimalComponent_through_rationalPoint_of_ideal
      J (fun i ↦ (integralAffineMap x0 z m i : ℚ)) (hzero z hz)
    exact Finset.mem_biUnion.mpr ⟨R, hR, Finset.mem_filter.mpr ⟨hz, by
      simpa using hxR⟩⟩
  have hB : (1 : ℝ) < (M : ℝ) + 1 := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hcomponent : ∀ R ∈ components,
      ((componentPoints R).card : ℝ) ≤
        CP * ((M : ℝ) + 1) ^ ((4 : ℝ) + epsilon) := by
    intro R hR
    have hRdata := hcomponents R hR
    have heE : deg R ≤ E :=
      (Finset.single_le_sum (fun S _ ↦ Nat.zero_le (deg S)) hR).trans hmass
    let A := affinePolynomialChangeAlgEquiv
      (fun i ↦ (x0 i : ℝ)) (m : ℝ) (by exact_mod_cast hm.ne')
    have hpacket : HasAffineHilbertDimensionDegree (R.map A) (dim R) (deg R) :=
      (hasAffineHilbertDimensionDegree_map_affinePolynomialChange_iff
        R (fun i ↦ (x0 i : ℝ)) (m : ℝ)
          (by exact_mod_cast hm.ne') (dim R) (deg R)).2 hRdata.2.2
    have hsubset : componentPoints R ⊆ pilaIntegralPoints (R.map A) ((M : ℝ) + 1) := by
      intro z hz
      obtain ⟨hzpoints, hzR⟩ := Finset.mem_filter.mp hz
      apply intPoint_mem_pilaIntegralPoints_of_mem_zeroLocus
      · intro i
        have hi : |(z i : ℝ)| ≤ (M : ℝ) := by
          simpa only [Int.cast_abs, Nat.cast_natAbs] using
            (show ((z i).natAbs : ℝ) ≤ (M : ℝ) by exact_mod_cast hbox z hzpoints i)
        linarith
      · exact mem_realPacketZeroLocus_of_realAffineImage hm R x0 z hzR
    calc
      ((componentPoints R).card : ℝ) ≤
          ((pilaIntegralPoints (R.map A) ((M : ℝ) + 1)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
      _ ≤ CP * ((M : ℝ) + 1) ^ ((4 : ℝ) + epsilon) :=
        hPilaBound (dim R) (deg R) hRdata.1 hRdata.2.1 heE (R.map A) hpacket
          ((M : ℝ) + 1) hB
  have hcomponentCount : components.card ≤ E := by
    calc
      components.card = ∑ _R ∈ components, 1 := by simp
      _ ≤ ∑ R ∈ components, deg R :=
        Finset.sum_le_sum fun R hR ↦ (hcomponents R hR).2.1
      _ ≤ E := hmass
  have hcard : points.card ≤ ∑ R ∈ components, (componentPoints R).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hcountReal : (components.card : ℝ) ≤ (max 1 E : ℕ) := by
    exact_mod_cast hcomponentCount.trans (Nat.le_max_right 1 E)
  calc
    (points.card : ℝ) ≤ ∑ R ∈ components, ((componentPoints R).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ _R ∈ components, CP * ((M : ℝ) + 1) ^ ((4 : ℝ) + epsilon) :=
      Finset.sum_le_sum fun R hR ↦ hcomponent R hR
    _ = (components.card : ℝ) * (CP * ((M : ℝ) + 1) ^ ((4 : ℝ) + epsilon)) := by simp
    _ ≤ (max 1 E : ℕ) * (CP * ((M : ℝ) + 1) ^ ((4 : ℝ) + epsilon)) :=
      mul_le_mul_of_nonneg_right hcountReal (by positivity)
    _ = C * ((M : ℝ) + 1) ^ ((4 : ℝ) + epsilon) := by
      dsimp only [C]
      ring

/-- The old nongeometric-prime counting conclusion, with the Galois-frontier
input replaced by one internally constructed proper hypersurface. All degree
and real-component mass facts are discharged internally. -/
theorem exists_uniform_qbarReducibleProjectivePrime_properDivisor_pilaBound
    (hPila : Pila1995TheoremA)
    (hSmooth : StandardAG.RationalProjectiveSmoothPointGeometricIntegrality)
    (N D : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) (r d m M : ℕ),
        Q.IsPrime →
        Q.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
        HasProjectiveDimensionDegree Q r d →
        r ≤ 4 → d ≤ D → ¬ (qbarCoefficientExtensionIdeal Q).IsPrime →
        0 < m → 1 ≤ M →
        ∀ (x0 : IntVector (N + 1)) (points : Finset (IntVector (N + 1))),
          (∀ z ∈ points, ∀ i, (z i).natAbs ≤ M) →
          (∀ z ∈ points,
            let x : Fin (N + 1) → ℚ := fun i ↦ (integralAffineMap x0 z m i : ℚ)
            x ≠ 0 ∧ x ∈ affineIdealZeroLocus Q) →
          (points.card : ℝ) ≤ C * ((M : ℝ) + 1) ^ ((4 : ℝ) + epsilon) := by
  classical
  let E := D * (N * (D - 1) + 1)
  obtain ⟨C, hC, hbound⟩ := exists_uniform_realComponentDegreeMass_fourthPower_pilaBound
    hPila (N + 1) E epsilon hepsilon
  refine ⟨C, hC, ?_⟩
  intro Q r d m M hprime hhom hdegree hr hd hnot hm hM x0 points hbox hzero
  have hDE : D ≤ E := by
    dsimp only [E]
    rw [Nat.mul_add, Nat.mul_one]
    omega
  by_cases hrsmall : r ≤ 3
  · obtain ⟨cdeg, hc, hmass⟩ := homogeneousPrimeRealConeComponentDegreeMass_internal
      N r d Q hprime hhom hdegree
    refine hbound Q (fun _ ↦ r + 1) cdeg ?_
      (hmass.trans (hd.trans hDE)) m M hm hM x0 points hbox (fun z hz ↦ (hzero z hz).2)
    intro R hR
    exact ⟨Nat.succ_le_succ hrsmall, (hc R hR).1, (hc R hR).2.toHilbert⟩
  · have hr4 : r = 4 := by omega
    subst r
    have hrN : 4 ≤ N := by
      have h := ringKrullDim_quotient_le (I := Q)
      rw [hdegree.1, ringKrullDim_mvPolynomial_fin_eq_of_field ℚ (N + 1)] at h
      have : 4 + 1 ≤ N + 1 := by exact_mod_cast h
      omega
    have hnotGeo : ¬ GeometricallyPrimeMvPolynomialIdeal Q := by
      intro hgeo
      exact hnot (hgeo Qbar)
    obtain ⟨G, a, ha, hGhom, hGnot, hGzero⟩ :=
      exists_homogeneous_proper_divisor_of_nongeometric_rational_points
        hSmooth hrN Q hprime hhom hdegree hnotGeo
    let J := Q ⊔ Ideal.span ({G} : Set _)
    have hJhom : J.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ) := by
      apply hhom.sup
      apply Ideal.homogeneous_span
      intro f hf
      obtain rfl := Set.mem_singleton_iff.mp hf
      exact ⟨a, hGhom⟩
    obtain ⟨sourceDeg, hsource, hsourceMass⟩ :=
      properHomogeneousHypersurface_componentDimensionDegreeMass
        (projectiveHilbertDegreeCertification_internal ℚ) Q G hprime hhom hdegree hGhom hGnot
    obtain ⟨cdeg, hc, hmass⟩ :=
      realCone_componentDegreeMass_of_equidimensional_rationalComponents
        homogeneousPrimeRealConeComponentDegreeMass_internal J hJhom sourceDeg hsource hsourceMass
    have ha' : a ≤ N * (D - 1) := ha.trans
      (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le_sub_right hd 1))
    have hmassE : d * a ≤ E :=
      (Nat.mul_le_mul hd ha').trans (by dsimp [E]; nlinarith)
    refine hbound J (fun _ ↦ 4) cdeg ?_
      (hmass.trans hmassE) m M hm hM x0 points hbox ?_
    · intro R hR
      exact ⟨le_rfl, (hc R hR).1, (hc R hR).2.toHilbert⟩
    · intro z hz
      exact mem_affineIdealZeroLocus_sup_span_singleton Q G _ (hzero z hz).2
        (hGzero _ (hzero z hz).2)

end
end TranslatedDepthSeven
