import TranslatedDepthSeven.ProjectiveAffineChartDimensionInternal
import TranslatedDepthSeven.HilbertConeFiniteDifference
import TranslatedDepthSeven.IsolatedVertexQuotientPersistentPila

/-!
# The affine chart of a homogeneous cone over a characteristic-zero field

These statements concern the literal map `X₀ ↦ 1`, `Xᵢ₊₁ ↦ Xᵢ`.
The chart domain has dimension one less than the cone domain.  Combining
the exact Hilbert-function identity with finite differences preserves the
degree, also over the real field.  There is no coefficient-height condition.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

theorem standardDehomogenizationHom_comp_finSuccRename
    (K : Type*) [CommRing K] (N : ℕ) :
    (multivariateDehomogenization (R := K) (σ := Fin N)).toRingHom.comp
        (MvPolynomial.renameEquiv K (_root_.finSuccEquiv N)).toRingHom =
      standardDehomogenizationHom K N := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [multivariateDehomogenization, standardDehomogenizationHom]
  · intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [multivariateDehomogenization, standardDehomogenizationHom,
        MvPolynomial.renameEquiv_apply]
    · simp [multivariateDehomogenization, standardDehomogenizationHom,
        MvPolynomial.renameEquiv_apply]

theorem map_standardDehomogenizationHom_finSuccRename
    {K : Type*} [CommRing K] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) :
    (I.map (MvPolynomial.renameEquiv K (_root_.finSuccEquiv N))).map
        multivariateDehomogenization.toRingHom =
      I.map (standardDehomogenizationHom K N) := by
  change (I.map (MvPolynomial.renameEquiv K (_root_.finSuccEquiv N)).toRingHom).map
    multivariateDehomogenization.toRingHom = _
  rw [Ideal.map_map, standardDehomogenizationHom_comp_finSuccRename]

theorem finSuccRename_homogeneousPrime_avoids_none
    {K : Type*} [Field K] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K))
    (hprime : I.IsPrime) (hX : X (0 : Fin (N + 1)) ∉ I) :
    let J := I.map (MvPolynomial.renameEquiv K (_root_.finSuccEquiv N))
    J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Option (Fin N)) K) ∧
      J.IsPrime ∧ X (none : Option (Fin N)) ∉ J := by
  dsimp only
  refine ⟨map_renameEquiv_isHomogeneous (_root_.finSuccEquiv N) I hI, ?_, ?_⟩
  · letI : I.IsPrime := hprime
    infer_instance
  · intro hmem
    let E := MvPolynomial.renameEquiv K (_root_.finSuccEquiv N)
    obtain ⟨f, hf, hfeq⟩ :=
      (Ideal.mem_map_iff_of_surjective E E.surjective).mp hmem
    have hfX : f = X (0 : Fin (N + 1)) := by
      apply E.injective
      rw [hfeq]
      simp [E, MvPolynomial.renameEquiv_apply]
    exact hX (hfX ▸ hf)

/-- Dimension of the literal nonempty chart, without a supplied projective
certificate. In particular the cone dimension is positive. -/
theorem exists_standardAffineChart_dimension
    {K : Type*} [Field K] [CharZero K] {N s : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K))
    (hprime : I.IsPrime) (hX : X (0 : Fin (N + 1)) ∉ I)
    (hdim : ringKrullDim (MvPolynomial (Fin (N + 1)) K ⧸ I) =
      (s : WithBot ℕ∞)) :
    ∃ r : ℕ, r + 1 = s ∧
      ringKrullDim (MvPolynomial (Fin N) K ⧸
        I.map (standardDehomogenizationHom K N)) = (r : WithBot ℕ∞) := by
  let I' := I.map (MvPolynomial.renameEquiv K (_root_.finSuccEquiv N))
  obtain ⟨hI'hom, hI'prime, hI'X⟩ :=
    finSuccRename_homogeneousPrime_avoids_none I hI hprime hX
  let J := I'.map multivariateDehomogenization.toRingHom
  let R := MvPolynomial (Fin N) K ⧸ J
  have hJprime : J.IsPrime :=
    map_multivariateDehomogenization_isPrime I' hI'hom hI'prime hI'X
  letI : J.IsPrime := hJprime
  have hconeTrdeg : Algebra.trdeg K (MvPolynomial (Option (Fin N)) K ⧸ I') =
      (s : Cardinal) := by
    rw [← (renameQuotientAlgEquiv K (_root_.finSuccEquiv N) I).trdeg_eq]
    exact trdeg_eq_nat_of_primeAffine_ringKrullDim_eq K I hprime hdim
  have hpolyTrdeg : Algebra.trdeg K (Polynomial R) = (s : Cardinal) :=
    (trdeg_optionChartPolynomial_eq_cone I' hI'hom hI'prime hI'X).trans hconeTrdeg
  obtain ⟨r, _hrN, _g, _hginj, _hgfinite, hrTrdeg⟩ :=
    exists_finite_injective_normalization_of_primeAffine_with_trdeg J
  have hrs : r + 1 = s := by
    have h := trdeg_add_eq K R (A := Polynomial R)
    rw [Polynomial.trdeg_of_isDomain, hpolyTrdeg] at h
    change Algebra.trdeg K (MvPolynomial (Fin N) K ⧸ J) + 1 = (s : Cardinal) at h
    rw [hrTrdeg] at h
    exact_mod_cast h
  refine ⟨r, hrs, ?_⟩
  have hchartDim := ringKrullDim_eq_nat_of_primeAffine_trdeg_eq K J hJprime hrTrdeg
  have hJ : J = I.map (standardDehomogenizationHom K N) :=
    map_standardDehomogenizationHom_finSuccRename I
  rwa [hJ] at hchartDim

theorem finrank_projectiveHilbertPiece_eq_standardAffineChart
    {K : Type*} [Field K] {N k : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K))
    (hprime : I.IsPrime) (hX : X (0 : Fin (N + 1)) ∉ I) :
    Module.finrank K (projectiveHilbertPiece K N I k) =
      Module.finrank K (affineHilbertFiltration K N
        (I.map (standardDehomogenizationHom K N)) k) := by
  let J := I.map (MvPolynomial.renameEquiv K (_root_.finSuccEquiv N))
  obtain ⟨hJhom, hJprime, hJX⟩ :=
    finSuccRename_homogeneousPrime_avoids_none I hI hprime hX
  change Module.finrank K
    (quotientHomogeneousComponent K (Fin (N + 1)) I k) = _
  rw [finrank_quotientHomogeneousComponent_map_renameEquiv
    K (_root_.finSuccEquiv N) I k]
  rw [finrank_projective_eq_affine_dehomogenization J hJhom hJprime hJX]
  rw [map_standardDehomogenizationHom_finSuccRename]

/-- An affine cone certificate yields the degree-preserving certificate
of its nonempty first chart over any characteristic-zero field. -/
theorem exists_standardAffineChart_dimensionDegree
    {K : Type*} [Field K] [CharZero K] {N s d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K))
    (hX : X (0 : Fin (N + 1)) ∉ I)
    (haffine : HasAffineDimensionDegree I s d) :
    ∃ r : ℕ, r + 1 = s ∧
      HasAffineDimensionDegree (I.map (standardDehomogenizationHom K N)) r d := by
  obtain ⟨r, hrs, hdim⟩ := exists_standardAffineChart_dimension I hI
    haffine.1 hX haffine.2.1
  obtain ⟨r', hr's, hprojective⟩ :=
    exists_projectiveDimensionDegree_of_homogeneous_affineCone I hI haffine (by omega)
  have hrr : r' = r := by omega
  subst r'
  refine ⟨r, hrs, standardAffineChart_isPrime I hI haffine.1 hX,
    hdim, hprojective.2.1, ?_⟩
  rcases hprojective.2.2 with ⟨P, hPdegree, hPlc, k₀, heventual⟩
  refine ⟨P, hPdegree, hPlc, k₀, ?_⟩
  intro k hk
  rw [← finrank_projectiveHilbertPiece_eq_standardAffineChart I hI haffine.1 hX]
  exact heventual k hk

end
end TranslatedDepthSeven
