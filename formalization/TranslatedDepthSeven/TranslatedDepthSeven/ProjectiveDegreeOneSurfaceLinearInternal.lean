import TranslatedDepthSeven.ProjectiveDegreeOneCurveSpanInternal
import TranslatedDepthSeven.RankSevenPersistentPlaneVertexSpan
import TranslatedDepthSeven.HomogeneousLinearNormalizationBoxCount

/-!
# Degree-one projective varieties have literal linear cones

The homogeneous normalization argument is dimension-independent.  Its
generic rank is bounded by the leading Hilbert coefficient, and degree one
therefore makes it an isomorphism.  The inverse images of coordinate classes
are homogeneous linear forms.  Their evaluations give a linear embedding
of the parameter vector space whose range is exactly the original ideal's
affine zero locus.  This also proves the dimension of that range; no
existence of rational points is assumed.

The final endpoint is the exact rational projective-surface statement used
by the persistent plane argument.  No geometric premise is added.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 2200000

/-- Leading-coefficient comparison with a polynomial-ring Hilbert function,
including projective dimension zero. -/
theorem multiplicity_le_one_of_shifted_projectiveHilbert_lower
    (P : Polynomial ℚ) (r δ E k₀ : ℕ)
    (hPdegree : P.natDegree = r)
    (hPleading : P.leadingCoeff = (r.factorial : ℚ)⁻¹)
    (hlower : ∀ n ≥ k₀,
      ((δ * (n + r).choose r : ℕ) : ℚ) ≤ P.eval ((n + E : ℕ) : ℚ)) :
    δ ≤ 1 := by
  let S : Polynomial ℚ := P.comp (Polynomial.X + Polynomial.C (E : ℚ))
  let B : Polynomial ℚ := Polynomial.preHilbertPoly ℚ r 0
  have hlinearDegree :
      (Polynomial.X + Polynomial.C (E : ℚ)).natDegree = 1 :=
    Polynomial.natDegree_X_add_C (E : ℚ)
  have hSdegree : S.natDegree = r := by
    simp only [S, Polynomial.natDegree_comp, hPdegree, hlinearDegree, mul_one]
  have hBdegree : B.natDegree = r :=
    Polynomial.natDegree_preHilbertPoly ℚ r 0
  have hSlc : S.leadingCoeff = (r.factorial : ℚ)⁻¹ := by
    dsimp only [S]
    rw [Polynomial.leadingCoeff_comp (by rw [hlinearDegree]; omega),
      Polynomial.leadingCoeff_X_add_C, one_pow, mul_one, hPleading]
  have hBlc : B.leadingCoeff = (r.factorial : ℚ)⁻¹ :=
    Polynomial.leadingCoeff_preHilbertPoly ℚ r 0
  have hfactorial : (r.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero r
  have hSne : S ≠ 0 := by
    intro hzero
    have h := hSlc
    rw [hzero, Polynomial.leadingCoeff_zero] at h
    exact (inv_ne_zero hfactorial) h.symm
  have hBne : B ≠ 0 := by
    intro hzero
    have h := hBlc
    rw [hzero, Polynomial.leadingCoeff_zero] at h
    exact (inv_ne_zero hfactorial) h.symm
  have hdegree : S.degree = B.degree := by
    rw [Polynomial.degree_eq_natDegree hSne,
      Polynomial.degree_eq_natDegree hBne, hSdegree, hBdegree]
  have hlimitQ : Filter.Tendsto
      (fun q : ℚ ↦ S.eval q / B.eval q) Filter.atTop (nhds (1 : ℚ)) := by
    have h := Polynomial.div_tendsto_leadingCoeff_div_of_degree_eq S B hdegree
    simpa only [hSlc, hBlc, div_self (inv_ne_zero hfactorial)] using h
  have hlimitN : Filter.Tendsto
      (fun n : ℕ ↦ S.eval (n : ℚ) / B.eval (n : ℚ))
      Filter.atTop (nhds (1 : ℚ)) :=
    hlimitQ.comp tendsto_natCast_atTop_atTop
  have heventual : ∀ᶠ n : ℕ in Filter.atTop,
      (δ : ℚ) ≤ S.eval (n : ℚ) / B.eval (n : ℚ) := by
    filter_upwards [Filter.eventually_ge_atTop k₀] with n hn
    have hB : B.eval (n : ℚ) = ((n + r).choose r : ℚ) := by
      dsimp only [B]
      simpa using
        (Polynomial.preHilbertPoly_eq_choose_sub_add ℚ r
          (k := 0) (n := n) (by omega))
    have hBpos : 0 < B.eval (n : ℚ) := by
      rw [hB]
      exact_mod_cast Nat.choose_pos (by omega : r ≤ n + r)
    have hS : S.eval (n : ℚ) = P.eval ((n + E : ℕ) : ℚ) := by
      simp [S]
    rw [le_div_iff₀ hBpos, hB, hS]
    norm_cast
    simpa [Nat.mul_comm] using hlower n hn
  exact_mod_cast ge_of_tendsto hlimitN heventual

/-- In any projective dimension, a degree-one homogeneous normalization has
the expected number of parameters and is surjective. -/
theorem homogeneousLinearNormalization_surjective_of_projective_degree_one
    {K : Type*} [Field K] [CharZero K] {N r : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hprime : I.IsPrime)
    (D : HomogeneousLinearNormalizationData I)
    (hprojective : HasProjectiveDimensionDegree I r 1) :
    D.parameterCount = r + 1 ∧ Function.Surjective D.hom := by
  have hdimension := D.ringKrullDim_eq_parameterPolynomial (N + 1) I hprime
  rw [ringKrullDim_mvPolynomial_fin_eq_of_field K D.parameterCount] at hdimension
  have hcount : D.parameterCount = r + 1 := by
    have hdim : (D.parameterCount : WithBot ℕ∞) = (r + 1 : ℕ) := by
      rw [← hdimension]
      simpa only [Nat.cast_add, Nat.cast_one] using hprojective.1
    exact_mod_cast hdim
  refine ⟨hcount, ?_⟩
  letI : I.IsPrime := hprime
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial (Fin (N + 1)) K ⧸ I
  let g := D.hom
  letI : IsDomain A := Ideal.Quotient.isDomain I
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : FaithfulSMul B A :=
    (faithfulSMul_iff_algebraMap_injective B A).mpr D.hom_injective
  haveI : Module.Finite B A := D.hom_finite
  have hdegree_le : Module.finrank (FractionRing B)
      (LocalizedModule (nonZeroDivisors B) A) ≤ 1 := by
    obtain ⟨E, hlower⟩ := exists_genericRank_lower_homogeneous_normalizationData
      K (Fin (N + 1)) I D (by omega)
    obtain ⟨_hdim, _hd, P, hPdegree, hPlc, k₀, hPeventual⟩ := hprojective
    apply multiplicity_le_one_of_shifted_projectiveHilbert_lower P r
      (Module.finrank (FractionRing B)
        (LocalizedModule (nonZeroDivisors B) A)) E k₀ hPdegree
        (by simpa only [Nat.cast_one, one_div] using hPlc)
    intro n hn
    have hvalue := hPeventual (n + E) (by omega)
    have hvalue' :
        (Module.finrank K
          (quotientHomogeneousComponent K (Fin (N + 1)) I (n + E)) : ℚ) =
            P.eval ((n + E : ℕ) : ℚ) := by
      simpa only [projectiveHilbertPiece, quotientHomogeneousComponent] using hvalue
    have hl := hlower n
    have hchoose : (D.parameterCount + n - 1).choose n = (n + r).choose r := by
      rw [hcount, show r + 1 + n - 1 = n + r by omega]
      simpa only [Nat.add_sub_cancel] using
        (Nat.choose_symm (by omega : r ≤ n + r))
    rw [hchoose] at hl
    rw [← hvalue']
    exact_mod_cast hl
  have hdegree_pos : 0 < Module.finrank (FractionRing B)
      (LocalizedModule (nonZeroDivisors B) A) := by
    let f := LocalizedModule.mkLinearMap (nonZeroDivisors B) A
    have hf : Function.Injective f := by
      apply (IsLocalizedModule.injective_iff_isRegular
        (S := nonZeroDivisors B) (f := f)).mpr
      intro c x y hxy
      change (c : B) • x = (c : B) • y at hxy
      rw [Algebra.smul_def, Algebra.smul_def] at hxy
      exact mul_left_cancel₀
        (map_ne_zero_of_mem_nonZeroDivisors
          (algebraMap B A) D.hom_injective c.property) hxy
    letI : Nontrivial (LocalizedModule (nonZeroDivisors B) A) := hf.nontrivial
    exact Module.finrank_pos
  haveI : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  have hrank : Module.finrank (FractionRing B)
      (LocalizedModule (nonZeroDivisors B) A) = 1 := by omega
  exact algebraMap_surjective_of_localized_finrank_eq_one
    (B := B) (A := A) D.hom_injective hrank

/-- A homogeneous linear polynomial defines a linear functional on the
coordinate vector space. -/
def homogeneousOneEvaluationLinearMap
    {K : Type*} [Field K] {s : ℕ}
    (f : MvPolynomial (Fin s) K) (hf : f.IsHomogeneous 1) :
    (Fin s → K) →ₗ[K] K where
  toFun x := MvPolynomial.eval x f
  map_add' x y := by
    simpa only [one_mul, Pi.add_apply] using
      eval_add_smul_of_isHomogeneous_one f hf x y 1
  map_smul' c x := by
    have hzero : MvPolynomial.eval (0 : Fin s → K) f = 0 := by
      have h := eval_add_smul_of_isHomogeneous_one f hf 0 0 1
      simp only [Pi.zero_apply, mul_zero, zero_add, one_mul] at h
      exact add_left_cancel (h.symm.trans (add_zero _).symm)
    simpa only [Pi.zero_apply, zero_add, hzero, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply] using
      eval_add_smul_of_isHomogeneous_one f hf 0 x c

/-- A bijective homogeneous linear normalization explicitly identifies the
cone with a linear subspace of the parameter dimension. -/
theorem exists_linearCone_of_homogeneousLinearNormalization_surjective
    {K : Type*} [Field K] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K))
    (D : HomogeneousLinearNormalizationData I)
    (hsurjective : Function.Surjective D.hom) :
    ∃ L : Submodule K (Fin (N + 1) → K),
      Module.finrank K L = D.parameterCount ∧
      (L : Set (Fin (N + 1) → K)) = affineIdealZeroLocus I := by
  classical
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial (Fin (N + 1)) K ⧸ I
  let e : B ≃ₐ[K] A := AlgEquiv.ofBijective D.hom
    ⟨D.hom_injective, hsurjective⟩
  let P (i : Fin (N + 1)) : B := e.symm ((Ideal.Quotient.mkₐ K I) (X i))
  have hP (i : Fin (N + 1)) : (P i).IsHomogeneous 1 := by
    obtain ⟨R, hR, heq⟩ := exists_homogeneous_preimage_of_surjective_linear_quotient
      I hhomogeneous D.forms D.forms_isHomogeneous hsurjective
      1 (X i) (isHomogeneous_X K i)
    have heq' : e R = (Ideal.Quotient.mkₐ K I) (X i) := heq
    have hPR : P i = R := by
      dsimp only [P]
      rw [← heq', e.symm_apply_apply]
    rw [hPR]
    exact hR
  let F : (Fin D.parameterCount → K) →ₗ[K] (Fin (N + 1) → K) :=
    LinearMap.pi fun i ↦ homogeneousOneEvaluationLinearMap (P i) (hP i)
  let phi (u : Fin D.parameterCount → K) : A →ₐ[K] K :=
    (MvPolynomial.aeval u).comp e.symm.toAlgHom
  have hcoord (u : Fin D.parameterCount → K) (i : Fin (N + 1)) :
      phi u ((Ideal.Quotient.mkₐ K I) (X i)) = F u i := rfl
  have hcomp (u : Fin D.parameterCount → K) :
      (phi u).comp (Ideal.Quotient.mkₐ K I) = MvPolynomial.aeval (F u) := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa using hcoord u i
  have hFzero (u : Fin D.parameterCount → K) : F u ∈ affineIdealZeroLocus I := by
    exact (quotientAlgHomToAffineIdealPoint I (phi u)).property
  have hFinjective : Function.Injective F := by
    intro u v huv
    have hphi : phi u = phi v := by
      apply AlgHom.ext
      intro a
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
      have h := (hcomp u).trans ((congrArg MvPolynomial.aeval huv).trans (hcomp v).symm)
      exact AlgHom.congr_fun h f
    funext j
    have h := AlgHom.congr_fun hphi (e (X j))
    change MvPolynomial.aeval u (e.symm (e (X j))) =
      MvPolynomial.aeval v (e.symm (e (X j))) at h
    simpa only [e.symm_apply_apply, MvPolynomial.aeval_X] using h
  have hFsurjective (z : Fin (N + 1) → K) (hz : z ∈ affineIdealZeroLocus I) :
      ∃ u, F u = z := by
    let chi : A →ₐ[K] K := affineIdealPointToQuotientAlgHom I ⟨z, hz⟩
    let u : Fin D.parameterCount → K := fun j ↦ chi (e (X j))
    have hu : MvPolynomial.aeval u = chi.comp e.toAlgHom := by
      apply MvPolynomial.algHom_ext
      intro j
      rw [MvPolynomial.aeval_X]
      rfl
    have hphi : phi u = chi := by
      apply AlgHom.ext
      intro a
      change MvPolynomial.aeval u (e.symm a) = chi a
      rw [hu]
      change chi (e (e.symm a)) = chi a
      rw [e.apply_symm_apply]
    refine ⟨u, ?_⟩
    funext i
    rw [← hcoord, hphi]
    change MvPolynomial.aeval z (X i) = z i
    exact MvPolynomial.aeval_X z i
  refine ⟨LinearMap.range F, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hFinjective, Module.finrank_fin_fun]
  · ext z
    exact ⟨fun ⟨u, hu⟩ ↦ hu ▸ hFzero u, hFsurjective z⟩

/-- Generic internally proved degree-one linearity, with the exact affine
cone and its vector-space dimension displayed. -/
theorem exists_linearCone_of_projective_degree_one
    {K : Type*} [Field K] [CharZero K] {N r : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hprime : I.IsPrime)
    (hhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K))
    (hprojective : HasProjectiveDimensionDegree I r 1) :
    ∃ L : Submodule K (Fin (N + 1) → K),
      Module.finrank K L = r + 1 ∧
      (L : Set (Fin (N + 1) → K)) = affineIdealZeroLocus I := by
  obtain ⟨D⟩ := exists_homogeneousLinearNormalizationData
    (N + 1) I hprime hhomogeneous
  obtain ⟨hcount, hsurjective⟩ :=
    homogeneousLinearNormalization_surjective_of_projective_degree_one I hprime D hprojective
  obtain ⟨L, hdim, hL⟩ :=
    exists_linearCone_of_homogeneousLinearNormalization_surjective I hhomogeneous D hsurjective
  exact ⟨L, hdim.trans hcount, hL⟩

/-- Exact internal discharge of the rational surface-cone input. -/
theorem degreeOneProjectiveSurfaceConeIsThreeDimensionalLinear_internal :
    StandardAG.DegreeOneProjectiveSurfaceConeIsThreeDimensionalLinear := by
  intro N I hprime hhomogeneous hprojective
  exact exists_linearCone_of_projective_degree_one I hprime hhomogeneous hprojective

end

end TranslatedDepthSeven
