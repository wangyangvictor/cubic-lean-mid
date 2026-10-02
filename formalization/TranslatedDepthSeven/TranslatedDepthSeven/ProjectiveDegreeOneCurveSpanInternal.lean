import TranslatedDepthSeven.IsolatedVertexQuotientRadialDirection
import TranslatedDepthSeven.ProjectiveDegreeOneSpan
import TranslatedDepthSeven.ParameterCountSurface
import TranslatedDepthSeven.FieldPolynomialKrullDimension
import TranslatedDepthSeven.AffineZeroLocusQuotientPoints

/-!
# The two-point span of an integral projective curve of degree one

This discharges the exact degree-one curve input used by the isolated-vertex
argument.  Homogeneous linear Noether normalization has two parameters.
The linear Hilbert polynomial forces its generic module rank to be one;
integral closedness of the polynomial parameter ring makes normalization
surjective.  The coordinate classes therefore lie in a vector space of
dimension at most two.  Restricting point evaluations to this space proves
the literal two-point spanning assertion.

Every normalization, dimension, and generic-rank ingredient used here has
already been proved internally.  There is no degree--span assumption and no
additional geometric input.  The final linear algebra keeps the nonzero
condition on the first cone representative explicit.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 1800000

/-- A linear Hilbert polynomial with leading coefficient one cannot dominate
two shifted copies of the polynomial-ring Hilbert function. -/
theorem multiplicity_le_one_of_shifted_linearHilbert_lower
    (P : Polynomial ℚ) (δ E k₀ : ℕ)
    (hdegree : P.natDegree = 1) (hleading : P.leadingCoeff = 1)
    (hlower : ∀ n ≥ k₀,
      ((δ * (n + 1) : ℕ) : ℚ) ≤ P.eval ((n + E : ℕ) : ℚ)) :
    δ ≤ 1 := by
  have hcoeff : P.coeff 1 = 1 := by
    simpa only [Polynomial.leadingCoeff, hdegree] using hleading
  have hlinear (x : ℚ) : P.eval x = x + P.coeff 0 := by
    rw [Polynomial.eq_X_add_C_of_natDegree_le_one hdegree.le]
    simp [hcoeff]
  by_contra hδ
  have hδQ : (2 : ℚ) ≤ δ := by exact_mod_cast (by omega : 2 ≤ δ)
  obtain ⟨n₁, hn₁⟩ := exists_nat_gt ((E : ℚ) + P.coeff 0)
  let n := max k₀ n₁
  have hn : (E : ℚ) + P.coeff 0 < n :=
    hn₁.trans_le (by exact_mod_cast (le_max_right k₀ n₁))
  have h := hlower n (le_max_left _ _)
  rw [hlinear] at h
  push_cast at h
  have hnnonnegative : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- In projective dimension one and degree one, finite homogeneous linear
normalization is already an isomorphism. -/
theorem homogeneousLinearNormalization_surjective_of_projective_curve_degree_one
    {K : Type*} [Field K] [CharZero K] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hprime : I.IsPrime)
    (D : HomogeneousLinearNormalizationData I)
    (hprojective : HasProjectiveDimensionDegree I 1 1) :
    D.parameterCount = 2 ∧ Function.Surjective D.hom := by
  have hdimension := D.ringKrullDim_eq_parameterPolynomial (N + 1) I hprime
  rw [ringKrullDim_mvPolynomial_fin_eq_of_field K D.parameterCount] at hdimension
  have hcount : D.parameterCount = 2 := by
    have hdim : (D.parameterCount : WithBot ℕ∞) = 2 := by
      rw [← hdimension]
      simpa using hprojective.1
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
    apply multiplicity_le_one_of_shifted_linearHilbert_lower P
      (Module.finrank (FractionRing B)
        (LocalizedModule (nonZeroDivisors B) A)) E k₀ hPdegree
        (by simpa using hPlc)
    intro n hn
    have hvalue := hPeventual (n + E) (by omega)
    have hvalue' :
        (Module.finrank K
          (quotientHomogeneousComponent K (Fin (N + 1)) I (n + E)) : ℚ) =
            P.eval ((n + E : ℕ) : ℚ) := by
      simpa only [projectiveHilbertPiece, quotientHomogeneousComponent] using hvalue
    have hl := hlower n
    have hchoose : (D.parameterCount + n - 1).choose n = n + 1 := by
      rw [hcount, show 2 + n - 1 = n + 1 by omega]
      exact Nat.choose_succ_self_right n
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

/-- If all coordinate classes lie in a subspace of dimension at most two,
two independent cone points span every cone point.  Point evaluations,
rather than a rationality or saturation assertion, provide the bridge. -/
theorem affineIdeal_twoPointSpan_of_coordinateClasses_in_twoDimensional_space
    {K : Type*} [Field K] {σ : Type*}
    (I : Ideal (MvPolynomial σ K))
    (S : Submodule K (MvPolynomial σ K ⧸ I)) [Module.Finite K S]
    (hdim : Module.finrank K S ≤ 2)
    (hX : ∀ i : σ, (Ideal.Quotient.mkₐ K I) (X i) ∈ S)
    (x y : σ → K) (hx : x ∈ affineIdealZeroLocus I)
    (hy : y ∈ affineIdealZeroLocus I) (hx0 : x ≠ 0)
    (hxy : ¬ ∃ a : K, y = a • x)
    (z : σ → K) (hz : z ∈ affineIdealZeroLocus I) :
    ∃ a c : K, z = a • x + c • y := by
  classical
  let ev (w : {w : σ → K // w ∈ affineIdealZeroLocus I}) : Module.Dual K S :=
    (affineIdealPointToQuotientAlgHom I w).toLinearMap.comp S.subtype
  let coord (i : σ) : S := ⟨(Ideal.Quotient.mkₐ K I) (X i), hX i⟩
  have hcoord (w : {w : σ → K // w ∈ affineIdealZeroLocus I}) (i : σ) :
      ev w (coord i) = w.1 i := by
    simp [ev, coord]
  let ex := ev ⟨x, hx⟩
  let ey := ev ⟨y, hy⟩
  let ez := ev ⟨z, hz⟩
  have hex : ex ≠ 0 := by
    intro hzero
    apply hx0
    funext i
    have h := congrArg (fun f : Module.Dual K S ↦ f (coord i)) hzero
    simpa only [ex, hcoord, LinearMap.zero_apply, Pi.zero_apply] using h
  have hey (a : K) : a • ex ≠ ey := by
    intro heq
    apply hxy
    refine ⟨a, ?_⟩
    funext i
    have h := congrArg (fun f : Module.Dual K S ↦ f (coord i)) heq
    simpa only [ex, ey, LinearMap.smul_apply, hcoord, Pi.smul_apply] using h.symm
  have hLI : LinearIndependent K ![ey, ex] := by
    apply linearIndependent_fin2.mpr
    simpa using And.intro hex hey
  have hspanRank :
      Module.finrank K (Submodule.span K (Set.range ![ey, ex])) = 2 := by
    simpa using finrank_span_eq_card hLI
  have hdualRank : Module.finrank K (Module.Dual K S) ≤ 2 := by
    simpa only [Subspace.dual_finrank_eq] using hdim
  have htop : Submodule.span K (Set.range ![ey, ex]) = ⊤ := by
    apply Submodule.eq_of_le_of_finrank_le le_top
    simpa only [finrank_top, hspanRank] using hdualRank
  have hmem : ez ∈ Submodule.span K ({ey, ex} : Set (Module.Dual K S)) := by
    rw [← Matrix.range_cons_cons_empty ey ex ![], htop]
    trivial
  obtain ⟨c, a, heq⟩ := Submodule.mem_span_pair.mp hmem
  refine ⟨a, c, ?_⟩
  funext i
  have h := congrArg (fun f : Module.Dual K S ↦ f (coord i)) heq
  simpa only [ex, ey, ez, LinearMap.add_apply, LinearMap.smul_apply,
    hcoord, Pi.add_apply, Pi.smul_apply, add_comm] using h.symm

/-- Internal proof of the exact nonzero two-point-span input used by the
radial isolated-vertex records. -/
theorem qbarIntegralProjectiveDegreeOneCurveTwoPointSpan_internal :
    StandardAG.QbarIntegralProjectiveDegreeOneCurveTwoPointSpan := by
  intro N I hprime hhomogeneous hprojective x y hx hy hx0 hxy z hz
  obtain ⟨D⟩ := exists_homogeneousLinearNormalizationData
    (N + 1) I hprime hhomogeneous
  obtain ⟨hcount, hsurjective⟩ :=
    homogeneousLinearNormalization_surjective_of_projective_curve_degree_one
      I hprime D hprojective
  let S : Submodule Qbar (MvPolynomial (Fin (N + 1)) Qbar ⧸ I) :=
    Submodule.span Qbar
      (Set.range fun j ↦ (Ideal.Quotient.mkₐ Qbar I) (D.forms j))
  letI : Module.Finite Qbar S :=
    Module.Finite.span_of_finite Qbar (Set.finite_range _)
  apply affineIdeal_twoPointSpan_of_coordinateClasses_in_twoDimensional_space
    I S ?_ ?_ x y hx hy hx0 hxy z hz
  · have h := finrank_range_le_card (R := Qbar)
      (fun j ↦ (Ideal.Quotient.mkₐ Qbar I) (D.forms j))
    simpa only [Fintype.card_fin, hcount] using h
  · intro i
    exact quotient_X_mem_span_linear_images_of_surjective I hhomogeneous
      D.forms D.forms_isHomogeneous hsurjective i

end

end TranslatedDepthSeven
