import TranslatedDepthSeven.IsolatedVertexQuotientEdgeBezout
import TranslatedDepthSeven.ProjectiveAffineChartBridge
import TranslatedDepthSeven.ProjectiveHilbertCoefficientExtension
import TranslatedDepthSeven.QbarInvariantIdealDescent
import TranslatedDepthSeven.RationalQbarPrimePila
import TranslatedDepthSeven.RationalPrimeGeometricFrontier
import TranslatedDepthSeven.FiniteResiduePacketRescaling
import TranslatedDepthSeven.AffineChartPilaComponentCount

/-!
# Residue-scaled Pila for persistent isolated-vertex quotient curves

A persistent nonempty quotient label is one fixed integral projective curve
over `Qbar`.  Its rational points are treated by the honest Galois
dichotomy.  A Galois-stable curve descends to a rational geometrically prime
curve and is counted by rational Qbar-prime Pila after division by the fixed
residue modulus.  A curve with a distinct conjugate is counted on the
zero-dimensional intersection with that conjugate.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 4000000

local instance isolatedVertexQuotientPersistentPilaPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-! ## Coefficient descent and the standard affine chart -/

/-- The complete projective Hilbert certificate descends along an exact
coefficient-extension identity.  This is the converse direction to
`qbarHasProjectiveDimensionDegree_of_rational` needed after invariant-ideal
descent. -/
theorem rationalHasProjectiveDimensionDegree_of_qbar_map_eq
    {N r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (P : Ideal (MvPolynomial (Fin (N + 1)) Qbar))
    (hmap : I.map (MvPolynomial.map (algebraMap ℚ Qbar)) = P)
    (hPprime : P.IsPrime)
    (hP : HasProjectiveDimensionDegree P r d) :
    HasProjectiveDimensionDegree I r d := by
  rcases hP with ⟨hdim, hd, H, hdegree, hleading, k₀, heventual⟩
  have hmapPrime :
      (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime := by
    rwa [hmap]
  have hdimEq := qbarProjectiveQuotient_ringKrullDim_map_eq I hmapPrime
  rw [hmap] at hdimEq
  refine ⟨hdimEq.symm.trans hdim, hd, H, hdegree, hleading, k₀, ?_⟩
  intro k hk
  have hfinrank := projectiveHilbertPiece_finrank_map_eq
    (K := ℚ) (L := Qbar) N k I
  rw [hmap] at hfinrank
  calc
    (Module.finrank ℚ (projectiveHilbertPiece ℚ N I k) : ℚ) =
        (Module.finrank Qbar (projectiveHilbertPiece Qbar N P k) : ℚ) := by
      exact_mod_cast hfinrank.symm
    _ = H.eval (k : ℚ) := heventual k hk

/-- Primality descends from the literal Qbar coefficient extension. -/
theorem rationalIdeal_isPrime_of_qbarCoefficientExtension_isPrime
    {N : ℕ} (I : Ideal (MvPolynomial (Fin N) ℚ))
    (hprime :
      (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime) :
    I.IsPrime := by
  let R := MvPolynomial (Fin N) ℚ
  let S := MvPolynomial (Fin N) Qbar
  let f : R →+* S := MvPolynomial.map (algebraMap ℚ Qbar)
  let J : Ideal S := I.map f
  letI : Algebra R S := MvPolynomial.algebraMvPolynomial
  have hcomap : J.comap f = I := by
    simpa only [MvPolynomial.algebraMap_apply] using
      (Ideal.comap_map_eq_self_of_faithfullyFlat I)
  have hcomPrime : (J.comap f).IsPrime := by
    exact hprime.comap f
  rwa [hcomap] at hcomPrime

/-- The literal consecutive-coordinate standard-chart substitution commutes
with coefficient extension. -/
theorem standardDehomogenizationHom_comp_map
    {S T : Type*} [CommRing S] [CommRing T]
    (N : ℕ) (f : S →+* T) :
    (standardDehomogenizationHom T N).comp (MvPolynomial.map f) =
      (MvPolynomial.map f).comp (standardDehomogenizationHom S N) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [standardDehomogenizationHom]
  · intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [standardDehomogenizationHom]
    · simp [standardDehomogenizationHom]

/-- Ideal-level form of standard-chart base change. -/
theorem map_standardDehomogenization_map_eq_map_map_standardDehomogenization
    {S T : Type*} [CommRing S] [CommRing T]
    (N : ℕ) (f : S →+* T)
    (I : Ideal (MvPolynomial (Fin (N + 1)) S)) :
    (I.map (MvPolynomial.map f)).map (standardDehomogenizationHom T N) =
      (I.map (standardDehomogenizationHom S N)).map
        (MvPolynomial.map f) := by
  rw [Ideal.map_map, Ideal.map_map,
    standardDehomogenizationHom_comp_map]

/-- Over the rationals, the generic and project-specific names for the
standard-chart map agree definitionally. -/
theorem standardDehomogenizationHom_rat_eq_rationalDehomogenizeAtZeroHom
    (N : ℕ) :
    standardDehomogenizationHom ℚ N =
      (@rationalDehomogenizeAtZeroHom N) := by
  rfl

/-- A homogeneous prime over an arbitrary field stays prime on the
consecutive-coordinate first affine chart when that chart is nonempty. -/
theorem standardAffineChart_isPrime
    {K : Type*} [Field K] {N : ℕ}
    (P : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hPhom : P.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K))
    (hPprime : P.IsPrime)
    (hX : X (0 : Fin (N + 1)) ∉ P) :
    (P.map (standardDehomogenizationHom K N)).IsPrime := by
  let e : MvPolynomial (Fin (N + 1)) K ≃ₐ[K]
      MvPolynomial (Option (Fin N)) K :=
    MvPolynomial.renameEquiv K (_root_.finSuccEquiv N)
  let J : Ideal (MvPolynomial (Option (Fin N)) K) := P.map e
  have hJhom : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Option (Fin N)) K) := by
    simpa only [J, e] using
      map_renameEquiv_isHomogeneous (_root_.finSuccEquiv N) P hPhom
  have hJprime : J.IsPrime := by
    letI : P.IsPrime := hPprime
    dsimp only [J, e]
    infer_instance
  have hJX : X (none : Option (Fin N)) ∉ J := by
    intro hmem
    obtain ⟨f, hf, hfeq⟩ :=
      (Ideal.mem_map_iff_of_surjective e e.surjective).1 hmem
    have hfX : f = X (0 : Fin (N + 1)) := by
      apply e.injective
      rw [hfeq]
      simp [e, MvPolynomial.renameEquiv_apply]
    exact hX (hfX ▸ hf)
  have hprime := map_multivariateDehomogenization_isPrime
    J hJhom hJprime hJX
  have hcomp :
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
  change (Ideal.map multivariateDehomogenization.toRingHom
    (Ideal.map e.toRingHom P)).IsPrime at hprime
  rw [Ideal.map_map, hcomp] at hprime
  exact hprime

/-- The rational standard affine chart remains prime after extension to
`Qbar` whenever the descended projective ideal extends to the displayed
homogeneous Qbar prime. -/
theorem rationalStandardAffineChart_qbarExtension_isPrime
    {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (P : Ideal (MvPolynomial (Fin (N + 1)) Qbar))
    (hmap : I.map (MvPolynomial.map (algebraMap ℚ Qbar)) = P)
    (hPhom : P.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) Qbar))
    (hPprime : P.IsPrime)
    (hX : X (0 : Fin (N + 1)) ∉ P) :
    ((I.map rationalDehomogenizeAtZeroHom).map
      (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime := by
  rw [← standardDehomogenizationHom_rat_eq_rationalDehomogenizeAtZeroHom]
  rw [← map_standardDehomogenization_map_eq_map_map_standardDehomogenization]
  rw [hmap]
  exact standardAffineChart_isPrime P hPhom hPprime hX

/-! ## Rational Qbar-prime Pila for one residue-scaled curve -/

/-- Rational Qbar-prime Pila, with its subpower factor absorbed uniformly
for one nonlinear curve degree. -/
private theorem rationalQbarPrime_pilaCurve_halfPower_oneDegree
    (hPila : Published.Pila1995TheoremARationalQbarPrime)
    (N d : ℕ) (hd : 2 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (I : Ideal (MvPolynomial (Fin N) ℚ)),
        (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
        HasAffineHilbertDimensionDegree I 1 d →
        ∀ V : ℝ, 1 < V →
          ((Published.rationalPilaIntegralPoints I V).card : ℝ) ≤
            C * V ^ ((1 / 2 : ℝ) + ε) := by
  obtain ⟨c, hc, hsource⟩ := hPila 1 d N (by omega)
  let C : ℝ := c * pilaConstant d ε
  have hconstant : 0 < pilaConstant d ε := by
    unfold pilaConstant
    positivity
  refine ⟨C, mul_pos hc hconstant, ?_⟩
  intro I hQbar hI V hV
  have hprinted := hsource I hQbar hI V hV
  have habsorb := pilaCurvePower_mul_factor_le_const_mul_rpow
    hd hε hV.le
  calc
    ((Published.rationalPilaIntegralPoints I V).card : ℝ) ≤
        c * V ^ ((d : ℝ)⁻¹) * pilaFactor d V := by
      simpa [pilaFactor] using hprinted
    _ = c * (V ^ ((d : ℝ)⁻¹) * pilaFactor d V) := by ring
    _ ≤ c * (pilaConstant d ε * V ^ ((1 / 2 : ℝ) + ε)) := by
      exact mul_le_mul_of_nonneg_left habsorb hc.le
    _ = C * V ^ ((1 / 2 : ℝ) + ε) := by
      simp only [C]
      ring

/-- A single coefficient-uniform constant for rational geometrically
integral affine curves of every degree `2,…,D`. -/
theorem exists_uniform_rationalQbarPrime_pilaCurve_halfPower_boundedDegree
    (hPila : Published.Pila1995TheoremARationalQbarPrime)
    (N D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ), 2 ≤ d → d ≤ D →
        ∀ (I : Ideal (MvPolynomial (Fin N) ℚ)),
          (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
          HasAffineHilbertDimensionDegree I 1 d →
          ∀ V : ℝ, 1 < V →
            ((Published.rationalPilaIntegralPoints I V).card : ℝ) ≤
              C * V ^ ((1 / 2 : ℝ) + ε) := by
  let degrees : Finset ℕ := Finset.Icc 2 D
  let degreeSubtype := {d : ℕ // d ∈ degrees}
  have heach : ∀ d : degreeSubtype, ∃ C : ℝ, 0 < C ∧
      ∀ (I : Ideal (MvPolynomial (Fin N) ℚ)),
        (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
        HasAffineHilbertDimensionDegree I 1 d.1 →
        ∀ V : ℝ, 1 < V →
          ((Published.rationalPilaIntegralPoints I V).card : ℝ) ≤
            C * V ^ ((1 / 2 : ℝ) + ε) := by
    intro d
    exact rationalQbarPrime_pilaCurve_halfPower_oneDegree
      hPila N d.1 (Finset.mem_Icc.mp d.2).1 ε hε
  choose c hc hbound using heach
  let C : ℝ := 1 + ∑ d : degreeSubtype, c d
  have hC : 0 < C := by
    dsimp only [C]
    have hsum : 0 ≤ ∑ d : degreeSubtype, c d :=
      Finset.sum_nonneg fun d _ ↦ (hc d).le
    linarith
  refine ⟨C, hC, ?_⟩
  intro d hd hdD I hQbar hI V hV
  have hdmem : d ∈ degrees := Finset.mem_Icc.mpr ⟨hd, hdD⟩
  let e : degreeSubtype := ⟨d, hdmem⟩
  have hsource := hbound e I hQbar (by simpa [e] using hI) V hV
  have hterm : c e ≤ ∑ a : degreeSubtype, c a := by
    exact Finset.single_le_sum
      (fun a _ ↦ (hc a).le) (Finset.mem_univ e)
  have hcle : c e ≤ C := by
    dsimp only [C]
    linarith
  exact hsource.trans
    (mul_le_mul_of_nonneg_right hcle (Real.rpow_nonneg (by positivity) _))

/-- Uniform residue-scaled Pila for a Galois-stable projective Qbar curve.
The proof descends the actual ideal, passes its projective Hilbert data to
the rational standard affine chart, divides the displayed congruence class
by `q`, and applies only rational Qbar-prime Pila. -/
theorem exists_uniform_galoisStableQbarProjectiveCurve_rescaled_constant
    (hPila : Published.Pila1995TheoremARationalQbarPrime)
    (D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {q : ℕ}, 0 < q →
        ∀ (base : IntVector 12)
          (Q : Ideal (MvPolynomial (Fin 13) Qbar))
          (d : ℕ),
        Q.IsPrime →
        Q.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin 13) Qbar) →
        HasProjectiveDimensionDegree Q 1 d →
        2 ≤ d → d ≤ D →
        (∀ g : Qbar ≃ₐ[ℚ] Qbar, conjugateIdeal g Q = Q) →
        ∀ (S : Finset (IntVector 12)),
        base ∈ S →
        (∀ z ∈ S,
          geometricQuotientRationalHomogeneousAffinePoint z ∈
            affineIdealZeroLocus Q) →
        (∀ z ∈ S, IntVectorCongruent q z base) →
        ∀ V : ℝ, 1 < V →
        (∀ z ∈ S, ∀ i,
          |(congruenceDisplacementOrZero q base z i : ℝ)| < V) →
          (S.card : ℝ) ≤ C * V ^ ((1 / 2 : ℝ) + ε) := by
  classical
  obtain ⟨C, hC, hPilaBound⟩ :=
    exists_uniform_rationalQbarPrime_pilaCurve_halfPower_boundedDegree
      hPila 12 D ε hε
  refine ⟨C, hC, ?_⟩
  intro q hq base Q d hQprime hQhom hQprojective hd hdD hstable
    S hbase hzero hcong V hV hquotientBox
  obtain ⟨I, hIhom, hIQ⟩ :=
    rationalHomogeneousIdeal_descent_of_galoisInvariant Q hstable hQhom
  have hIprojective : HasProjectiveDimensionDegree I 1 d :=
    rationalHasProjectiveDimensionDegree_of_qbar_map_eq
      I Q hIQ hQprime hQprojective
  have hIQprime :
      (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime := by
    rwa [hIQ]
  have hIprime : I.IsPrime :=
    rationalIdeal_isPrime_of_qbarCoefficientExtension_isPrime I hIQprime
  have hXQ : X (0 : Fin 13) ∉ Q := by
    intro hX
    have hzeroX := hzero base hbase (X (0 : Fin 13)) hX
    simpa [geometricQuotientRationalHomogeneousAffinePoint,
      quotientRationalHomogeneousAffinePoint] using hzeroX
  have hXI : X (0 : Fin 13) ∉ I := by
    intro hX
    apply hXQ
    rw [← hIQ]
    have hmapX := Ideal.mem_map_of_mem
      (MvPolynomial.map (algebraMap ℚ Qbar)) hX
    simpa using hmapX
  let A : Ideal (MvPolynomial (Fin 12) ℚ) :=
    I.map rationalDehomogenizeAtZeroHom
  have hAprojective : HasAffineHilbertDimensionDegree A 1 d := by
    exact hasAffineHilbertDimensionDegree_rationalStandardAffineChart
      I hIhom hIprime hXI hIprojective
  have hAQbar :
      (A.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime := by
    exact rationalStandardAffineChart_qbarExtension_isPrime
      I Q hIQ hQhom hQprime hXQ
  let A' := A.map (affinePolynomialChangeAlgEquiv
    (fun i ↦ (base i : ℚ)) (q : ℚ)
    (by exact_mod_cast hq.ne'))
  have hA'projective : HasAffineHilbertDimensionDegree A' 1 d := by
    exact (hasAffineHilbertDimensionDegree_map_affinePolynomialChange_iff
      A (fun i ↦ (base i : ℚ)) (q : ℚ)
        (by exact_mod_cast hq.ne') 1 d).2 hAprojective
  have hA'Qbar :
      (A'.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime := by
    exact qbarCoefficientExtension_affinePolynomialChange_isPrime
      A hAQbar (fun i ↦ (base i : ℚ)) (q : ℚ)
        (by exact_mod_cast hq.ne')
  have hinjective : Set.InjOn
      (congruenceDisplacementOrZero q base) (↑S : Set (IntVector 12)) := by
    apply (congruenceDisplacementOrZero_injOn base).mono
    intro z hz
    exact hcong z hz
  have himage : ∀ z ∈ S,
      congruenceDisplacementOrZero q base z ∈
        Published.rationalPilaIntegralPoints A' V := by
    intro z hz
    have hzQ := hzero z hz
    have hzI : quotientRationalHomogeneousAffinePoint z ∈
        affineIdealZeroLocus I := by
      apply (rational_zero_of_ideal_iff_qbar_zero_of_extension
        I Q hIQ (quotientRationalHomogeneousAffinePoint z)).2
      simpa [geometricQuotientRationalHomogeneousAffinePoint] using hzQ
    have hzA : (fun i ↦ (z i : ℚ)) ∈ affineIdealZeroLocus A := by
      rw [mem_affineIdealZeroLocus_iff]
      change I.map rationalDehomogenizeAtZeroHom ≤
        RingHom.ker (MvPolynomial.eval (fun i ↦ (z i : ℚ)))
      rw [Ideal.map_le_iff_le_comap]
      intro f hf
      rw [Ideal.mem_comap, RingHom.mem_ker]
      rw [← standardDehomogenizationHom_rat_eq_rationalDehomogenizeAtZeroHom,
        eval_standardDehomogenizationHom]
      exact hzI f hf
    apply intPoint_mem_rationalPilaIntegralPoints_packet
      hq A base (congruenceDisplacementOrZero q base z) V
    · exact hquotientBox z hz
    · have hreconstruct : integralAffineMap base
          (congruenceDisplacementOrZero q base z) q = z := by
        funext i
        simp only [integralAffineMap]
        exact (congruenceDisplacementOrZero_spec base z (hcong z hz) i).symm
      rwa [hreconstruct]
  have hcard : S.card ≤
      (Published.rationalPilaIntegralPoints A' V).card :=
    Finset.card_le_card_of_injOn
      (congruenceDisplacementOrZero q base) himage hinjective
  calc
    (S.card : ℝ) ≤
        ((Published.rationalPilaIntegralPoints A' V).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ C * V ^ ((1 / 2 : ℝ) + ε) :=
      hPilaBound d hd hdD A' hA'Qbar hA'projective V hV

/-! ## The distinct-conjugate branch -/

namespace StandardAG

/-- Coefficientwise automorphisms of `Qbar` preserve the projective Hilbert
dimension and degree of a homogeneous ideal.  This semilinear Hilbert-piece
transport is the one narrow textbook input not yet provided by the existing
coefficient-extension/renaming APIs. -/
def QbarConjugatePreservesProjectiveDimensionDegree : Prop :=
  ∀ (N r d : ℕ) (g : Qbar ≃ₐ[ℚ] Qbar)
    (P : Ideal (MvPolynomial (Fin (N + 1)) Qbar)),
    HasProjectiveDimensionDegree P r d →
      HasProjectiveDimensionDegree (conjugateIdeal g P) r d

end StandardAG

/-- A coefficientwise conjugate of a homogeneous Qbar ideal is homogeneous. -/
theorem conjugateIdeal_isHomogeneous
    {N : ℕ} (g : Qbar ≃ₐ[ℚ] Qbar)
    (Q : Ideal (MvPolynomial (Fin N) Qbar))
    (hQ : Q.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin N) Qbar)) :
    (conjugateIdeal g Q).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin N) Qbar) := by
  simpa [conjugateIdeal, conjugatePolynomial_apply] using
    isHomogeneous_map_mvPolynomialMap g.toRingHom Q hQ

/-- A coefficientwise conjugate of a prime Qbar ideal is prime. -/
theorem conjugateIdeal_isPrime
    {N : ℕ} (g : Qbar ≃ₐ[ℚ] Qbar)
    (Q : Ideal (MvPolynomial (Fin N) Qbar))
    (hQ : Q.IsPrime) :
    (conjugateIdeal g Q).IsPrime := by
  letI : Q.IsPrime := hQ
  unfold conjugateIdeal
  exact Ideal.map_isPrime_of_equiv (conjugatePolynomial g)

/-- Every finite set of normalized rational points on a Qbar curve with a
distinct conjugate has cardinal at most the square of the curve degree. -/
theorem card_rationalPoints_on_QbarCurve_with_distinct_conjugate_le_degree_sq
    (hBezout : StandardAG.QbarDistinctProjectiveCurveFirstChartBezout)
    (hConjugate :
      StandardAG.QbarConjugatePreservesProjectiveDimensionDegree)
    (Q : Ideal (MvPolynomial (Fin 13) Qbar))
    (d : ℕ)
    (hQprime : Q.IsPrime)
    (hQhom : Q.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 13) Qbar))
    (hQprojective : HasProjectiveDimensionDegree Q 1 d)
    (g : Qbar ≃ₐ[ℚ] Qbar)
    (hne : conjugateIdeal g Q ≠ Q)
    (S : Finset (IntVector 12))
    (hzero : ∀ z ∈ S,
      geometricQuotientRationalHomogeneousAffinePoint z ∈
        affineIdealZeroLocus Q) :
    S.card ≤ d * d := by
  apply card_geometricQuotientPoints_on_distinct_curves_le_degree_mul
    hBezout Q (conjugateIdeal g Q) hQprime
      (conjugateIdeal_isPrime g Q hQprime) hQhom
      (conjugateIdeal_isHomogeneous g Q hQhom)
      hQprojective (hConjugate 12 1 d g Q hQprojective) hne.symm S
  intro z hz
  rw [mem_affineIdealZeroLocus_iff_le_ker_aeval]
  have hQle := hzero z hz
  rw [mem_affineIdealZeroLocus_iff_le_ker_aeval] at hQle
  apply sup_le
  · exact hQle
  · have hconjugate := conjugateIdeal_le_rationalEvaluationKernel
        g Q (quotientRationalHomogeneousAffinePoint z)
        hQle
    simpa [geometricQuotientRationalHomogeneousAffinePoint] using hconjugate

/-- Uniform cell-level Galois dichotomy.  In the stable branch this is the
residue-scaled Pila bound.  In the nonstable branch rationality of the
coordinates puts every point on a distinct conjugate, so Bezout gives the
constant `D²` term. -/
theorem exists_uniform_QbarProjectiveCurve_rescaled_dichotomy_constant
    (hPila : Published.Pila1995TheoremARationalQbarPrime)
    (hBezout : StandardAG.QbarDistinctProjectiveCurveFirstChartBezout)
    (hConjugate :
      StandardAG.QbarConjugatePreservesProjectiveDimensionDegree)
    (D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {q : ℕ}, 0 < q →
        ∀ (base : IntVector 12)
          (Q : Ideal (MvPolynomial (Fin 13) Qbar))
          (d : ℕ),
        Q.IsPrime →
        Q.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin 13) Qbar) →
        HasProjectiveDimensionDegree Q 1 d →
        2 ≤ d → d ≤ D →
        ∀ (S : Finset (IntVector 12)),
        base ∈ S →
        (∀ z ∈ S,
          geometricQuotientRationalHomogeneousAffinePoint z ∈
            affineIdealZeroLocus Q) →
        (∀ z ∈ S, IntVectorCongruent q z base) →
        ∀ V : ℝ, 1 < V →
        (∀ z ∈ S, ∀ i,
          |(congruenceDisplacementOrZero q base z i : ℝ)| < V) →
          (S.card : ℝ) ≤
            (D : ℝ) ^ 2 + C * V ^ ((1 / 2 : ℝ) + ε) := by
  obtain ⟨C, hC, hstableBound⟩ :=
    exists_uniform_galoisStableQbarProjectiveCurve_rescaled_constant
      hPila D ε hε
  refine ⟨C, hC, ?_⟩
  intro q hq base Q d hQprime hQhom hQprojective hd hdD S hbase
    hzero hcong V hV hquotientBox
  rcases conjugateIdeal_fixed_or_exists_distinct Q with hstable | ⟨g, hg⟩
  · have hbound := hstableBound hq base Q d hQprime hQhom
      hQprojective hd hdD hstable S hbase hzero hcong V hV hquotientBox
    exact hbound.trans (le_add_of_nonneg_left (sq_nonneg (D : ℝ)))
  · have hcard :=
      card_rationalPoints_on_QbarCurve_with_distinct_conjugate_le_degree_sq
        hBezout hConjugate Q d hQprime hQhom hQprojective g hg S hzero
    have hdegree : (S.card : ℝ) ≤ (D : ℝ) ^ 2 := by
      calc
        (S.card : ℝ) ≤ ((d * d : ℕ) : ℝ) := by exact_mod_cast hcard
        _ = (d : ℝ) ^ 2 := by norm_num [pow_two]
        _ ≤ (D : ℝ) ^ 2 := by
          gcongr
    exact hdegree.trans (le_add_of_nonneg_right
      (mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _)))

/-! ## The literal persistent quotient cell at one surviving residue -/

/-- Points in the persistent `Q`-cell for which the displayed modulus
survives, restricted to one literal residue class. -/
def isolatedVertexQuotientPersistentSurvivingResidueCell
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (Q : Ideal (MvPolynomial (Fin 13) Qbar))
    (q : ReservoirModulus Ppool k) (rho : Fin 12 → ZMod q.1) :
    Finset (IntVector 12) :=
  (isolatedVertexQuotientDenominatorCompatiblePersistentCell
    U p sourceEquations CF hx₀ lowerEquations model hquotient
      hqpos hqsf hqlower (some Q)).filter fun w ↦
    survivesTwoCertificates q ((p.m : ℤ) * model.denominator)
        (isolatedVertexQuotientSelectedCertificateValue
          U p sourceEquations CF hx₀ lowerEquations w) ∧
      (integralResidueVector w : Fin 12 → ZMod q.1) = rho

/-- Membership in the literal cell exposes persistence, survival, and the
fixed residue separately. -/
theorem mem_isolatedVertexQuotientPersistentSurvivingResidueCell_iff
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (Q : Ideal (MvPolynomial (Fin 13) Qbar))
    (q : ReservoirModulus Ppool k) (rho : Fin 12 → ZMod q.1)
    (w : IntVector 12) :
    w ∈ isolatedVertexQuotientPersistentSurvivingResidueCell
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hqpos hqsf hqlower Q q rho ↔
      w ∈ isolatedVertexQuotientDenominatorCompatiblePersistentCell
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hqpos hqsf hqlower (some Q) ∧
      survivesTwoCertificates q ((p.m : ℤ) * model.denominator)
        (isolatedVertexQuotientSelectedCertificateValue
          U p sourceEquations CF hx₀ lowerEquations w) ∧
      (integralResidueVector w : Fin 12 → ZMod q.1) = rho := by
  classical
  simp [isolatedVertexQuotientPersistentSurvivingResidueCell]

/-- Every point in a literal persistent surviving residue cell is on its
displayed retained Qbar curve. -/
theorem mem_zeroLocus_and_retained_of_mem_persistentSurvivingResidueCell
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    {Q : Ideal (MvPolynomial (Fin 13) Qbar)}
    {q : ReservoirModulus Ppool k} {rho : Fin 12 → ZMod q.1}
    {w : IntVector 12}
    (hw : w ∈ isolatedVertexQuotientPersistentSurvivingResidueCell
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hqpos hqsf hqlower Q q rho) :
    geometricQuotientRationalHomogeneousAffinePoint w ∈
        affineIdealZeroLocus Q ∧
      IsRetainedNonradialQuotientNodeComponent
        (qbarIntVector (dropFirstIntVector (U.pointEquiv x₀)))
        (algebraMap ℚ Qbar (p.m : ℚ)) Q := by
  have hwdata :=
    (mem_isolatedVertexQuotientPersistentSurvivingResidueCell_iff
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hqpos hqsf hqlower Q q rho w).1 hw
  exact mem_zeroLocus_and_retainedNonradial_of_mem_denominatorCompatiblePersistentCell
    U p sourceEquations CF hx₀ lowerEquations model hquotient
      hqpos hqsf hqlower hwdata.1 hwdata.2.1

/-- Actual persistent-cell specialization of the Galois dichotomy.  The
degree `e ≥ 2` is the literal degree carried by the retained component;
no rationality is inferred from the existence of rational points. -/
theorem exists_degree_constant_card_persistentSurvivingResidueCell_le
    (hPila : Published.Pila1995TheoremARationalQbarPrime)
    (hBezout : StandardAG.QbarDistinctProjectiveCurveFirstChartBezout)
    (hConjugate :
      StandardAG.QbarConjugatePreservesProjectiveDimensionDegree)
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (Q : Ideal (MvPolynomial (Fin 13) Qbar))
    (q : ReservoirModulus Ppool k) (rho : Fin 12 → ZMod q.1)
    (base : IntVector 12)
    (hbase : base ∈ isolatedVertexQuotientPersistentSurvivingResidueCell
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hqpos hqsf hqlower Q q rho)
    (ε : ℝ) (hε : 0 < ε)
    (V : ℝ) (hV : 1 < V)
    (hquotientBox : ∀ z ∈
      isolatedVertexQuotientPersistentSurvivingResidueCell
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hqpos hqsf hqlower Q q rho,
      ∀ i, |(congruenceDisplacementOrZero q.1 base z i : ℝ)| < V) :
    ∃ (e : ℕ) (C : ℝ),
      2 ≤ e ∧ 0 < C ∧
      HasProjectiveDimensionDegree Q 1 e ∧
      ((isolatedVertexQuotientPersistentSurvivingResidueCell
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hqpos hqsf hqlower Q q rho).card : ℝ) ≤
        (e : ℝ) ^ 2 + C * V ^ ((1 / 2 : ℝ) + ε) := by
  classical
  let S := isolatedVertexQuotientPersistentSurvivingResidueCell
    U p sourceEquations CF hx₀ lowerEquations model hquotient
      hqpos hqsf hqlower Q q rho
  have hbaseGeom :=
    mem_zeroLocus_and_retained_of_mem_persistentSurvivingResidueCell
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hqpos hqsf hqlower hbase
  obtain ⟨s, e, hQintegral, hQprojective, hs, he, _hnonradial⟩ :=
    hbaseGeom.2
  subst s
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_QbarProjectiveCurve_rescaled_dichotomy_constant
      hPila hBezout hConjugate e ε hε
  refine ⟨e, C, he, hC, hQprojective, ?_⟩
  apply hbound (hqpos q) base Q e hQintegral.1 hQintegral.2
    hQprojective he le_rfl S hbase
  · intro z hz
    exact (mem_zeroLocus_and_retained_of_mem_persistentSurvivingResidueCell
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hqpos hqsf hqlower hz).1
  · intro z hz
    have hzdata :=
      (mem_isolatedVertexQuotientPersistentSurvivingResidueCell_iff
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hqpos hqsf hqlower Q q rho z).1 hz
    have hbdata :=
      (mem_isolatedVertexQuotientPersistentSurvivingResidueCell_iff
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hqpos hqsf hqlower Q q rho base).1 hbase
    have hzPacket : z ∈ integralResiduePacket S rho :=
      mem_integralResiduePacket_iff.mpr ⟨hz, hzdata.2.2⟩
    have hbasePacket : base ∈ integralResiduePacket S rho :=
      mem_integralResiduePacket_iff.mpr ⟨hbase, hbdata.2.2⟩
    exact intVectorCongruent_of_mem_same_integralResiduePacket
      hzPacket hbasePacket
  · exact hV
  · exact hquotientBox

/-- Fully specialized residue-scale form.  The quotient box already built
into the isolated-vertex point set gives divided side
`2 * transformedSide / q + 2`; hence no separate box hypothesis remains. -/
theorem exists_degree_constant_card_persistentSurvivingResidueCell_le_residueScaled
    (hPila : Published.Pila1995TheoremARationalQbarPrime)
    (hBezout : StandardAG.QbarDistinctProjectiveCurveFirstChartBezout)
    (hConjugate :
      StandardAG.QbarConjugatePreservesProjectiveDimensionDegree)
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (Q : Ideal (MvPolynomial (Fin 13) Qbar))
    (q : ReservoirModulus Ppool k) (rho : Fin 12 → ZMod q.1)
    (base : IntVector 12)
    (hbase : base ∈ isolatedVertexQuotientPersistentSurvivingResidueCell
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hqpos hqsf hqlower Q q rho)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (e : ℕ) (C : ℝ),
      2 ≤ e ∧ 0 < C ∧
      HasProjectiveDimensionDegree Q 1 e ∧
      ((isolatedVertexQuotientPersistentSurvivingResidueCell
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hqpos hqsf hqlower Q q rho).card : ℝ) ≤
        (e : ℝ) ^ 2 + C *
          (2 * (isolatedVertexTransformedNaturalSide U p : ℝ) / q.1 + 2) ^
            ((1 / 2 : ℝ) + ε) := by
  classical
  let S := isolatedVertexQuotientPersistentSurvivingResidueCell
    U p sourceEquations CF hx₀ lowerEquations model hquotient
      hqpos hqsf hqlower Q q rho
  let V : ℝ :=
    2 * (isolatedVertexTransformedNaturalSide U p : ℝ) / q.1 + 2
  have hV : 1 < V := by
    dsimp only [V]
    have hqreal : (0 : ℝ) < q.1 := by exact_mod_cast hqpos q
    have hnonneg : 0 ≤
        2 * (isolatedVertexTransformedNaturalSide U p : ℝ) / q.1 := by
      positivity
    linarith
  apply exists_degree_constant_card_persistentSurvivingResidueCell_le
    hPila hBezout hConjugate U p sourceEquations CF hx₀ lowerEquations
      model hquotient hqpos hqsf hqlower Q q rho base hbase ε hε V hV
  intro z hz i
  have hzdata :=
    (mem_isolatedVertexQuotientPersistentSurvivingResidueCell_iff
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hqpos hqsf hqlower Q q rho z).1 hz
  have hbdata :=
    (mem_isolatedVertexQuotientPersistentSurvivingResidueCell_iff
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hqpos hqsf hqlower Q q rho base).1 hbase
  have hzPacket : z ∈ integralResiduePacket S rho :=
    mem_integralResiduePacket_iff.mpr ⟨hz, hzdata.2.2⟩
  have hbasePacket : base ∈ integralResiduePacket S rho :=
    mem_integralResiduePacket_iff.mpr ⟨hbase, hbdata.2.2⟩
  have hcong : IntVectorCongruent q.1 z base :=
    intVectorCongruent_of_mem_same_integralResiduePacket
      hzPacket hbasePacket
  have hzRegular := (Finset.mem_filter.mp hzdata.1).1
  have hbRegular := (Finset.mem_filter.mp hbdata.1).1
  have hzPoint := (mem_isolatedVertexRegularQuotientPointFinset_iff
    U p x₀ sourceEquations CF lowerEquations z).1 hzRegular |>.1
  have hbPoint := (mem_isolatedVertexRegularQuotientPointFinset_iff
    U p x₀ sourceEquations CF lowerEquations base).1 hbRegular |>.1
  have hzbox : ∀ j,
      |(z j : ℝ) - (0 : ℝ)| ≤
        (isolatedVertexTransformedNaturalSide U p : ℝ) := by
    intro j
    have hj := isolatedVertexQuotientPoint_coordinate_le
      U p x₀ sourceEquations CF hzPoint j
    have hjReal : ((z j).natAbs : ℝ) ≤
        (isolatedVertexTransformedNaturalSide U p : ℝ) := by
      exact_mod_cast hj
    simpa only [sub_zero, Nat.cast_natAbs, Int.cast_abs] using hjReal
  have hbasebox : ∀ j,
      |(base j : ℝ) - (0 : ℝ)| ≤
        (isolatedVertexTransformedNaturalSide U p : ℝ) := by
    intro j
    have hj := isolatedVertexQuotientPoint_coordinate_le
      U p x₀ sourceEquations CF hbPoint j
    have hjReal : ((base j).natAbs : ℝ) ≤
        (isolatedVertexTransformedNaturalSide U p : ℝ) := by
      exact_mod_cast hj
    simpa only [sub_zero, Nat.cast_natAbs, Int.cast_abs] using hjReal
  have hraw := congruenceDisplacementOrZero_coordinate_bound
    (hqpos q) base z hcong (center := (0 : RealVector 12))
      (R := (isolatedVertexTransformedNaturalSide U p : ℝ))
      hzbox hbasebox i
  dsimp only [V]
  linarith

end

end TranslatedDepthSeven
