import TranslatedDepthSeven.RankSevenDegreeOneProperStarCounting

/-!
# Pila on a proper hyperplane section of a projective fourfold

This file isolates the ordinary geometric fact needed after the equations
obtained from the counted points do not both vanish identically on a
fourfold.  A hyperplane which does not contain a geometrically integral
projective fourfold cuts an effective Cartier divisor.  Its reduced real
components have affine-cone dimension four, and the sum of their degrees is
at most the degree of the fourfold.  Pila is then applied separately to those
literal components after the affine packet substitution.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 10000000

namespace StandardAG

/-- Reduced degree mass for a proper hyperplane section of a geometrically
integral projective fourfold, after extension from `ℚ` to `ℝ`.

The homogeneous cone over the fourfold has dimension five.  Since `f` is a
non-zero-divisor in its geometrically integral coordinate ring, the cone over
the hyperplane section is pure of dimension four.  The hyperplane has degree
one, so the sum of the degrees of the reduced components is at most `d`.

References: Hartshorne, *Algebraic Geometry*, I.7.7; Stacks Project,
Section 33.35 (Tag `089X`) for the hyperplane-section exact sequence, and
Lemma 43.16.4 (Tag `0B01`) for the Cartier-divisor multiplicities.  Flat
base change to `ℝ` preserves the Hilbert polynomial, and discarding
multiplicities can only decrease the displayed degree sum. -/
def GeometricallyIntegralProjectiveFourfoldHyperplaneRealDegreeMass : Prop :=
  ∀ (N d : ℕ) (Q : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
    Q.IsPrime →
    Q.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
    GeometricallyPrimeMvPolynomialIdeal Q →
    HasProjectiveDimensionDegree Q 4 d →
    ∀ f : MvPolynomial (Fin (N + 1)) ℚ,
      f.IsHomogeneous 1 → f ∉ Q →
      ∃ componentDegree :
          Ideal (MvPolynomial (Fin (N + 1)) ℝ) → ℕ,
        (∀ R ∈ finiteMinimalPrimes
            ((Q ⊔ Ideal.span ({f} : Set _)).map
              (MvPolynomial.map (algebraMap ℚ ℝ))),
          1 ≤ componentDegree R ∧
          HasAffineHilbertDimensionDegree R 4 (componentDegree R)) ∧
        ∑ R ∈ finiteMinimalPrimes
            ((Q ⊔ Ideal.span ({f} : Set _)).map
              (MvPolynomial.map (algebraMap ℚ ℝ))),
          componentDegree R ≤ d

end StandardAG

/-- Every rational point of an ideal lies on one literal real minimal
component of its coefficient extension.  This is the elementary
minimal-prime selection used for the hyperplane section. -/
theorem exists_realMinimalComponent_through_rationalPoint_of_ideal
    {N : ℕ} (I : Ideal (MvPolynomial (Fin N) ℚ))
    (x : Fin N → ℚ) (hx : x ∈ affineIdealZeroLocus I) :
    ∃ R ∈ finiteMinimalPrimes
        (I.map (MvPolynomial.map (algebraMap ℚ ℝ))),
      (fun i ↦ algebraMap ℚ ℝ (x i)) ∈ affineIdealZeroLocus R := by
  let xr : Fin N → ℝ := fun i ↦ algebraMap ℚ ℝ (x i)
  let T : Ideal (MvPolynomial (Fin N) ℝ) :=
    RingHom.ker (MvPolynomial.eval xr)
  letI : T.IsPrime := RingHom.ker_isPrime _
  have hIT : I.map (MvPolynomial.map (algebraMap ℚ ℝ)) ≤ T := by
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    apply RingHom.mem_ker.mpr
    change MvPolynomial.eval xr
      (MvPolynomial.map (algebraMap ℚ ℝ) f) = 0
    rw [show xr = fun i ↦ algebraMap ℚ ℝ (x i) from rfl,
      eval_realCoefficientExtension_at_rationalPoint]
    rw [hx f hf, map_zero]
  obtain ⟨R, hR, hRT⟩ := exists_finiteMinimalPrime_le hIT
  refine ⟨R, hR, ?_⟩
  rw [mem_affineIdealZeroLocus_iff]
  exact hRT

/-- A point on `Q` at which `f` vanishes lies on the literal ideal
`Q + (f)`. -/
theorem mem_affineIdealZeroLocus_sup_span_singleton
    {N : ℕ} (Q : Ideal (MvPolynomial (Fin N) ℚ))
    (f : MvPolynomial (Fin N) ℚ) (x : Fin N → ℚ)
    (hxQ : x ∈ affineIdealZeroLocus Q)
    (hxf : MvPolynomial.eval x f = 0) :
    x ∈ affineIdealZeroLocus (Q ⊔ Ideal.span ({f} : Set _)) := by
  rw [mem_affineIdealZeroLocus_iff] at hxQ ⊢
  have hQker : Q ≤ RingHom.ker (MvPolynomial.eval x) := by
    intro g hg
    exact RingHom.mem_ker.mpr (hxQ g hg)
  have hfker : Ideal.span ({f} : Set _) ≤
      RingHom.ker (MvPolynomial.eval x) := by
    apply Ideal.span_le.mpr
    intro g hg
    have hgf : g = f := by simpa only [Set.mem_singleton_iff] using hg
    subst g
    exact RingHom.mem_ker.mpr hxf
  exact sup_le hQker hfker

/-- Real zero-locus membership is transported by the invertible affine
packet substitution. -/
theorem mem_affinePacketZeroLocus_of_realAffineImage
    {N m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin N) ℝ))
    (x0 z : IntVector N)
    (hz : (fun i ↦ (integralAffineMap x0 z m i : ℝ)) ∈
      affineIdealZeroLocus I) :
    (fun i ↦ (z i : ℝ)) ∈ affineIdealZeroLocus
      (I.map (affinePolynomialChangeAlgEquiv
        (fun i ↦ (x0 i : ℝ)) (m : ℝ)
        (by exact_mod_cast hm.ne'))) := by
  change I.map (affinePolynomialChangeAlgEquiv
      (fun i ↦ (x0 i : ℝ)) (m : ℝ)
      (by exact_mod_cast hm.ne')) ≤
    RingHom.ker (MvPolynomial.eval (fun i ↦ (z i : ℝ)))
  rw [Ideal.map_le_iff_le_comap]
  intro g hg
  change MvPolynomial.eval (fun i ↦ (z i : ℝ))
      (affinePolynomialChangeAlgEquiv
        (fun i ↦ (x0 i : ℝ)) (m : ℝ)
        (by exact_mod_cast hm.ne') g) = 0
  change MvPolynomial.aeval (fun i ↦ (z i : ℝ))
      (affinePolynomialChangeAlgEquiv
        (fun i ↦ (x0 i : ℝ)) (m : ℝ)
        (by exact_mod_cast hm.ne') g) = 0
  rw [aeval_affinePolynomialChange]
  have hpoint :
      (fun i ↦ (x0 i : ℝ) + (m : ℝ) * (z i : ℝ)) =
        fun i ↦ (integralAffineMap x0 z m i : ℝ) := by
    funext i
    simp [integralAffineMap]
  rw [hpoint]
  exact hz g hg

/-- Coefficient-uniform Pila estimate for any finite set in a normalized
box whose original affine images lie on a geometrically integral projective
fourfold and on one proper rational hyperplane.  The hyperplane coefficients
are completely unrestricted: the constant depends only on `N`, the degree
bound `D`, and epsilon. -/
theorem exists_uniform_projectiveFourfold_properHyperplane_pilaBound
    (hPila : Pila1995TheoremA)
    (hHyperplaneMass :
      StandardAG.GeometricallyIntegralProjectiveFourfoldHyperplaneRealDegreeMass)
    (N D : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) (d : ℕ),
        Q.IsPrime →
        Q.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
        GeometricallyPrimeMvPolynomialIdeal Q →
        HasProjectiveDimensionDegree Q 4 d →
        d ≤ D →
        ∀ f : MvPolynomial (Fin (N + 1)) ℚ,
          f.IsHomogeneous 1 → f ∉ Q →
          ∀ (m M : ℕ), 0 < m → 1 ≤ M →
          ∀ (x0 : IntVector (N + 1))
            (points : Finset (IntVector (N + 1))),
            (∀ z ∈ points, ∀ i, (z i).natAbs ≤ M) →
            (∀ z ∈ points,
              (fun i ↦ (integralAffineMap x0 z m i : ℚ)) ∈
                affineIdealZeroLocus Q ∧
              MvPolynomial.eval
                (fun i ↦ (integralAffineMap x0 z m i : ℚ)) f = 0) →
            (points.card : ℝ) ≤
              C * ((M : ℝ) + 1) ^ ((4 : ℝ) + epsilon) := by
  classical
  obtain ⟨CP, hCP, hPilaBound⟩ :=
    pila1995_hilbertDimensionAtMost_boundedDegree
      hPila (N + 1) 4 D epsilon hepsilon
  let C : ℝ := (max 1 D : ℕ) * CP
  have hC : 0 < C := mul_pos (by positivity) hCP
  refine ⟨C, hC, ?_⟩
  intro Q d hQprime hQhomogeneous hQgeometric hQprojective hdD
    f hfhomogeneous hfQ m M hm hM x0 points hbox hzero
  obtain ⟨componentDegree, hcomponents, hmass⟩ :=
    hHyperplaneMass N d Q hQprime hQhomogeneous hQgeometric hQprojective
      f hfhomogeneous hfQ
  let J : Ideal (MvPolynomial (Fin (N + 1)) ℚ) :=
    Q ⊔ Ideal.span ({f} : Set _)
  let components := finiteMinimalPrimes
    (J.map (MvPolynomial.map (algebraMap ℚ ℝ)))
  let componentPoints :=
    fun R : Ideal (MvPolynomial (Fin (N + 1)) ℝ) ↦
      points.filter fun z ↦
        (fun i ↦ (integralAffineMap x0 z m i : ℝ)) ∈
          affineIdealZeroLocus R
  have hcover : points ⊆ components.biUnion componentPoints := by
    intro z hz
    let x : Fin (N + 1) → ℚ :=
      fun i ↦ (integralAffineMap x0 z m i : ℚ)
    have hxsection : x ∈ affineIdealZeroLocus J := by
      exact mem_affineIdealZeroLocus_sup_span_singleton Q f x
        (hzero z hz).1 (hzero z hz).2
    obtain ⟨R, hR, hxR⟩ :=
      exists_realMinimalComponent_through_rationalPoint_of_ideal
        J x hxsection
    refine Finset.mem_biUnion.mpr ⟨R, ?_, ?_⟩
    · simpa only [components] using hR
    · rw [Finset.mem_filter]
      refine ⟨hz, ?_⟩
      simpa only [x, Nat.cast_ofNat, Int.cast_ofNat] using hxR
  have hB : (1 : ℝ) < (M : ℝ) + 1 := by
    have hNat : 1 < M + 1 := Nat.lt_succ_iff.mpr hM
    exact_mod_cast hNat
  have hcomponent : ∀ R ∈ components,
      ((componentPoints R).card : ℝ) ≤
        CP * ((M : ℝ) + 1) ^ ((4 : ℝ) + epsilon) := by
    intro R hR
    have hRdata := hcomponents R (by simpa only [components, J] using hR)
    have heD : componentDegree R ≤ D := by
      exact ((Finset.single_le_sum
        (fun S _hS ↦ Nat.zero_le (componentDegree S))
        (by simpa only [components, J] using hR)).trans hmass).trans hdD
    let A := affinePolynomialChangeAlgEquiv
      (fun i ↦ (x0 i : ℝ)) (m : ℝ) (by exact_mod_cast hm.ne')
    have hpacket : HasAffineHilbertDimensionDegree
        (R.map A) 4 (componentDegree R) :=
      (hasAffineHilbertDimensionDegree_map_affinePolynomialChange_iff
        R (fun i ↦ (x0 i : ℝ)) (m : ℝ)
          (by exact_mod_cast hm.ne') 4 (componentDegree R)).2 hRdata.2
    have hsubset : componentPoints R ⊆
        pilaIntegralPoints (R.map A) ((M : ℝ) + 1) := by
      intro z hz
      have hzdata := Finset.mem_filter.mp hz
      apply intPoint_mem_pilaIntegralPoints_of_mem_zeroLocus
      · intro i
        have hi : |(z i : ℝ)| ≤ (M : ℝ) := by
          simpa only [Int.cast_abs, Nat.cast_natAbs] using
            (show ((z i).natAbs : ℝ) ≤ (M : ℝ) by
              exact_mod_cast hbox z hzdata.1 i)
        linarith
      · exact mem_affinePacketZeroLocus_of_realAffineImage
          hm R x0 z hzdata.2
    calc
      ((componentPoints R).card : ℝ) ≤
          ((pilaIntegralPoints (R.map A) ((M : ℝ) + 1)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
      _ ≤ CP * ((M : ℝ) + 1) ^ ((4 : ℝ) + epsilon) :=
        hPilaBound 4 (componentDegree R) (le_refl 4) hRdata.1 heD
          (R.map A) hpacket ((M : ℝ) + 1) hB
  have hcomponentCount : components.card ≤ D := by
    calc
      components.card = ∑ _R ∈ components, 1 := by simp
      _ ≤ ∑ R ∈ components, componentDegree R := by
        apply Finset.sum_le_sum
        intro R hR
        exact (hcomponents R
          (by simpa only [components, J] using hR)).1
      _ ≤ d := by simpa only [components, J] using hmass
      _ ≤ D := hdD
  have hcard : points.card ≤
      ∑ R ∈ components, (componentPoints R).card := by
    calc
      points.card ≤ (components.biUnion componentPoints).card :=
        Finset.card_le_card hcover
      _ ≤ ∑ R ∈ components, (componentPoints R).card :=
        Finset.card_biUnion_le
  have hsum :
      (∑ R ∈ components, ((componentPoints R).card : ℝ)) ≤
        ∑ _R ∈ components,
          CP * ((M : ℝ) + 1) ^ ((4 : ℝ) + epsilon) := by
    exact Finset.sum_le_sum fun R hR ↦ hcomponent R hR
  have hcountReal : (components.card : ℝ) ≤ (max 1 D : ℕ) := by
    exact_mod_cast hcomponentCount.trans (Nat.le_max_right 1 D)
  calc
    (points.card : ℝ) ≤
        ∑ R ∈ components, ((componentPoints R).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ _R ∈ components,
          CP * ((M : ℝ) + 1) ^ ((4 : ℝ) + epsilon) := hsum
    _ = (components.card : ℝ) *
          (CP * ((M : ℝ) + 1) ^ ((4 : ℝ) + epsilon)) := by simp
    _ ≤ (max 1 D : ℕ) *
          (CP * ((M : ℝ) + 1) ^ ((4 : ℝ) + epsilon)) := by
      exact mul_le_mul_of_nonneg_right hcountReal (by positivity)
    _ = C * ((M : ℝ) + 1) ^ ((4 : ℝ) + epsilon) := by
      dsimp only [C]
      ring

end

end TranslatedDepthSeven
