import TranslatedDepthSeven.RankSevenDegreeOneProperStarLowDegree
import TranslatedDepthSeven.AffineChartPilaComponentCount

/-!
# The geometrically reducible components of a literal projective star

For a rational homogeneous prime `Q` which is reducible after extension to
`Qbar`, `RationalPrimeGeometricFrontier` constructs one fixed rational
homogeneous frontier containing every rational point of `Q` and having
strictly smaller dimension.  Here we make the ensuing component cover
literal: first take the actual rational minimal components of that frontier,
then the actual real minimal components after coefficient extension, and
discard only the irrelevant cone vertex.

The sole geometric input below is the standard fixed-degree assertion that
this displayed finite component set has uniformly bounded degree mass and
that its nonempty projective components have dimension at most three.  It is
a static base-change/Bezout statement and contains no lattice-point count.
Pila is then applied separately to the displayed real prime components, with
its constant chosen before `Q`, the affine packet, and the finite point set.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 12000000

/-- Coefficient extension of a rational homogeneous cone to `ℝ`. -/
def realCoefficientExtensionOfRationalIdeal {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) :
    Ideal (MvPolynomial (Fin (N + 1)) ℝ) :=
  I.map (MvPolynomial.map (algebraMap ℚ ℝ))

/-- The literal real minimal components obtained from the actual rational
minimal components of the rational geometric frontier. -/
def rationalFrontierRealMinimalComponents {N : ℕ}
    (Q : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) :
    Finset (Ideal (MvPolynomial (Fin (N + 1)) ℝ)) := by
  classical
  exact (finiteMinimalPrimes (rationalGeometricFrontierIdeal Q)).biUnion
    fun R ↦ finiteMinimalPrimes (realCoefficientExtensionOfRationalIdeal R)

/-- The preceding literal component set with the cone vertex removed. -/
def activeRationalFrontierRealMinimalComponents {N : ℕ}
    (Q : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) :
    Finset (Ideal (MvPolynomial (Fin (N + 1)) ℝ)) := by
  classical
  exact (rationalFrontierRealMinimalComponents Q).filter fun R ↦
    ¬ projectiveIrrelevantIdeal ℝ N ≤ R

namespace StandardAG

/-- Fixed-degree degree bounds for the literal rational-frontier component
set.  This is the reduced-component form of flat invariance and additivity
of projective Hilbert polynomials, combined with Bezout for the Galois-
conjugate intersections defining `rationalGeometricFrontierIdeal`.

The integer `E` is selected solely from the ambient dimension and the degree
bound.  No coefficient height, integral point, translated box, or counting
constant occurs in the statement.

References: Hartshorne, Chapter I, Sections 4 and 7; Fulton,
*Intersection Theory*, Section 8.4; and the Stacks Project, Tags `00P0`,
`01M3`, and Section 43.16. -/
def RationalGeometricFrontierRealComponentBounds : Prop :=
  ∀ (N D : ℕ), ∃ E : ℕ, 1 ≤ E ∧
    ∀ (Q : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) (r d : ℕ),
      Q.IsPrime →
      Q.IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
      HasProjectiveDimensionDegree Q r d →
      r ≤ 4 → d ≤ D →
      ¬ (qbarCoefficientExtensionIdeal Q).IsPrime →
        (activeRationalFrontierRealMinimalComponents Q).card ≤ E ∧
        ∀ R ∈ activeRationalFrontierRealMinimalComponents Q,
          ∃ s e : ℕ, s ≤ 3 ∧ 1 ≤ e ∧ e ≤ E ∧
            R.IsHomogeneous
              (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℝ) ∧
            HasProjectiveHilbertDimensionDegree R s e

end StandardAG

/-- A nonzero rational point on a geometrically reducible rational prime is
contained in one of the literal active real frontier components.  This is
proved from the definition of the frontier and minimal-prime decomposition;
it is not part of the external fixed-degree input. -/
theorem exists_activeRationalFrontierRealMinimalComponent_through_point
    {N : ℕ}
    (Q : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    {x : Fin (N + 1) → ℚ} (hxne : x ≠ 0)
    (hxQ : x ∈ affineIdealZeroLocus Q) :
    ∃ R ∈ activeRationalFrontierRealMinimalComponents Q,
      (fun i ↦ algebraMap ℚ ℝ (x i)) ∈ affineIdealZeroLocus R := by
  classical
  let J := rationalGeometricFrontierIdeal Q
  have hxJ : x ∈ affineIdealZeroLocus J :=
    rationalZero_mem_rationalGeometricFrontierIdeal Q x hxQ
  let Tq : Ideal (MvPolynomial (Fin (N + 1)) ℚ) :=
    RingHom.ker (MvPolynomial.eval x)
  letI : Tq.IsPrime := RingHom.ker_isPrime _
  have hJTq : J ≤ Tq := by
    rw [mem_affineIdealZeroLocus_iff] at hxJ
    exact hxJ
  obtain ⟨P, hP, hPTq⟩ := exists_finiteMinimalPrime_le hJTq
  let xr : Fin (N + 1) → ℝ := fun i ↦ algebraMap ℚ ℝ (x i)
  let Tr : Ideal (MvPolynomial (Fin (N + 1)) ℝ) :=
    RingHom.ker (MvPolynomial.eval xr)
  letI : Tr.IsPrime := RingHom.ker_isPrime _
  have hPTr : realCoefficientExtensionOfRationalIdeal P ≤ Tr := by
    rw [realCoefficientExtensionOfRationalIdeal, Ideal.map_le_iff_le_comap]
    intro f hf
    apply RingHom.mem_ker.mpr
    change MvPolynomial.eval xr
      (MvPolynomial.map (algebraMap ℚ ℝ) f) = 0
    rw [show xr = fun i ↦ algebraMap ℚ ℝ (x i) from rfl,
      eval_realCoefficientExtension_at_rationalPoint]
    have hzero : MvPolynomial.eval x f = 0 :=
      RingHom.mem_ker.mp (hPTq hf)
    rw [hzero, map_zero]
  obtain ⟨R, hR, hRTr⟩ := exists_finiteMinimalPrime_le hPTr
  have hRall : R ∈ rationalFrontierRealMinimalComponents Q := by
    rw [rationalFrontierRealMinimalComponents]
    exact Finset.mem_biUnion.mpr ⟨P, hP, hR⟩
  have hxR : xr ∈ affineIdealZeroLocus R := by
    rw [mem_affineIdealZeroLocus_iff]
    exact hRTr
  have hactive : ¬ projectiveIrrelevantIdeal ℝ N ≤ R := by
    intro hirr
    apply hxne
    funext i
    have hXi : X i ∈ projectiveIrrelevantIdeal ℝ N := by
      apply Ideal.subset_span
      exact ⟨i, rfl⟩
    have hzeroReal := hxR (X i) (hirr hXi)
    have hmapzero : algebraMap ℚ ℝ (x i) = 0 := by
      simpa [xr] using hzeroReal
    exact (map_eq_zero_iff (algebraMap ℚ ℝ)
      (FaithfulSMul.algebraMap_injective ℚ ℝ)).mp hmapzero
  refine ⟨R, ?_, hxR⟩
  rw [activeRationalFrontierRealMinimalComponents, Finset.mem_filter]
  exact ⟨hRall, hactive⟩

/-- Real vanishing is transported exactly by the packet substitution
`x = x0 + m z`. -/
theorem mem_realPacketZeroLocus_of_realAffineImage
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
  intro f hf
  change MvPolynomial.eval (fun i ↦ (z i : ℝ))
      (affinePolynomialChangeAlgEquiv
        (fun i ↦ (x0 i : ℝ)) (m : ℝ)
        (by exact_mod_cast hm.ne') f) = 0
  change MvPolynomial.aeval (fun i ↦ (z i : ℝ))
      (affinePolynomialChangeAlgEquiv
        (fun i ↦ (x0 i : ℝ)) (m : ℝ)
        (by exact_mod_cast hm.ne') f) = 0
  rw [aeval_affinePolynomialChange]
  have hpoint :
      (fun i ↦ (x0 i : ℝ) + (m : ℝ) * (z i : ℝ)) =
        fun i ↦ (integralAffineMap x0 z m i : ℝ) := by
    funext i
    simp [integralAffineMap]
  rw [hpoint]
  exact hz f hf

/-- Coefficient-uniform Pila bound for geometrically reducible rational
projective primes of dimension at most four.  The frontier degree bound and
the Pila constant are chosen before the ideal, affine packet, and points. -/
theorem exists_uniform_qbarReducibleProjectivePrime_pilaBound
    (hPila : Pila1995TheoremA)
    (hFrontier : StandardAG.RationalGeometricFrontierRealComponentBounds)
    (N D : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) (r d m M : ℕ),
        Q.IsPrime →
        Q.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
        HasProjectiveDimensionDegree Q r d →
        r ≤ 4 → d ≤ D →
        ¬ (qbarCoefficientExtensionIdeal Q).IsPrime →
        0 < m → 1 ≤ M →
        ∀ (x0 : IntVector (N + 1))
          (points : Finset (IntVector (N + 1))),
          (∀ z ∈ points, ∀ i, (z i).natAbs ≤ M) →
          (∀ z ∈ points,
            let x : Fin (N + 1) → ℚ :=
              fun i ↦ (integralAffineMap x0 z m i : ℚ)
            x ≠ 0 ∧ x ∈ affineIdealZeroLocus Q) →
          (points.card : ℝ) ≤
            C * ((M : ℝ) + 1) ^ ((4 : ℝ) + epsilon) := by
  classical
  obtain ⟨E, hE, hFrontierBound⟩ := hFrontier N D
  obtain ⟨CP, hCP, hPilaBound⟩ :=
    pila1995_hilbertDimensionAtMostFour_boundedDegree
      hPila (N + 1) E epsilon hepsilon
  let C : ℝ := (E : ℝ) * CP
  refine ⟨C, mul_pos (by exact_mod_cast hE) hCP, ?_⟩
  intro Q r d m M hQprime hQhom hQprojective hr hd hQbar hm hM
    x0 points hbox hzero
  let components := activeRationalFrontierRealMinimalComponents Q
  have hgeometry := hFrontierBound Q r d hQprime hQhom hQprojective
    hr hd hQbar
  let componentPoints := fun R : Ideal (MvPolynomial (Fin (N + 1)) ℝ) ↦
    points.filter fun z ↦
      (fun i ↦ (integralAffineMap x0 z m i : ℝ)) ∈
        affineIdealZeroLocus R
  have hcover : points ⊆ components.biUnion componentPoints := by
    intro z hz
    let x : Fin (N + 1) → ℚ :=
      fun i ↦ (integralAffineMap x0 z m i : ℚ)
    obtain ⟨R, hR, hxR⟩ :=
      exists_activeRationalFrontierRealMinimalComponent_through_point
        Q (hzero z hz).1 (hzero z hz).2
    refine Finset.mem_biUnion.mpr ⟨R, ?_, ?_⟩
    · simpa only [components] using hR
    · rw [Finset.mem_filter]
      refine ⟨hz, ?_⟩
      simpa only [x, Nat.cast_ofNat, Int.cast_ofNat] using hxR
  have hB : (1 : ℝ) < (M : ℝ) + 1 := by
    have : 1 < M + 1 := Nat.lt_succ_iff.mpr hM
    exact_mod_cast this
  have hcomponent : ∀ R ∈ components,
      ((componentPoints R).card : ℝ) ≤
        CP * ((M : ℝ) + 1) ^ ((4 : ℝ) + epsilon) := by
    intro R hR
    obtain ⟨s, e, hs, he, heE, hRhom, hRprojective⟩ :=
      hgeometry.2 R (by simpa only [components] using hR)
    let A := affinePolynomialChangeAlgEquiv
      (fun i ↦ (x0 i : ℝ)) (m : ℝ) (by exact_mod_cast hm.ne')
    have hRprime : R.IsPrime := by
      have hRall : R ∈ rationalFrontierRealMinimalComponents Q :=
        (Finset.mem_filter.mp
          (show R ∈ activeRationalFrontierRealMinimalComponents Q by
            simpa only [components] using hR)).1
      rw [rationalFrontierRealMinimalComponents] at hRall
      obtain ⟨P, _hP, hRmin⟩ := Finset.mem_biUnion.mp hRall
      exact isPrime_of_mem_finiteMinimalPrimes hRmin
    have hcone : HasAffineHilbertDimensionDegree R (s + 1) e :=
      hasAffineHilbertDimensionDegree_of_homogeneous_hasProjectiveHilbertDimensionDegree
        R hRhom hRprime s e hRprojective
    have hpacket : HasAffineHilbertDimensionDegree (R.map A) (s + 1) e :=
      (hasAffineHilbertDimensionDegree_map_affinePolynomialChange_iff
        R (fun i ↦ (x0 i : ℝ)) (m : ℝ)
          (by exact_mod_cast hm.ne') (s + 1) e).2 hcone
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
      · exact mem_realPacketZeroLocus_of_realAffineImage
          hm R x0 z hzdata.2
    calc
      ((componentPoints R).card : ℝ) ≤
          ((pilaIntegralPoints (R.map A) ((M : ℝ) + 1)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
      _ ≤ CP * ((M : ℝ) + 1) ^ ((4 : ℝ) + epsilon) :=
        hPilaBound (s + 1) e (by omega) he heE (R.map A) hpacket
          ((M : ℝ) + 1) hB
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
  have hcomponentsReal : (components.card : ℝ) ≤ E := by
    exact_mod_cast hgeometry.1
  calc
    (points.card : ℝ) ≤
        ∑ R ∈ components, ((componentPoints R).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ _R ∈ components,
        CP * ((M : ℝ) + 1) ^ ((4 : ℝ) + epsilon) := hsum
    _ = (components.card : ℝ) * CP *
        ((M : ℝ) + 1) ^ ((4 : ℝ) + epsilon) := by
      simp [mul_assoc]
    _ ≤ (E : ℝ) * CP *
        ((M : ℝ) + 1) ^ ((4 : ℝ) + epsilon) := by
      gcongr
    _ = C * ((M : ℝ) + 1) ^ ((4 : ℝ) + epsilon) := rfl

end

end TranslatedDepthSeven
