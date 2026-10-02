import TranslatedDepthSeven.RankSevenDegreeOneProperStarQbarReducible
import TranslatedDepthSeven.ProjectiveHilbertCoefficientExtension
import TranslatedDepthSeven.QbarDetectsGeometricPrimeness
import TranslatedDepthSeven.QbarComponentKrullDimension

/-!
# The dimension-two count for a smooth projective star

At a Jacobian-regular direction the whole projective star lies in one
rational codimension-three linear section of the original cone.  This file
counts the literal normalized integral points on that fixed section.

The rational minimal components of the displayed section are used only as a
finite cover.  An occupied rational component has projective dimension at
most two: choose a geometric component above it through the occupied point,
observe that it is an actual component of the same displayed section, and
use exclusion from the depth-seven exceptional locus.  A geometrically
integral rational component is then counted by the normalized projective
Pila estimate.  Otherwise its actual real minimal components are counted
separately; their number is controlled by the additive degree mass under
base change.  Thus no count for a star, a section, or a component family is
assumed.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 16000000

namespace StandardAG

/-- Extension of an integral rational projective cone to `ℝ` is
equidimensional, and its degree is the sum of the degrees of its reduced
real components.

This is flat invariance and additivity of the Hilbert polynomial.  It is
stated for the affine cones because the packet substitution acts on all
homogeneous coordinates.  It contains no lattice-point estimate.

References: Hartshorne, Chapter I, Section 7; Fulton, *Intersection Theory*,
Section 8.4; and the Stacks Project, Tags `00P0` and `01M3`. -/
def HomogeneousPrimeRealConeComponentDegreeMass : Prop :=
  ∀ (N r d : ℕ)
    (Q : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
    Q.IsPrime →
    Q.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
    HasProjectiveDimensionDegree Q r d →
      ∃ componentDegree :
          Ideal (MvPolynomial (Fin (N + 1)) ℝ) → ℕ,
        (∀ R ∈ finiteMinimalPrimes
            (realCoefficientExtensionOfRationalIdeal Q),
          1 ≤ componentDegree R ∧
          HasAffineDimensionDegree R (r + 1) (componentDegree R)) ∧
        ∑ R ∈ finiteMinimalPrimes
            (realCoefficientExtensionOfRationalIdeal Q),
          componentDegree R ≤ d

end StandardAG

/-- The rational ideal of the literal section is homogeneous. -/
theorem rationalLinearSectionIdeal_isHomogeneous
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (hhomogeneous : (finiteEquationIdeal
      (rationalizedEquationFinset equations)).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ))
    {c : ℕ} (D : Matrix (Fin c) (Fin 13) ℚ) :
    (finiteEquationIdeal
      (rationalLinearSectionEquationFinset equations D)).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ) := by
  have hrow : (finiteEquationIdeal
      (rationalMatrixRowLinearEquationFamily D)).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ) := by
    apply Ideal.homogeneous_span
    intro f hf
    rw [Finset.mem_coe, rationalMatrixRowLinearEquationFamily,
      Finset.mem_image] at hf
    obtain ⟨i, _hi, rfl⟩ := hf
    exact ⟨1, rationalMatrixRowLinearPolynomial_isHomogeneous D i⟩
  rw [rationalLinearSectionEquationFinset,
    finiteEquationIdeal_union_rowLinearEquationFamily]
  exact hhomogeneous.sup hrow

/-- Every equation of a rational linear section has degree bounded by the
maximum of one and the degree bound for the original equations. -/
theorem rationalLinearSectionEquation_totalDegree_le
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    {c : ℕ} (D : Matrix (Fin c) (Fin 13) ℚ)
    {g : MvPolynomial (Fin 13) ℚ}
    (hg : g ∈ rationalLinearSectionEquationFinset equations D) :
    g.totalDegree ≤ max 1 (equationFamilyDegreeBound equations) := by
  classical
  rcases Finset.mem_union.mp hg with hg | hg
  · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
    have hmapDegree :
        (MvPolynomial.map (Int.castRingHom ℚ) f).totalDegree =
          f.totalDegree := by
      unfold MvPolynomial.totalDegree
      rw [MvPolynomial.support_map_of_injective _ Int.cast_injective]
    rw [hmapDegree]
    exact (totalDegree_le_equationFamilyDegreeBound hf).trans
      (le_max_right 1 (equationFamilyDegreeBound equations))
  · obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hg
    exact (rationalMatrixRowLinearPolynomial_isHomogeneous D i).totalDegree_le
      |>.trans (le_max_left 1 (equationFamilyDegreeBound equations))

/-- Literal Bezout bounds for the rational minimal-prime list of a linear
section. -/
theorem rationalLinearSection_componentBezoutBounds
    (hBezout : StandardAG.FiniteEquationProjectiveComponentBezoutBounds)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    {c : ℕ} (D : Matrix (Fin c) (Fin 13) ℚ) :
    let E := (max 1
      (max 1 (equationFamilyDegreeBound equations))) ^ 13
    (finiteMinimalPrimes
      (finiteEquationIdeal
        (rationalLinearSectionEquationFinset equations D))).card ≤ E ∧
      ∀ Q ∈ finiteMinimalPrimes
          (finiteEquationIdeal
            (rationalLinearSectionEquationFinset equations D)),
        ∀ r d : ℕ, HasProjectiveDimensionDegree Q r d → d ≤ E := by
  dsimp only
  simpa only [Nat.reduceAdd] using
    hBezout 12
      (rationalLinearSectionEquationFinset equations D)
      (max 1 (equationFamilyDegreeBound equations))
      (fun g hg ↦ rationalLinearSectionEquation_totalDegree_le
        equations D hg)

/-- An integral common zero annihilated by the displayed rows is a rational
zero of the generated section ideal. -/
theorem intCast_mem_rationalLinearSectionIdeal
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    {c : ℕ} (D : Matrix (Fin c) (Fin 13) ℚ)
    (x : IntVector 13) (hzero : IntegralCommonZero equations x)
    (hD : Matrix.mulVec D (fun j ↦ (x j : ℚ)) = 0) :
    (fun j ↦ (x j : ℚ)) ∈ affineIdealZeroLocus
      (finiteEquationIdeal
        (rationalLinearSectionEquationFinset equations D)) := by
  rw [affineIdealZeroLocus_finiteEquationIdeal]
  intro g hg
  rcases Finset.mem_union.mp hg with hg | hg
  · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
    rw [eval_map_intCast, hzero f hf, Int.cast_zero]
  · obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hg
    rw [eval_rationalMatrixRowLinearPolynomial]
    exact congrFun hD i

/-- Minimal components are transitive through coefficient extension: a
minimal component above a rational minimal component of `I` is itself a
minimal component of the extension of `I` to `Qbar`.

The proof is only the minimality argument and faithful-flat contraction; no
geometric theorem is used. -/
theorem qbarMinimalComponent_of_rationalMinimalComponent
    {N : ℕ}
    (I Q : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hQ : Q ∈ finiteMinimalPrimes I)
    (P : Ideal (MvPolynomial (Fin (N + 1)) Qbar))
    (hP : P ∈ finiteMinimalPrimes (qbarCoefficientExtensionIdeal Q)) :
    P ∈ finiteMinimalPrimes
      (I.map (MvPolynomial.map (algebraMap ℚ Qbar))) := by
  have hQmin := (mem_finiteMinimalPrimes_iff I Q).mp hQ
  have hPmin := (mem_finiteMinimalPrimes_iff
    (qbarCoefficientExtensionIdeal Q) P).mp hP
  have hQprime : Q.IsPrime := hQmin.1.1
  have hPprime : P.IsPrime := hPmin.1.1
  have hPcomap :
      P.comap (MvPolynomial.map (algebraMap ℚ Qbar)) = Q :=
    comap_qbar_minimalPrime_map_eq_of_isPrime Q hQprime P hPmin
  apply (mem_finiteMinimalPrimes_iff _ _).mpr
  refine ⟨⟨hPprime, ?_⟩, ?_⟩
  · exact (Ideal.map_mono hQmin.1.2).trans hPmin.1.2
  · intro R hR hRP
    have hIRcomap : I ≤
        R.comap (MvPolynomial.map (algebraMap ℚ Qbar)) := by
      rw [← Ideal.map_le_iff_le_comap]
      exact hR.2
    have hcomapRQ :
        R.comap (MvPolynomial.map (algebraMap ℚ Qbar)) ≤ Q := by
      rw [← hPcomap]
      exact Ideal.comap_mono hRP
    have hQRcomap : Q ≤
        R.comap (MvPolynomial.map (algebraMap ℚ Qbar)) :=
      hQmin.2 ⟨hR.1.comap _, hIRcomap⟩ hcomapRQ
    have hQmapR : qbarCoefficientExtensionIdeal Q ≤ R := by
      rw [qbarCoefficientExtensionIdeal, Ideal.map_le_iff_le_comap]
      exact hQRcomap
    exact hPmin.2 ⟨hR.1, hQmapR⟩ hRP

/-- A rational point of an ideal lies on one actual real minimal component
of its coefficient extension. -/
theorem exists_realMinimalComponent_through_rationalPoint
    {N : ℕ}
    (Q : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (x : Fin (N + 1) → ℚ) (hx : x ∈ affineIdealZeroLocus Q) :
    ∃ R ∈ finiteMinimalPrimes
        (realCoefficientExtensionOfRationalIdeal Q),
      (fun i ↦ algebraMap ℚ ℝ (x i)) ∈ affineIdealZeroLocus R := by
  let xr : Fin (N + 1) → ℝ := fun i ↦ algebraMap ℚ ℝ (x i)
  let T : Ideal (MvPolynomial (Fin (N + 1)) ℝ) :=
    RingHom.ker (MvPolynomial.eval xr)
  letI : T.IsPrime := RingHom.ker_isPrime _
  have hQT : realCoefficientExtensionOfRationalIdeal Q ≤ T := by
    rw [realCoefficientExtensionOfRationalIdeal, Ideal.map_le_iff_le_comap]
    intro f hf
    apply RingHom.mem_ker.mpr
    change MvPolynomial.eval xr
      (MvPolynomial.map (algebraMap ℚ ℝ) f) = 0
    rw [show xr = fun i ↦ algebraMap ℚ ℝ (x i) from rfl,
      eval_realCoefficientExtension_at_rationalPoint]
    rw [hx f hf, map_zero]
  obtain ⟨R, hR, hRT⟩ := exists_finiteMinimalPrime_le hQT
  refine ⟨R, hR, ?_⟩
  rw [mem_affineIdealZeroLocus_iff]
  exact hRT

/-- An occupied rational minimal component of a normalized codimension-three
section has projective dimension at most two.  The only geometric input is
equidimensionality of a prime after coefficient extension.  All incidence
and minimal-component assertions are proved for the literal ideals. -/
theorem rationalLinearSection_occupiedMinimalPrime_dimension_le_two
    (hHilbert : StandardAG.ProjectiveHilbertDegreeCertification ℚ)
    (hHilbertQbar : StandardAG.ProjectiveHilbertDegreeCertification Qbar)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (hhomogeneous : (finiteEquationIdeal
      (rationalizedEquationFinset equations)).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ))
    (D : Matrix (Fin 3) (Fin 13) ℚ) (hDrank : D.rank = 3)
    (hDheight : rationalProjectiveLinearHeight D ≤ ⌈p.H ^ CF⌉₊)
    {z : IntVector 13}
    (hz : z ∈ depthSevenNormalizedDisplacementFinset
      p x₀ equations CF)
    (hDpoint : Matrix.mulVec D
      (fun j ↦ (integralAffineMap x₀ z p.m j : ℚ)) = 0)
    (Q : Ideal (MvPolynomial (Fin 13) ℚ))
    (hQ : Q ∈ finiteMinimalPrimes
      (finiteEquationIdeal
        (rationalLinearSectionEquationFinset equations D)))
    (hxQ : (fun j ↦ (integralAffineMap x₀ z p.m j : ℚ)) ∈
      affineIdealZeroLocus Q) :
    ∃ r d : ℕ,
      HasProjectiveDimensionDegree Q r d ∧ r ≤ 2 := by
  classical
  have hzdata := (Finset.mem_filter.mp hz).2
  dsimp only at hzdata
  obtain ⟨_hbox, _hzero, hxne, _hnonlinear, hnotExceptional⟩ := hzdata
  let xInt : IntVector 13 := integralAffineMap x₀ z p.m
  let x : Fin 13 → ℚ := fun j ↦ (xInt j : ℚ)
  have hxneQ : x ≠ 0 := by
    exact intCast_ne_zero hxne
  have hQprime : Q.IsPrime := isPrime_of_mem_finiteMinimalPrimes hQ
  have hQhomogeneous : Q.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ) := by
    apply isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous
      (rationalLinearSectionIdeal_isHomogeneous
        equations hhomogeneous D)
    exact (mem_finiteMinimalPrimes_iff _ _).mp hQ
  have hirrelevant : ¬ projectiveIrrelevantIdeal ℚ 12 ≤ Q := by
    intro hirr
    apply hxneQ
    exact eq_zero_of_mem_affineIdealZeroLocus_of_irrelevant_le
      hirr (by simpa only [x, xInt] using hxQ)
  obtain ⟨r, d, _P, hQcertificate⟩ :=
    hHilbert 12 Q hQprime hQhomogeneous hirrelevant
  have hQprojective : HasProjectiveDimensionDegree Q r d :=
    hQcertificate.toPublished
  let xbar : Fin 13 → Qbar := fun j ↦ algebraMap ℚ Qbar (x j)
  have hxbarQ : xbar ∈ affineIdealZeroLocus
      (qbarCoefficientExtensionIdeal Q) := by
    apply (rational_zero_of_ideal_iff_qbar_zero_of_extension
      Q (qbarCoefficientExtensionIdeal Q) rfl x).mp
    simpa only [x, xInt] using hxQ
  let T : Ideal (MvPolynomial (Fin 13) Qbar) :=
    RingHom.ker (MvPolynomial.eval xbar)
  letI : T.IsPrime := RingHom.ker_isPrime _
  have hQbarT : qbarCoefficientExtensionIdeal Q ≤ T := by
    rw [mem_affineIdealZeroLocus_iff] at hxbarQ
    exact hxbarQ
  obtain ⟨P, hP, hPT⟩ := exists_finiteMinimalPrime_le hQbarT
  have hPsection : P ∈ finiteMinimalPrimes
      ((finiteEquationIdeal
        (rationalLinearSectionEquationFinset equations D)).map
          (MvPolynomial.map (algebraMap ℚ Qbar))) :=
    qbarMinimalComponent_of_rationalMinimalComponent
      (finiteEquationIdeal
        (rationalLinearSectionEquationFinset equations D)) Q hQ P hP
  have hPgeometric : P ∈ finiteEquationMinimalPrimes
      (geometricLinearSectionEquationFinset equations D) := by
    rw [mem_finiteEquationMinimalPrimes_iff,
      geometricLinearSectionIdeal_eq_map_rationalLinearSectionIdeal]
    exact (mem_finiteMinimalPrimes_iff _ _).mp hPsection
  have hPhomogeneous : P.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 13) Qbar) :=
    qbarMinimalComponent_isHomogeneous Q hQhomogeneous P hP
  have hxbarP : xbar ∈ affineIdealZeroLocus P := by
    rw [mem_affineIdealZeroLocus_iff]
    exact hPT
  have hPirrelevant : ¬ geometricIrrelevantCoordinateIdeal 13 ≤ P := by
    intro hirr
    apply hxne
    funext j
    have hX : MvPolynomial.X j ∈ P := by
      apply hirr
      exact Ideal.subset_span (Set.mem_range_self j)
    have heval := hxbarP (MvPolynomial.X j) hX
    have hcast : algebraMap ℚ Qbar (x j) = 0 := by
      simpa [xbar] using heval
    have hrat : x j = 0 :=
      (map_eq_zero_iff (algebraMap ℚ Qbar)
        (FaithfulSMul.algebraMap_injective ℚ Qbar)).mp hcast
    have hrat' : (xInt j : ℚ) = 0 := by simpa only [x] using hrat
    exact_mod_cast hrat'
  have hPcomponent : IsProjectiveSectionComponent equations D P :=
    ⟨hPgeometric, hPirrelevant⟩
  have hxProjective : ProjectivePointVanishesOnGeometricIdeal P
      (integralProjectiveClass xInt hxne) := by
    let xrat : Fin 13 → ℚ := fun j ↦ (xInt j : ℚ)
    have hxrat : xrat ≠ 0 := intCast_ne_zero hxne
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep
      ℚ xrat hxrat
    have ha' : a • xrat = (integralProjectiveClass xInt hxne).rep := by
      simpa only [integralProjectiveClass, xrat] using ha
    have hscaled := smul_mem_affineIdealZeroLocus_of_isHomogeneous
      P hPhomogeneous (by simpa only [xbar, x, xInt, xrat] using hxbarP)
        (algebraMap ℚ Qbar (a : ℚ))
    have hrep : (fun i ↦ algebraMap ℚ Qbar
        ((integralProjectiveClass xInt hxne).rep i)) =
        fun i ↦ algebraMap ℚ Qbar (a : ℚ) * xbar i := by
      funext i
      have hi := congrFun ha' i
      change algebraMap ℚ Qbar
          ((integralProjectiveClass xInt hxne).rep i) = _
      rw [← hi]
      change algebraMap ℚ Qbar ((a : ℚ) * (xInt i : ℚ)) =
        algebraMap ℚ Qbar (a : ℚ) *
          algebraMap ℚ Qbar (xInt i : ℚ)
      exact map_mul (algebraMap ℚ Qbar) _ _
    rw [ProjectivePointVanishesOnGeometricIdeal, hrep]
    exact hscaled
  have hPprime : P.IsPrime := isPrime_of_mem_finiteMinimalPrimes hP
  obtain ⟨rP, e, _polynomial, hPcertificate⟩ :=
    hHilbertQbar 12 P hPprime hPhomogeneous (by
      simpa only [projectiveIrrelevantIdeal,
        geometricIrrelevantCoordinateIdeal, Nat.reduceAdd] using
          hPirrelevant)
  have hPprojective : HasProjectiveDimensionDegree P rP e :=
    hPcertificate.toPublished
  have hdimEq : ringKrullDim (MvPolynomial (Fin 13) Qbar ⧸ P) =
      ringKrullDim (MvPolynomial (Fin 13) ℚ ⧸ Q) :=
    qbar_minimalComponent_ringKrullDim_eq Q hQprime P hP
  have hrsucc : rP + 1 = r + 1 := by
    exact_mod_cast hPprojective.1.symm.trans (hdimEq.trans hQprojective.1)
  have hrP : rP = r := by omega
  subst rP
  have hr : r ≤ 2 :=
    (codimensionThree_component_dimension_degree_of_not_exceptional
      equations ⌈p.H ^ CF⌉₊ D hDrank hDheight P hPcomponent
      (integralProjectiveClass xInt hxne) hxProjective hnotExceptional
      (by simpa only [HasGeometricProjectiveDimensionDegree] using
        hPprojective)).1
  exact ⟨r, d, hQprojective, hr⟩

/-- Pila on the actual real minimal components of a rational projective
prime of projective dimension at most two.  The finite cover and its
cardinality bound are derived from the displayed degree mass. -/
theorem exists_uniform_projectiveAtMostTwo_realComponentPilaBound
    (hPila : Pila1995TheoremA)
    (hRealMass : StandardAG.HomogeneousPrimeRealConeComponentDegreeMass)
    (N D : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
        (r d m M : ℕ),
        Q.IsPrime →
        Q.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
        HasProjectiveDimensionDegree Q r d →
        r ≤ 2 → d ≤ D → 0 < m → 1 ≤ M →
        ∀ (x₀ : IntVector (N + 1))
          (points : Finset (IntVector (N + 1))),
          (∀ z ∈ points, ∀ i, (z i).natAbs ≤ M) →
          (∀ z ∈ points,
            (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
              affineIdealZeroLocus Q) →
          (points.card : ℝ) ≤
            C * ((M : ℝ) + 1) ^ ((3 : ℝ) + epsilon) := by
  classical
  obtain ⟨CP, hCP, hPilaBound⟩ :=
    pila1995_hilbertDimensionAtMost_boundedDegree
      hPila (N + 1) 3 D epsilon hepsilon
  let C : ℝ := (max 1 D : ℕ) * CP
  refine ⟨C, mul_pos (by positivity) hCP, ?_⟩
  intro Q r d m M hQprime hQhom hQprojective hr hdD hm hM
    x₀ points hbox hzero
  obtain ⟨componentDegree, hcomponents, hmass⟩ :=
    hRealMass N r d Q hQprime hQhom hQprojective
  let components := finiteMinimalPrimes
    (realCoefficientExtensionOfRationalIdeal Q)
  let componentPoints :=
    fun R : Ideal (MvPolynomial (Fin (N + 1)) ℝ) ↦
      points.filter fun z ↦
        (fun i ↦ (integralAffineMap x₀ z m i : ℝ)) ∈
          affineIdealZeroLocus R
  have hcover : points ⊆ components.biUnion componentPoints := by
    intro z hz
    let x : Fin (N + 1) → ℚ :=
      fun i ↦ (integralAffineMap x₀ z m i : ℚ)
    obtain ⟨R, hR, hxR⟩ :=
      exists_realMinimalComponent_through_rationalPoint Q x (hzero z hz)
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
        CP * ((M : ℝ) + 1) ^ ((3 : ℝ) + epsilon) := by
    intro R hR
    have hRdata := hcomponents R (by simpa only [components] using hR)
    have heD : componentDegree R ≤ D := by
      exact ((Finset.single_le_sum
        (fun S _hS ↦ Nat.zero_le (componentDegree S))
        (by simpa only [components] using hR)).trans hmass).trans hdD
    let A := affinePolynomialChangeAlgEquiv
      (fun i ↦ (x₀ i : ℝ)) (m : ℝ) (by exact_mod_cast hm.ne')
    have hpacket : HasAffineHilbertDimensionDegree
        (R.map A) (r + 1) (componentDegree R) :=
      (hasAffineHilbertDimensionDegree_map_affinePolynomialChange_iff
        R (fun i ↦ (x₀ i : ℝ)) (m : ℝ)
          (by exact_mod_cast hm.ne') (r + 1) (componentDegree R)).2
        hRdata.2.toHilbert
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
          hm R x₀ z hzdata.2
    calc
      ((componentPoints R).card : ℝ) ≤
          ((pilaIntegralPoints (R.map A) ((M : ℝ) + 1)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
      _ ≤ CP * ((M : ℝ) + 1) ^ ((3 : ℝ) + epsilon) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          hPilaBound (r + 1) (componentDegree R) (by omega)
            hRdata.1 heD (R.map A) hpacket ((M : ℝ) + 1) hB
  have hcomponentCount : components.card ≤ D := by
    calc
      components.card ≤
          ∑ R ∈ components, componentDegree R := by
        exact Finset.card_le_of_sum_positive_mass components componentDegree
          (∑ R ∈ components, componentDegree R)
          (fun R hR ↦
            (hcomponents R (by simpa only [components] using hR)).1)
          le_rfl
      _ ≤ d := by simpa only [components] using hmass
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
          CP * ((M : ℝ) + 1) ^ ((3 : ℝ) + epsilon) := by
    exact Finset.sum_le_sum fun R hR ↦ hcomponent R hR
  have hcountReal : (components.card : ℝ) ≤ (max 1 D : ℕ) := by
    exact_mod_cast hcomponentCount.trans (Nat.le_max_right 1 D)
  calc
    (points.card : ℝ) ≤
        ∑ R ∈ components, ((componentPoints R).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ _R ∈ components,
        CP * ((M : ℝ) + 1) ^ ((3 : ℝ) + epsilon) := hsum
    _ = (components.card : ℝ) * CP *
        ((M : ℝ) + 1) ^ ((3 : ℝ) + epsilon) := by
      simp [mul_assoc]
    _ ≤ (max 1 D : ℕ) * CP *
        ((M : ℝ) + 1) ^ ((3 : ℝ) + epsilon) := by
      gcongr
    _ = C * ((M : ℝ) + 1) ^ ((3 : ℝ) + epsilon) := rfl

/-- Coefficient-uniform `3 + epsilon` bound for normalized integral points
on one literal bounded-height codimension-three section.  The finite covers
are the actual minimal-prime lists of the displayed rational section and of
the real coefficient extensions of its rational components. -/
theorem exists_uniform_normalizedCodimensionThreeSection_pilaBound
    (hPila : Pila1995TheoremA)
    (hRealMass : StandardAG.HomogeneousPrimeRealConeComponentDegreeMass)
    (hHilbert : StandardAG.ProjectiveHilbertDegreeCertification ℚ)
    (hHilbertQbar : StandardAG.ProjectiveHilbertDegreeCertification Qbar)
    (hBezout : StandardAG.FiniteEquationProjectiveComponentBezoutBounds)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (hhomogeneous : (finiteEquationIdeal
      (rationalizedEquationFinset equations)).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (CF : ℕ) (p : Parameters) (x₀ : IntVector 13)
        (D : Matrix (Fin 3) (Fin 13) ℚ),
        D.rank = 3 →
        rationalProjectiveLinearHeight D ≤ ⌈p.H ^ CF⌉₊ →
        ∀ (M : ℕ), 1 ≤ M →
        ∀ (points : Finset (IntVector 13)),
          points ⊆ depthSevenNormalizedDisplacementFinset
            p x₀ equations CF →
          (∀ z ∈ points, ∀ i, (z i).natAbs ≤ M) →
          (∀ z ∈ points, Matrix.mulVec D
            (fun j ↦ (integralAffineMap x₀ z p.m j : ℚ)) = 0) →
          (points.card : ℝ) ≤
            C * ((M : ℝ) + 1) ^ ((3 : ℝ) + epsilon) := by
  classical
  let E : ℕ := (max 1
    (max 1 (equationFamilyDegreeBound equations))) ^ 13
  have hE : 1 ≤ E := one_le_pow₀ (Nat.le_max_left _ _)
  obtain ⟨CP, hCP, hPrimeBound⟩ :=
    exists_uniform_normalizedProjectiveAtMost_pilaBound
      hPila 12 2 E epsilon hepsilon
  obtain ⟨CR, hCR, hRealBound⟩ :=
    exists_uniform_projectiveAtMostTwo_realComponentPilaBound
      hPila hRealMass 12 E epsilon hepsilon
  let C₀ : ℝ := CP + CR
  let C : ℝ := (E : ℝ) * C₀
  have hC₀ : 0 < C₀ := by
    dsimp only [C₀]
    linarith
  refine ⟨C, mul_pos (by exact_mod_cast hE) hC₀, ?_⟩
  intro CF p x₀ D hDrank hDheight M hM points hnormalized hbox hDpoint
  let sectionIdeal := finiteEquationIdeal
    (rationalLinearSectionEquationFinset equations D)
  let components := finiteMinimalPrimes sectionIdeal
  let componentPoints := fun Q : Ideal (MvPolynomial (Fin 13) ℚ) ↦
    points.filter fun z ↦
      (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
        affineIdealZeroLocus Q
  have hsectionBounds : components.card ≤ E ∧
      ∀ Q ∈ components, ∀ r d : ℕ,
        HasProjectiveDimensionDegree Q r d → d ≤ E := by
    simpa only [components, sectionIdeal, E] using
      rationalLinearSection_componentBezoutBounds hBezout equations D
  have hcover : points ⊆ components.biUnion componentPoints := by
    intro z hz
    have hzNormalized := hnormalized hz
    have hzdata := (Finset.mem_filter.mp hzNormalized).2
    dsimp only at hzdata
    obtain ⟨_hzbox, hzero, _hxne, _hnonlinear, _hnot⟩ := hzdata
    let x : Fin 13 → ℚ :=
      fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)
    let T : Ideal (MvPolynomial (Fin 13) ℚ) :=
      RingHom.ker (MvPolynomial.eval x)
    letI : T.IsPrime := RingHom.ker_isPrime _
    have hsectionT : sectionIdeal ≤ T := by
      have hxsection := intCast_mem_rationalLinearSectionIdeal
        equations D (integralAffineMap x₀ z p.m) hzero (hDpoint z hz)
      rw [mem_affineIdealZeroLocus_iff] at hxsection
      simpa only [sectionIdeal, x] using hxsection
    obtain ⟨Q, hQ, hQT⟩ := exists_finiteMinimalPrime_le hsectionT
    refine Finset.mem_biUnion.mpr ⟨Q, ?_, ?_⟩
    · simpa only [components] using hQ
    · rw [Finset.mem_filter]
      refine ⟨hz, ?_⟩
      rw [mem_affineIdealZeroLocus_iff]
      simpa only [x] using hQT
  have hcomponent : ∀ Q ∈ components,
      ((componentPoints Q).card : ℝ) ≤
        C₀ * ((M : ℝ) + 1) ^ ((3 : ℝ) + epsilon) := by
    intro Q hQ
    by_cases hempty : componentPoints Q = ∅
    · simp [hempty]
      positivity
    · obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      have hzdata := Finset.mem_filter.mp hz
      have hzNormalized := hnormalized hzdata.1
      have hxQ := hzdata.2
      obtain ⟨r, d, hQprojective, hr⟩ :=
        rationalLinearSection_occupiedMinimalPrime_dimension_le_two
          hHilbert hHilbertQbar p x₀ equations CF hhomogeneous
            D hDrank hDheight hzNormalized (hDpoint z hzdata.1) Q
            (by simpa only [components, sectionIdeal] using hQ) hxQ
      have hdE := hsectionBounds.2 Q hQ r d hQprojective
      have hQprime : Q.IsPrime := isPrime_of_mem_finiteMinimalPrimes
        (by simpa only [components, sectionIdeal] using hQ)
      have hQhomogeneous : Q.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ) := by
        apply isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous
          (rationalLinearSectionIdeal_isHomogeneous
            equations hhomogeneous D)
        exact (mem_finiteMinimalPrimes_iff _ _).mp
          (by simpa only [components, sectionIdeal] using hQ)
      have hcellBox : ∀ w ∈ componentPoints Q, ∀ i,
          (w i).natAbs ≤ M := by
        intro w hw i
        exact hbox w (Finset.mem_filter.mp hw).1 i
      have hcellZero : ∀ w ∈ componentPoints Q,
          (fun i ↦ (integralAffineMap x₀ w p.m i : ℚ)) ∈
            affineIdealZeroLocus Q := by
        intro w hw
        exact (Finset.mem_filter.mp hw).2
      by_cases hgeom : (qbarCoefficientExtensionIdeal Q).IsPrime
      · have hraw := hPrimeBound r d p.m M hr hdE hM p.hm Q
          hQhomogeneous
          (geometricallyPrime_of_qbarCoefficientExtension_isPrime Q hgeom)
          hQprojective x₀ (componentPoints Q) hcellBox hcellZero
        have hraw' : ((componentPoints Q).card : ℝ) ≤
            CP * ((M : ℝ) + 1) ^ ((3 : ℝ) + epsilon) := by
          convert hraw using 1 <;> norm_num
        exact hraw'.trans (mul_le_mul_of_nonneg_right
          (show CP ≤ C₀ by dsimp only [C₀]; linarith)
          (Real.rpow_nonneg (by positivity) _))
      · have hraw := hRealBound Q r d p.m M hQprime hQhomogeneous
          hQprojective hr hdE p.hm hM x₀ (componentPoints Q)
            hcellBox hcellZero
        exact hraw.trans (mul_le_mul_of_nonneg_right
          (show CR ≤ C₀ by dsimp only [C₀]; linarith)
          (Real.rpow_nonneg (by positivity) _))
  have hcard : points.card ≤
      ∑ Q ∈ components, (componentPoints Q).card := by
    calc
      points.card ≤ (components.biUnion componentPoints).card :=
        Finset.card_le_card hcover
      _ ≤ ∑ Q ∈ components, (componentPoints Q).card :=
        Finset.card_biUnion_le
  have hsum :
      (∑ Q ∈ components, ((componentPoints Q).card : ℝ)) ≤
        ∑ _Q ∈ components,
          C₀ * ((M : ℝ) + 1) ^ ((3 : ℝ) + epsilon) := by
    exact Finset.sum_le_sum fun Q hQ ↦ hcomponent Q hQ
  have hcomponentsReal : (components.card : ℝ) ≤ E := by
    exact_mod_cast hsectionBounds.1
  calc
    (points.card : ℝ) ≤
        ∑ Q ∈ components, ((componentPoints Q).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ _Q ∈ components,
        C₀ * ((M : ℝ) + 1) ^ ((3 : ℝ) + epsilon) := hsum
    _ = (components.card : ℝ) * C₀ *
        ((M : ℝ) + 1) ^ ((3 : ℝ) + epsilon) := by
      simp [mul_assoc]
    _ ≤ (E : ℝ) * C₀ *
        ((M : ℝ) + 1) ^ ((3 : ℝ) + epsilon) := by
      gcongr
    _ = C * ((M : ℝ) + 1) ^ ((3 : ℝ) + epsilon) := rfl

/-- The smooth-star specialization.  The Jacobian section is selected once
from the centre `h`, before any point is considered.  The explicit height
premise is the only place where a downstream direction-height estimate is
needed. -/
theorem exists_uniform_normalizedSmoothProjectiveStar_pilaBound
    (hPila : Pila1995TheoremA)
    (hRealMass : StandardAG.HomogeneousPrimeRealConeComponentDegreeMass)
    (hHilbert : StandardAG.ProjectiveHilbertDegreeCertification ℚ)
    (hHilbertQbar : StandardAG.ProjectiveHilbertDegreeCertification Qbar)
    (hBezout : StandardAG.FiniteEquationProjectiveComponentBezoutBounds)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (degree : MvPolynomial (Fin 13) ℤ → ℕ)
    (hdegree : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    (hhomogeneous : (finiteEquationIdeal
      (rationalizedEquationFinset equations)).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (CF : ℕ) (p : Parameters) (x₀ h : IntVector 13),
        IsDepthSevenJacobianRegularAt equations h →
        Nat.factorial 3 *
          (equationFamilySupportBound equations *
            equationFamilyDegreeBound equations *
            equationFamilyCoefficientBound equations *
            max 1 (directionHeight h) ^
              equationFamilyDegreeBound equations) ^ 3 ≤ ⌈p.H ^ CF⌉₊ →
        ∀ (M : ℕ), 1 ≤ M →
        ∀ (points : Finset (IntVector 13)),
          points ⊆ depthSevenNormalizedDisplacementFinset
            p x₀ equations CF →
          (∀ z ∈ points, ∀ i, (z i).natAbs ≤ M) →
          (∀ z ∈ points,
            ∃ hx : integralAffineMap x₀ z p.m ≠ 0,
              integralProjectiveClass (integralAffineMap x₀ z p.m) hx ∈
                integralProjectiveStarLocus equations degree h) →
          (points.card : ℝ) ≤
            C * ((M : ℝ) + 1) ^ ((3 : ℝ) + epsilon) := by
  obtain ⟨C, hC, hsectionBound⟩ :=
    exists_uniform_normalizedCodimensionThreeSection_pilaBound
      hPila hRealMass hHilbert hHilbertQbar hBezout equations
        hhomogeneous epsilon hepsilon
  refine ⟨C, hC, ?_⟩
  intro CF p x₀ h hregular hheight M hM points hnormalized hbox hstar
  obtain ⟨D, hDrank, hDraw, hDstar⟩ :=
    exists_threeRowSection_containing_projectiveStar
      equations degree hdegree h hregular
  apply hsectionBound CF p x₀ D hDrank (hDraw.trans hheight)
    M hM points hnormalized hbox
  intro z hz
  obtain ⟨hx, hxstar⟩ := hstar z hz
  have hxQ : (fun j ↦ (integralAffineMap x₀ z p.m j : ℚ)) ≠ 0 :=
    intCast_ne_zero hx
  exact hDstar _ hxQ (by
    simpa only [integralProjectiveClass] using hxstar)

end

end TranslatedDepthSeven
