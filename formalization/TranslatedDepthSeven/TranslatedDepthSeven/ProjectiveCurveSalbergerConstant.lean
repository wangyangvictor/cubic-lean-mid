import TranslatedDepthSeven.RankSevenSalbergerPilaTerminal
import TranslatedDepthSeven.SquarefreeRpow

/-!
# A constant bound for one smooth composite-modulus curve packet

Salberger's 2007 Corollary 3.7 applies to an arbitrary reduced
equidimensional projective scheme, not only to a hypersurface.  In projective
dimension one and at multiplicity-one residue points, its several-prime
factor is exactly `q ^ degree`.  The auxiliary form therefore cuts a fixed
integral curve in boundedly many points by Bezout.

This file keeps those two inputs separate and literal.  The only new
algebraic-geometric boundary is the reduced first-chart form of the
curve--hypersurface Bezout theorem.  It contains no packet or point-counting
conclusion.  Everything after that input, including the cardinal injection
and the specialization of the several-prime product, is proved in Lean.

Reference for the determinant step: P. Salberger, *On the Density of
Rational and Integral Points on Algebraic Varieties*, J. reine angew. Math.
606 (2007), Corollary 3.7 and formula (3.8), p. 132 of the journal version
(p. 9 of arXiv:math/0508326).  The curve-plus-Bezout use is made explicitly
in the proof of Lemma 4.3 on the following page.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

local instance projectiveCurveSalbergerConstantPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-! ## The reduced rational first chart -/

/-- The first affine chart of a rational homogeneous ideal, retained in
homogeneous coordinates by adjoining `X₀ - 1` and then reducing. -/
def rationalFirstAffineChartReducedIdeal {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) :
    Ideal (MvPolynomial (Fin (N + 1)) ℚ) :=
  (I ⊔ Ideal.span
    ({X 0 - C 1} : Set (MvPolynomial (Fin (N + 1)) ℚ))).radical

namespace StandardAG

/-- Reduced first-chart Bezout for one integral projective curve and a
homogeneous form which does not contain it.  The displayed spanning family
is the coordinate-algebra form of the degree/length bound `d * k`.

This is the hypersurface case of projective Bezout (Hartshorne I.7.7, or
Fulton, *Intersection Theory*, Example 8.4.6), followed by passage to the
reduced standard affine chart. -/
def RationalProjectiveCurveAuxiliaryFirstChartBezout : Prop :=
  ∀ (N d k : ℕ)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (G : MvPolynomial (Fin (N + 1)) ℚ),
    I.IsPrime →
    I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
    HasProjectiveDimensionDegree I 1 d →
    G.IsHomogeneous k →
    G ∉ I →
      ∃ spanningFamily : Fin (d * k) →
          (MvPolynomial (Fin (N + 1)) ℚ ⧸
            rationalFirstAffineChartReducedIdeal
              (I ⊔ Ideal.span ({G} : Set _))),
        Submodule.span ℚ (Set.range spanningFamily) = ⊤

end StandardAG

/-- The normalized rational affine-chart representative of an integral
affine point. -/
def rationalIntegralAffineChartPoint {N : ℕ} (z : IntVector N) :
    Fin (N + 1) → ℚ :=
  fun i ↦ (integralAffineChartVector z i : ℚ)

@[simp]
theorem rationalIntegralAffineChartPoint_zero {N : ℕ} (z : IntVector N) :
    rationalIntegralAffineChartPoint z 0 = 1 := rfl

@[simp]
theorem rationalIntegralAffineChartPoint_succ {N : ℕ}
    (z : IntVector N) (i : Fin N) :
    rationalIntegralAffineChartPoint z i.succ = z i := by
  simp [rationalIntegralAffineChartPoint]

theorem rationalIntegralAffineChartPoint_injective {N : ℕ} :
    Function.Injective
      (rationalIntegralAffineChartPoint : IntVector N → Fin (N + 1) → ℚ) := by
  intro z w hzw
  funext i
  have hi := congrFun hzw i.succ
  simp only [rationalIntegralAffineChartPoint_succ] at hi
  exact_mod_cast hi

/-- A normalized affine point on an ideal annihilates the radical of its
literal first-chart ideal. -/
theorem rationalIntegralAffineChartPoint_mem_firstChartReducedIdeal
    {N : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (z : IntVector N)
    (hz : rationalIntegralAffineChartPoint z ∈ affineIdealZeroLocus I) :
    rationalIntegralAffineChartPoint z ∈
      affineIdealZeroLocus (rationalFirstAffineChartReducedIdeal I) := by
  rw [mem_affineIdealZeroLocus_iff_le_ker_aeval]
  apply (RingHom.ker_isPrime
    (MvPolynomial.eval (rationalIntegralAffineChartPoint z))).radical_le_iff.mpr
  apply sup_le
  · rw [mem_affineIdealZeroLocus_iff_le_ker_aeval] at hz
    exact hz
  · rw [Ideal.span_le]
    intro f hf
    simp only [Set.mem_singleton_iff] at hf
    subst f
    change MvPolynomial.aeval
      (rationalIntegralAffineChartPoint z) (X 0 - C 1) = 0
    simp [rationalIntegralAffineChartPoint]

/-- A displayed `D`-element spanning family for the reduced first-chart
coordinate algebra bounds any finite collection of normalized integral
points on that chart by `D`. -/
theorem card_le_of_rationalIntegralAffineChartPoints_mem_of_span
    {N : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (S : Finset (IntVector N)) (D : ℕ)
    (hzero : ∀ z ∈ S,
      rationalIntegralAffineChartPoint z ∈ affineIdealZeroLocus I)
    (spanningFamily : Fin D →
      (MvPolynomial (Fin (N + 1)) ℚ ⧸
        rationalFirstAffineChartReducedIdeal I))
    (hspan : Submodule.span ℚ (Set.range spanningFamily) = ⊤) :
    S.card ≤ D := by
  classical
  let A := MvPolynomial (Fin (N + 1)) ℚ ⧸
    rationalFirstAffineChartReducedIdeal I
  let pointHom : {z // z ∈ S} → (A →ₐ[ℚ] ℚ) := fun z ↦
    affineIdealPointToQuotientAlgHom (rationalFirstAffineChartReducedIdeal I)
      ⟨rationalIntegralAffineChartPoint z.1,
        rationalIntegralAffineChartPoint_mem_firstChartReducedIdeal
          I z.1 (hzero z.1 z.2)⟩
  have hinjective : Function.Injective pointHom := by
    intro z w hzw
    apply Subtype.ext
    apply rationalIntegralAffineChartPoint_injective
    dsimp only [pointHom] at hzw
    have hpoint :
        (⟨rationalIntegralAffineChartPoint z.1,
          rationalIntegralAffineChartPoint_mem_firstChartReducedIdeal
            I z.1 (hzero z.1 z.2)⟩ :
          {x // x ∈ affineIdealZeroLocus
            (rationalFirstAffineChartReducedIdeal I)}) =
        ⟨rationalIntegralAffineChartPoint w.1,
          rationalIntegralAffineChartPoint_mem_firstChartReducedIdeal
            I w.1 (hzero w.1 w.2)⟩ :=
      (affineIdealZeroLocusEquivQuotientAlgHom
        (rationalFirstAffineChartReducedIdeal I)).injective hzw
    exact congrArg (fun x ↦ x.1) hpoint
  have hfiniteA : Module.Finite ℚ A := Module.finite_def.mpr <|
    Submodule.fg_iff_exists_fin_generating_family.mpr
      ⟨D, spanningFamily, hspan⟩
  letI : Module.Finite ℚ A := hfiniteA
  calc
    S.card = Nat.card {z // z ∈ S} := by simp
    _ ≤ Nat.card (A →ₐ[ℚ] ℚ) :=
      Nat.card_le_card_of_injective pointHom hinjective
    _ ≤ Module.finrank ℚ A := card_algHom_le_finrank ℚ A ℚ
    _ ≤ D := by
      simpa [A] using finrank_le_of_span_eq_top hspan

/-- The reduced curve--hypersurface Bezout input, followed by the preceding
kernel count. -/
theorem card_integralAffinePoints_on_projectiveCurve_auxiliary_le
    (hBezout : StandardAG.RationalProjectiveCurveAuxiliaryFirstChartBezout)
    {N d k : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (G : MvPolynomial (Fin (N + 1)) ℚ)
    (hIprime : I.IsPrime)
    (hIhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hIdegree : HasProjectiveDimensionDegree I 1 d)
    (hGhomogeneous : G.IsHomogeneous k)
    (hGnot : G ∉ I)
    (S : Finset (IntVector N))
    (hIzero : ∀ z ∈ S, ∀ f ∈ I,
      MvPolynomial.eval (rationalIntegralAffineChartPoint z) f = 0)
    (hGzero : ∀ z ∈ S,
      MvPolynomial.eval (rationalIntegralAffineChartPoint z) G = 0) :
    S.card ≤ d * k := by
  obtain ⟨spanningFamily, hspan⟩ :=
    hBezout N d k I G hIprime hIhomogeneous hIdegree
      hGhomogeneous hGnot
  apply card_le_of_rationalIntegralAffineChartPoints_mem_of_span
    (I ⊔ Ideal.span ({G} : Set _)) S (d * k) _ spanningFamily hspan
  intro z hz
  rw [mem_affineIdealZeroLocus_iff_le_ker_aeval]
  apply sup_le
  · intro f hf
    exact RingHom.mem_ker.mpr (hIzero z hz f hf)
  · rw [Ideal.span_le]
    intro f hf
    simp only [Set.mem_singleton_iff] at hf
    subst f
    exact RingHom.mem_ker.mpr (hGzero z hz)

/-! ## Salberger followed by Bezout -/

/-- Exact constant bound for one integral affine packet on a rational
integral projective curve.  The constant `K` is chosen before the curve,
the primes, the residue points and the packet. -/
theorem exists_uniform_projectiveCurve_packet_card_le_degree_mul_salberger
    (hSalberger : Salberger2007Corollary37)
    (hBezout : StandardAG.RationalProjectiveCurveAuxiliaryFirstChartBezout)
    (N d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ,
      ∀ (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
        I.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
        I.IsPrime →
        ¬ projectiveIrrelevantIdeal ℚ N ≤ I →
        HasProjectiveDimensionDegree I 1 d →
        X (0 : Fin (N + 1)) ∉ I →
        ∀ (B : ℝ), 1 ≤ B →
        ∀ (index : Type) (_ : Fintype index),
        ∀ (prime : index → ℕ) (hprime : ∀ i, (prime i).Prime),
          Function.Injective prime →
        ∀ (point : ∀ i, Fin (N + 1) → ZMod (prime i)),
          (∀ i, point i 0 ≠ 0) →
          (∀ i, HasHilbertSamuelMultiplicityAt (hprime i)
            (projectiveSpecialFiberIdeal I) (point i) 1 1) →
          B ^ (1 + ε) ≤
            ∏ i, (prime i : ℝ) ^
              (((d : ℝ) / (1 : ℝ)) ^ ((1 : ℝ)⁻¹)) →
        ∀ (S : Finset (IntVector N)),
          (∀ z ∈ S, ∀ i, |(z i : ℝ)| ≤ B) →
          (∀ z ∈ S, ∀ f ∈ I,
            MvPolynomial.eval (rationalIntegralAffineChartPoint z) f = 0) →
          (∀ z ∈ S, ∀ j i,
            (z i : ZMod (prime j)) =
              (point j 0)⁻¹ * point j i.succ) →
          S.card ≤ d * K := by
  obtain ⟨K, hK⟩ := hSalberger N d ε hε
  refine ⟨K, ?_⟩
  intro I hIhom hIprime hIirrelevant hIdegree hIchart B hB
    index _ prime hprime hinjective point hpoint0 hmultiplicity
    hproduct S hbox hzero hreduction
  obtain ⟨hIscheme, hinfinity⟩ :=
    homogeneousPrime_salbergerProjectiveHypotheses
      I hIhom hIprime hIirrelevant hIdegree hIchart
  obtain ⟨k, G, hk, hGhom, hGnot, hGsource⟩ :=
    hK 1 (by omega) I hIscheme hinfinity B hB index inferInstance
      prime hprime hinjective (fun _ ↦ 1) (fun _ ↦ Nat.zero_lt_succ 0)
      point hpoint0 hmultiplicity (by simpa using hproduct)
  have hGzero : ∀ z ∈ S,
      MvPolynomial.eval (rationalIntegralAffineChartPoint z) G = 0 := by
    intro z hz
    apply hGsource (integralAffineChartVector z)
    exact integralAffineChartVector_mem_InSalbergerSOne
      I B hB prime hprime point hpoint0 z (hbox z hz)
        (by simpa [rationalIntegralAffineChartPoint] using hzero z hz)
        (hreduction z hz)
  have hcard : S.card ≤ d * k :=
    card_integralAffinePoints_on_projectiveCurve_auxiliary_le
      hBezout I G hIprime hIhom hIdegree hGhom hGnot S hzero hGzero
  exact hcard.trans (Nat.mul_le_mul_left d hk)

/-! ## The square-free modulus product -/

/-- Transport an affine residue vector along a literal equality of its
moduli. -/
def curveCastResidueVector {N q r : ℕ} (h : q = r)
    (rho : Fin N → ZMod q) : Fin N → ZMod r :=
  fun i ↦ ZMod.castHom h.symm.dvd (ZMod r) (rho i)

@[simp]
theorem curveCastResidueVector_rfl {N q : ℕ} (rho : Fin N → ZMod q) :
    curveCastResidueVector rfl rho = rho := by
  funext i
  simp [curveCastResidueVector]

/-- Transporting the residue modulus transports the literal packet. -/
theorem integralResiduePacket_curveCastResidueVector
    {N q r : ℕ} (h : q = r) (S : Finset (IntVector N))
    (rho : Fin N → ZMod q) :
    integralResiduePacket S (curveCastResidueVector h rho) =
      integralResiduePacket S rho := by
  cases h
  rw [curveCastResidueVector_rfl]

/-- Reduction from a product of primes to one displayed prime factor. -/
def curvePrimeReduction (P : Finset ℕ) (s : {s // s ∈ P}) :
    ZMod (primeProduct P) →+* ZMod s.1 :=
  ZMod.castHom (by
    simpa [primeProduct] using
      (Finset.dvd_prod_of_mem id s.2)) (ZMod s.1)

/-- The normalized projective residue point attached to an affine residue
vector. -/
def curveAffineProjectivePoint {N : ℕ} (P : Finset ℕ)
    (rho : Fin N → ZMod (primeProduct P)) (s : {s // s ∈ P}) :
    Fin (N + 1) → ZMod s.1 :=
  Fin.cases 1 fun i ↦ curvePrimeReduction P s (rho i)

@[simp]
theorem curveAffineProjectivePoint_zero {N : ℕ}
    (P : Finset ℕ) (rho : Fin N → ZMod (primeProduct P))
    (s : {s // s ∈ P}) :
    curveAffineProjectivePoint P rho s 0 = 1 := rfl

@[simp]
theorem curveAffineProjectivePoint_succ {N : ℕ}
    (P : Finset ℕ) (rho : Fin N → ZMod (primeProduct P))
    (s : {s // s ∈ P}) (i : Fin N) :
    curveAffineProjectivePoint P rho s i.succ =
      curvePrimeReduction P s (rho i) := rfl

/-- Every point of a residue packet specializes to the corresponding
normalized projective point at each prime factor. -/
theorem integralResiduePacket_specializesTo_curveAffineProjectivePoint
    {N : ℕ} (P : Finset ℕ) (hprime : ∀ s ∈ P, s.Prime)
    (S : Finset (IntVector N))
    (rho : Fin N → ZMod (primeProduct P))
    {z : IntVector N} (hz : z ∈ integralResiduePacket S rho)
    (s : {s // s ∈ P}) (i : Fin N) :
    (z i : ZMod s.1) =
      (curveAffineProjectivePoint P rho s 0)⁻¹ *
        curveAffineProjectivePoint P rho s i.succ := by
  letI : Fact s.1.Prime := ⟨hprime s.1 s.2⟩
  have hzrho := congrFun (mem_integralResiduePacket_iff.mp hz).2 i
  have hcast := congrArg (curvePrimeReduction P s) hzrho
  have hsdiv : s.1 ∣ primeProduct P := by
    simpa [primeProduct] using
      (Finset.dvd_prod_of_mem id s.2)
  change ZMod.cast (z i : ZMod (primeProduct P)) =
      ZMod.cast (rho i) at hcast
  rw [ZMod.cast_intCast hsdiv] at hcast
  simpa using hcast

/-- The normalized projective residue point is in the standard chart. -/
theorem curveAffineProjectivePoint_zero_ne_zero {N : ℕ}
    (P : Finset ℕ) (hprime : ∀ s ∈ P, s.Prime)
    (rho : Fin N → ZMod (primeProduct P)) (s : {s // s ∈ P}) :
    curveAffineProjectivePoint P rho s 0 ≠ 0 := by
  letI : Fact s.1.Prime := ⟨hprime s.1 s.2⟩
  rw [curveAffineProjectivePoint_zero]
  exact one_ne_zero

/-- For a curve and multiplicity one, the several-prime product indexed by
the prime divisors of a square-free modulus is literally `q ^ d`. -/
theorem curveMultiplicityOne_primeFactors_product_eq_modulus_rpow
    {q d : ℕ} (hq : Squarefree q) :
    (∏ s : {s // s ∈ q.primeFactors},
      ((s : ℕ) : ℝ) ^
        (((d : ℝ) / (1 : ℝ)) ^ ((1 : ℝ)⁻¹))) =
      (q : ℝ) ^ (d : ℝ) := by
  have hexponent :
      (((d : ℝ) / (1 : ℝ)) ^ ((1 : ℝ)⁻¹)) = (d : ℝ) := by
    norm_num
  rw [hexponent, primeSubtype_prod_natCast_rpow_eq_primeProduct]
  rw [show primeProduct q.primeFactors = q by
    simpa only [primeProduct] using Nat.prod_primeFactors_of_squarefree hq]

/-- Square-free-modulus specialization of the preceding uniform packet
bound.  All local multiplicity-one assertions remain explicit. -/
theorem exists_uniform_projectiveCurve_squarefreePacket_card_le_degree_mul
    (hSalberger : Salberger2007Corollary37)
    (hBezout : StandardAG.RationalProjectiveCurveAuxiliaryFirstChartBezout)
    (N d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ,
      ∀ (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
        I.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
        I.IsPrime →
        ¬ projectiveIrrelevantIdeal ℚ N ≤ I →
        HasProjectiveDimensionDegree I 1 d →
        X (0 : Fin (N + 1)) ∉ I →
        ∀ (q : ℕ), Squarefree q →
        ∀ (point : ∀ s : {s // s ∈ q.primeFactors},
          Fin (N + 1) → ZMod s.1),
          (∀ s, point s 0 ≠ 0) →
          (∀ s, HasHilbertSamuelMultiplicityAt
            ((Nat.mem_primeFactors.mp s.2).1)
            (projectiveSpecialFiberIdeal I) (point s) 1 1) →
        ∀ (B : ℝ), 1 ≤ B →
          B ^ (1 + ε) ≤ (q : ℝ) ^ (d : ℝ) →
        ∀ (S : Finset (IntVector N)),
          (∀ z ∈ S, ∀ i, |(z i : ℝ)| ≤ B) →
          (∀ z ∈ S, ∀ f ∈ I,
            MvPolynomial.eval (rationalIntegralAffineChartPoint z) f = 0) →
          (∀ z ∈ S, ∀ s i,
            (z i : ZMod s.1) = (point s 0)⁻¹ * point s i.succ) →
          S.card ≤ d * K := by
  obtain ⟨K, hK⟩ :=
    exists_uniform_projectiveCurve_packet_card_le_degree_mul_salberger
      hSalberger hBezout N d hε
  refine ⟨K, ?_⟩
  intro I hIhom hIprime hIirrelevant hIdegree hIchart q hq point
    hpoint0 hmultiplicity B hB hthreshold S hbox hzero hreduction
  apply hK I hIhom hIprime hIirrelevant hIdegree hIchart B hB
    {s // s ∈ q.primeFactors} inferInstance (fun s ↦ s.1)
    (fun s ↦ (Nat.mem_primeFactors.mp s.2).1) Subtype.val_injective
    point hpoint0 hmultiplicity _ S hbox hzero hreduction
  rw [curveMultiplicityOne_primeFactors_product_eq_modulus_rpow hq]
  exact hthreshold

/-- One auxiliary-degree constant works simultaneously for every nonlinear
curve degree at most `D`.  The conclusion uses the harmless uniform envelope
`D * K`; in particular the constant is chosen before the curve and its
degree. -/
theorem exists_uniform_projectiveCurve_squarefreePacket_card_le_degreeBound_mul
    (hSalberger : Salberger2007Corollary37)
    (hBezout : StandardAG.RationalProjectiveCurveAuxiliaryFirstChartBezout)
    (N D : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ,
      ∀ (d : ℕ), 2 ≤ d → d ≤ D →
      ∀ (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
        I.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
        I.IsPrime →
        ¬ projectiveIrrelevantIdeal ℚ N ≤ I →
        HasProjectiveDimensionDegree I 1 d →
        X (0 : Fin (N + 1)) ∉ I →
        ∀ (q : ℕ), Squarefree q →
        ∀ (point : ∀ s : {s // s ∈ q.primeFactors},
          Fin (N + 1) → ZMod s.1),
          (∀ s, point s 0 ≠ 0) →
          (∀ s, HasHilbertSamuelMultiplicityAt
            ((Nat.mem_primeFactors.mp s.2).1)
            (projectiveSpecialFiberIdeal I) (point s) 1 1) →
        ∀ (B : ℝ), 1 ≤ B →
          B ^ (1 + ε) ≤ (q : ℝ) ^ (d : ℝ) →
        ∀ (S : Finset (IntVector N)),
          (∀ z ∈ S, ∀ i, |(z i : ℝ)| ≤ B) →
          (∀ z ∈ S, ∀ f ∈ I,
            MvPolynomial.eval (rationalIntegralAffineChartPoint z) f = 0) →
          (∀ z ∈ S, ∀ s i,
            (z i : ZMod s.1) = (point s 0)⁻¹ * point s i.succ) →
          S.card ≤ D * K := by
  classical
  let degrees : Finset ℕ := Finset.Icc 2 D
  let Degree := {d : ℕ // d ∈ degrees}
  have heach : ∀ e : Degree, ∃ K : ℕ,
      ∀ (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
        I.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
        I.IsPrime →
        ¬ projectiveIrrelevantIdeal ℚ N ≤ I →
        HasProjectiveDimensionDegree I 1 e.1 →
        X (0 : Fin (N + 1)) ∉ I →
        ∀ (q : ℕ), Squarefree q →
        ∀ (point : ∀ s : {s // s ∈ q.primeFactors},
          Fin (N + 1) → ZMod s.1),
          (∀ s, point s 0 ≠ 0) →
          (∀ s, HasHilbertSamuelMultiplicityAt
            ((Nat.mem_primeFactors.mp s.2).1)
            (projectiveSpecialFiberIdeal I) (point s) 1 1) →
        ∀ (B : ℝ), 1 ≤ B →
          B ^ (1 + ε) ≤ (q : ℝ) ^ (e.1 : ℝ) →
        ∀ (S : Finset (IntVector N)),
          (∀ z ∈ S, ∀ i, |(z i : ℝ)| ≤ B) →
          (∀ z ∈ S, ∀ f ∈ I,
            MvPolynomial.eval (rationalIntegralAffineChartPoint z) f = 0) →
          (∀ z ∈ S, ∀ s i,
            (z i : ZMod s.1) = (point s 0)⁻¹ * point s i.succ) →
          S.card ≤ e.1 * K := by
    intro e
    exact exists_uniform_projectiveCurve_squarefreePacket_card_le_degree_mul
      hSalberger hBezout N e.1 hε
  choose c hc using heach
  let K : ℕ := ∑ e : Degree, c e
  refine ⟨K, ?_⟩
  intro d hd hdD I hIhom hIprime hIirrelevant hIdegree hIchart
    q hq point hpoint0 hmultiplicity B hB hthreshold S hbox hzero
    hreduction
  have hdmem : d ∈ degrees := Finset.mem_Icc.mpr ⟨hd, hdD⟩
  let e : Degree := ⟨d, hdmem⟩
  have hsource := hc e I hIhom hIprime hIirrelevant
    (by simpa [e] using hIdegree) hIchart q hq point hpoint0
    hmultiplicity B hB (by simpa [e] using hthreshold) S hbox hzero
    hreduction
  have hcle : c e ≤ K := by
    dsimp only [K]
    exact Finset.single_le_sum
      (fun a _ ↦ Nat.zero_le (c a)) (Finset.mem_univ e)
  exact hsource.trans (Nat.mul_le_mul hdD hcle)

end

end TranslatedDepthSeven
