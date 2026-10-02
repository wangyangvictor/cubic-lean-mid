import TranslatedDepthSeven.RankSevenSalbergerPilaTerminal
import TranslatedDepthSeven.RankSevenSourceSectionComponents

/-!
# Composition of an actual rank-seven source section with Salberger and Pila

This file partitions a literal occupied packet by the actual rational
minimal-prime components of its normalized source section.  For every
nonempty component class, homogeneity, primality, survival in projective
space, and meeting the standard affine chart are proved internally.  An
exact projective Hilbert dimension--degree statement, the literal smooth
special-fibre data, and the post-auxiliary-form component facts then feed
directly into the Salberger--Pila terminal theorem.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000

/-- The points of a literal packet which lie on one specified actual
rational component of the normalized source section. -/
def rankSevenPacketPointsOnSourceComponent
    (X : Finset (IntVector 13))
    (I : Ideal (MvPolynomial (Fin 14) ℚ)) : Finset (IntVector 13) := by
  classical
  exact X.filter fun z ↦ ∀ f ∈ I,
    MvPolynomial.eval
      (fun i ↦ (integralAffineChartVector z i : ℚ)) f = 0

@[simp]
theorem mem_rankSevenPacketPointsOnSourceComponent_iff
    (X : Finset (IntVector 13))
    (I : Ideal (MvPolynomial (Fin 14) ℚ)) (z : IntVector 13) :
    z ∈ rankSevenPacketPointsOnSourceComponent X I ↔
      z ∈ X ∧ ∀ f ∈ I, MvPolynomial.eval
        (fun i ↦ (integralAffineChartVector z i : ℚ)) f = 0 := by
  classical
  simp [rankSevenPacketPointsOnSourceComponent]

/-- The packet is covered by its actual rational minimal-prime component
classes. -/
theorem rankSevenPacket_card_le_sum_sourceComponents
    (x₀ : IntVector 13) {m : ℕ} (hm : 0 < m)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (A : Matrix (Fin 4) (Fin 14) ℚ)
    (X : Finset (IntVector 13))
    (hzero : ∀ z ∈ X,
      IntegralCommonZero equations (integralAffineMap x₀ z m))
    (hA : ∀ z ∈ X,
      Matrix.mulVec A (rationalHomogeneousAffinePoint z) = 0) :
    X.card ≤
      ∑ I ∈ finiteMinimalPrimes
          (rankSevenSourceSectionIdeal x₀ m hm equations A),
        (rankSevenPacketPointsOnSourceComponent X I).card := by
  classical
  let components := finiteMinimalPrimes
    (rankSevenSourceSectionIdeal x₀ m hm equations A)
  let componentUnion : Finset (IntVector 13) :=
    components.biUnion fun I ↦ rankSevenPacketPointsOnSourceComponent X I
  have hcover : X ⊆ componentUnion := by
    intro z hz
    obtain ⟨I, hI, _hprime, _hhom, _hchart, _hirr, hIz⟩ :=
      exists_rankSevenSourceSectionComponent_through_packetPoint
        x₀ hm equations hhomogeneous A z (hzero z hz) (hA z hz)
    exact Finset.mem_biUnion.mpr
      ⟨I, hI,
        (mem_rankSevenPacketPointsOnSourceComponent_iff X I z).mpr
          ⟨hz, hIz⟩⟩
  calc
    X.card ≤ componentUnion.card := Finset.card_le_card hcover
    _ ≤ ∑ I ∈ components,
        (rankSevenPacketPointsOnSourceComponent X I).card :=
      Finset.card_biUnion_le

/-- The actual Cramer section supplied by an occupied rank-seven chart
packet gives the preceding component cover, with its rank and height data
retained verbatim.  This is the concrete connection to
`exists_projectedSection_for_rankSevenChartPacket`; no component geometry is
inserted here. -/
theorem exists_rankSevenSourceSection_componentCover_for_chartPacket
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (P : Finset ℕ) (hprime : ∀ s ∈ P, s.Prime)
    (hlower : manuscriptReservoirTarget normalizedSurfaceReservoirConstant
      p.T (5 / 7) ≤ primeProduct P)
    (rho : Fin 13 → ZMod (primeProduct P))
    (hrho : rho ∈ occupiedIntegralResidues (primeProduct P)
      (depthSevenNormalizedJacobianChartCell p x₀ equations CF C))
    (hqm : Nat.Coprime (primeProduct P) p.m)
    (hqchart : Nat.Coprime (primeProduct P)
      (MvPolynomial.eval
        (integralAffineMap x₀
          (integralResiduePacketBase
            (depthSevenNormalizedJacobianChartCell p x₀ equations CF C)
            rho hrho) p.m)
        C.determinant).natAbs) :
    ∃ A : Matrix (Fin 4) (Fin 14) ℤ,
      (A.map ((↑) : ℤ → ℚ)).rank = 4 ∧
      (∀ i q, (A i q).natAbs ≤ depthSevenPacketSectionEntryBound p) ∧
      rationalProjectiveLinearHeight (A.map ((↑) : ℤ → ℚ)) ≤
        ⌈p.H ^ packetSectionHeightExponent⌉₊ ∧
      (integralResiduePacket
        (depthSevenNormalizedJacobianChartCell p x₀ equations CF C) rho).card ≤
        ∑ I ∈ finiteMinimalPrimes
            (rankSevenSourceSectionIdeal x₀ p.m p.hm equations
              (A.map ((↑) : ℤ → ℚ))),
          (rankSevenPacketPointsOnSourceComponent
            (integralResiduePacket
              (depthSevenNormalizedJacobianChartCell p x₀ equations CF C) rho)
            I).card := by
  obtain ⟨A, hArank, hAmem, hAentry, hAheight, _hprojected⟩ :=
    exists_projectedSection_for_rankSevenChartPacket
      p x₀ equations CF C P hprime hlower rho hrho hqm hqchart
  refine ⟨A, hArank, hAentry, hAheight, ?_⟩
  apply rankSevenPacket_card_le_sum_sourceComponents
    x₀ p.hm equations hhomogeneous (A.map ((↑) : ℤ → ℚ))
  · intro z hz
    have hzChart : z ∈
        depthSevenNormalizedJacobianChartCell p x₀ equations CF C :=
      (mem_integralResiduePacket_iff.mp hz).1
    exact depthSevenNormalized_integralCommonZero p x₀ equations CF
      ((mem_depthSevenNormalizedJacobianChartCell_iff
        p x₀ equations CF C z).mp hzChart).1
  · exact hAmem

/-- A nonempty actual component class automatically gives all projective
qualification hypotheses required by Salberger except its Hilbert
dimension--degree formula. -/
theorem rankSevenSourceComponent_projectiveQualification_of_nonempty
    (x₀ : IntVector 13) {m : ℕ} (hm : 0 < m)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (A : Matrix (Fin 4) (Fin 14) ℚ)
    (X : Finset (IntVector 13))
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (hI : I ∈ finiteMinimalPrimes
      (rankSevenSourceSectionIdeal x₀ m hm equations A))
    (hnonempty :
      (rankSevenPacketPointsOnSourceComponent X I).Nonempty) :
    I.IsPrime ∧
      I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 14) ℚ) ∧
      MvPolynomial.X (0 : Fin 14) ∉ I ∧
      ¬ (projectiveIrrelevantIdeal ℚ 13 ≤ I) := by
  obtain ⟨z, hz⟩ := hnonempty
  have hzspec :=
    (mem_rankSevenPacketPointsOnSourceComponent_iff X I z).mp hz
  have hprime := isPrime_of_mem_finiteMinimalPrimes hI
  have hhom : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 14) ℚ) :=
    isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous
      (rankSevenSourceSectionIdeal_isHomogeneous
        x₀ hm equations hhomogeneous A)
      ((mem_finiteMinimalPrimes_iff _ _).mp hI)
  have hchart : MvPolynomial.X (0 : Fin 14) ∉ I := by
    intro hX
    have := hzspec.2 _ hX
    simp [integralAffineChartVector] at this
  have hirrelevant : ¬ (projectiveIrrelevantIdeal ℚ 13 ≤ I) := by
    intro hle
    exact hchart (hle (Ideal.subset_span ⟨0, rfl⟩))
  exact ⟨hprime, hhom, hchart, hirrelevant⟩

/-! ## The canonical projective residue point of a square-free packet -/

/-- Reduction from the literal reservoir modulus to one of its prime
factors. -/
def reservoirPrimeReduction (P : Finset ℕ) (s : {s // s ∈ P}) :
    ZMod (primeProduct P) →+* ZMod s.1 :=
  ZMod.castHom (by
    simpa [primeProduct] using
      (Finset.dvd_prod_of_mem id s.2)) (ZMod s.1)

/-- The standard-affine projective point over a reservoir prime attached to
one occupied residue vector. -/
def reservoirAffineProjectivePoint (P : Finset ℕ)
    (rho : Fin 13 → ZMod (primeProduct P)) (s : {s // s ∈ P}) :
    Fin 14 → ZMod s.1 :=
  Fin.cases 1 fun i ↦ reservoirPrimeReduction P s (rho i)

@[simp]
theorem reservoirAffineProjectivePoint_zero
    (P : Finset ℕ) (rho : Fin 13 → ZMod (primeProduct P))
    (s : {s // s ∈ P}) :
    reservoirAffineProjectivePoint P rho s 0 = 1 := by
  rfl

@[simp]
theorem reservoirAffineProjectivePoint_succ
    (P : Finset ℕ) (rho : Fin 13 → ZMod (primeProduct P))
    (s : {s // s ∈ P}) (i : Fin 13) :
    reservoirAffineProjectivePoint P rho s i.succ =
      reservoirPrimeReduction P s (rho i) := by
  rfl

/-- Every point of a residue packet specializes to its canonical standard-
affine projective residue point at each reservoir prime. -/
theorem integralResiduePacket_specializesTo_reservoirAffineProjectivePoint
    (P : Finset ℕ) (hprime : ∀ s ∈ P, s.Prime)
    (Z : Finset (IntVector 13))
    (rho : Fin 13 → ZMod (primeProduct P))
    {z : IntVector 13} (hz : z ∈ integralResiduePacket Z rho)
    (s : {s // s ∈ P}) (i : Fin 13) :
    (z i : ZMod s.1) =
      (reservoirAffineProjectivePoint P rho s 0)⁻¹ *
        reservoirAffineProjectivePoint P rho s i.succ := by
  letI : Fact s.1.Prime := ⟨hprime s.1 s.2⟩
  have hzrho := congrFun (mem_integralResiduePacket_iff.mp hz).2 i
  have hcast := congrArg (reservoirPrimeReduction P s) hzrho
  have hsdiv : s.1 ∣ primeProduct P := by
    simpa [primeProduct] using
      (Finset.dvd_prod_of_mem id s.2)
  change ZMod.cast (z i : ZMod (primeProduct P)) =
      ZMod.cast (rho i) at hcast
  rw [ZMod.cast_intCast hsdiv] at hcast
  simpa using hcast

/-- The canonical projective residue point lies in the standard affine
chart. -/
theorem reservoirAffineProjectivePoint_zero_ne_zero
    (P : Finset ℕ) (hprime : ∀ s ∈ P, s.Prime)
    (rho : Fin 13 → ZMod (primeProduct P)) (s : {s // s ∈ P}) :
    reservoirAffineProjectivePoint P rho s 0 ≠ 0 := by
  letI : Fact s.1.Prime := ⟨hprime s.1 s.2⟩
  simp

/-- Direct application of the terminal theorem to one nonempty actual
source-section component class.  The displayed remaining hypotheses are
exactly: its projective dimension and degree, Salberger's smooth special
fibres and prime product, and the dimension/degree alternatives for the
actual affine minimal primes after adjoining his auxiliary form. -/
theorem rankSevenSourceComponentPacket_card_le_salbergerLines_add_pilaCurves
    (hSalberger : Salberger2007Corollary37)
    (hPila : Pila1995TheoremA)
    (x₀ : IntVector 13) {m : ℕ} (hm : 0 < m)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (A : Matrix (Fin 4) (Fin 14) ℚ)
    (packet : Finset (IntVector 13))
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (hI : I ∈ finiteMinimalPrimes
      (rankSevenSourceSectionIdeal x₀ m hm equations A))
    (hnonempty :
      (rankSevenPacketPointsOnSourceComponent packet I).Nonempty)
    {d D : ℕ} (hIdimensionDegree : HasProjectiveDimensionDegree I 2 d)
    {εSalberger εPila B : ℝ}
    (hεSalberger : 0 < εSalberger) (hεPila : 0 < εPila)
    (hB : 1 ≤ B)
    {index : Type} [Fintype index]
    (prime : index → ℕ) (hprime : ∀ i, (prime i).Prime)
    (hinjective : Function.Injective prime)
    (point : ∀ i, Fin 14 → ZMod (prime i))
    (hchart : ∀ i, point i 0 ≠ 0)
    (hmultiplicity : ∀ i,
      HasHilbertSamuelMultiplicityAt (hprime i)
        (projectiveSpecialFiberIdeal I) (point i) 2 1)
    (hproduct : B ^ (1 + εSalberger) ≤
      ∏ i, (prime i : ℝ) ^
        (((d : ℝ) / (1 : ℝ)) ^ ((2 : ℝ)⁻¹)))
    (hbox : ∀ z ∈ packet, ∀ i, |(z i : ℝ)| ≤ B)
    (hreduction : ∀ z ∈ packet, ∀ j i,
      (z i : ZMod (prime j)) =
        (point j 0)⁻¹ * point j i.succ) :
    ∃ K : ℕ,
      (∀ (k : ℕ), k ≤ K →
        ∀ G : MvPolynomial (Fin 14) ℚ,
          G.IsHomogeneous k → G ∉ I →
          ∀ Q ∈ finiteMinimalPrimes
              (realAffineChartIntersectionIdeal I G),
            HasAffineHilbertDimensionDegree Q 1 1 ∨
              ∃ e : ℕ, 2 ≤ e ∧ e ≤ D ∧
                HasAffineHilbertDimensionDegree Q 1 e) →
      ∃ (k : ℕ) (G : MvPolynomial (Fin 14) ℚ) (C : ℝ),
        0 < C ∧ k ≤ K ∧ G.IsHomogeneous k ∧ G ∉ I ∧
        (∀ z ∈ rankSevenPacketPointsOnSourceComponent packet I,
          MvPolynomial.eval
            (fun i ↦ (integralAffineChartVector z i : ℚ)) G = 0) ∧
        ((rankSevenPacketPointsOnSourceComponent packet I).card : ℝ) ≤
          ((finitePointsOnLinearCurveComponents
            (realAffineChartIntersectionIdeal I G)
            (rankSevenPacketPointsOnSourceComponent packet I)).card : ℝ) +
          ((nonlinearAffineComponents
            (realAffineChartIntersectionIdeal I G)).card : ℝ) * C *
            (B + 1) ^ ((1 / 2 : ℝ) + εPila) := by
  obtain ⟨hIprime, hIhom, hIchart, hIirrelevant⟩ :=
    rankSevenSourceComponent_projectiveQualification_of_nonempty
      x₀ hm equations hhomogeneous A packet I hI hnonempty
  apply rankSevenSurfacePacket_card_le_salbergerLines_add_pilaCurves
    hSalberger hPila hεSalberger hεPila I hIhom hIprime
      hIirrelevant hIdimensionDegree hIchart hB prime hprime hinjective
      point hchart hmultiplicity hproduct
      (rankSevenPacketPointsOnSourceComponent packet I)
  · intro z hz i
    exact hbox z
      ((mem_rankSevenPacketPointsOnSourceComponent_iff packet I z).mp hz).1 i
  · intro z hz f hf
    exact ((mem_rankSevenPacketPointsOnSourceComponent_iff packet I z).mp hz).2
      f hf
  · intro z hz j i
    exact hreduction z
      ((mem_rankSevenPacketPointsOnSourceComponent_iff packet I z).mp hz).1 j i

/-- The preceding component estimate specialized to a literal occupied
residue packet.  The prime indexing, projective residue points, affine-chart
condition, and all specialization congruences are now canonical; only the
genuinely geometric multiplicity statement and Salberger's numerical
product condition remain as local inputs. -/
theorem rankSevenResiduePacketComponent_card_le_salbergerLines_add_pilaCurves
    (hSalberger : Salberger2007Corollary37)
    (hPila : Pila1995TheoremA)
    (x₀ : IntVector 13) {m : ℕ} (hm : 0 < m)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (A : Matrix (Fin 4) (Fin 14) ℚ)
    (Z : Finset (IntVector 13))
    (P : Finset ℕ) (hprime : ∀ s ∈ P, s.Prime)
    (rho : Fin 13 → ZMod (primeProduct P))
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (hI : I ∈ finiteMinimalPrimes
      (rankSevenSourceSectionIdeal x₀ m hm equations A))
    (hnonempty :
      (rankSevenPacketPointsOnSourceComponent
        (integralResiduePacket Z rho) I).Nonempty)
    {d D : ℕ} (hIdimensionDegree : HasProjectiveDimensionDegree I 2 d)
    {εSalberger εPila B : ℝ}
    (hεSalberger : 0 < εSalberger) (hεPila : 0 < εPila)
    (hB : 1 ≤ B)
    (hmultiplicity : ∀ s : {s // s ∈ P},
      HasHilbertSamuelMultiplicityAt (hprime s.1 s.2)
        (projectiveSpecialFiberIdeal I)
        (reservoirAffineProjectivePoint P rho s) 2 1)
    (hproduct : B ^ (1 + εSalberger) ≤
      ∏ s : {s // s ∈ P}, (s.1 : ℝ) ^
        (((d : ℝ) / (1 : ℝ)) ^ ((2 : ℝ)⁻¹)))
    (hbox : ∀ z ∈ integralResiduePacket Z rho,
      ∀ i, |(z i : ℝ)| ≤ B) :
    ∃ K : ℕ,
      (∀ (k : ℕ), k ≤ K →
        ∀ G : MvPolynomial (Fin 14) ℚ,
          G.IsHomogeneous k → G ∉ I →
          ∀ Q ∈ finiteMinimalPrimes
              (realAffineChartIntersectionIdeal I G),
            HasAffineHilbertDimensionDegree Q 1 1 ∨
              ∃ e : ℕ, 2 ≤ e ∧ e ≤ D ∧
                HasAffineHilbertDimensionDegree Q 1 e) →
      ∃ (k : ℕ) (G : MvPolynomial (Fin 14) ℚ) (C : ℝ),
        0 < C ∧ k ≤ K ∧ G.IsHomogeneous k ∧ G ∉ I ∧
        (∀ z ∈ rankSevenPacketPointsOnSourceComponent
            (integralResiduePacket Z rho) I,
          MvPolynomial.eval
            (fun i ↦ (integralAffineChartVector z i : ℚ)) G = 0) ∧
        ((rankSevenPacketPointsOnSourceComponent
          (integralResiduePacket Z rho) I).card : ℝ) ≤
          ((finitePointsOnLinearCurveComponents
            (realAffineChartIntersectionIdeal I G)
            (rankSevenPacketPointsOnSourceComponent
              (integralResiduePacket Z rho) I)).card : ℝ) +
          ((nonlinearAffineComponents
            (realAffineChartIntersectionIdeal I G)).card : ℝ) * C *
            (B + 1) ^ ((1 / 2 : ℝ) + εPila) := by
  apply rankSevenSourceComponentPacket_card_le_salbergerLines_add_pilaCurves
    hSalberger hPila x₀ hm equations hhomogeneous A
      (integralResiduePacket Z rho) I hI hnonempty hIdimensionDegree
      hεSalberger hεPila hB
      (fun s : {s // s ∈ P} ↦ s.1)
      (fun s ↦ hprime s.1 s.2) Subtype.val_injective
      (reservoirAffineProjectivePoint P rho)
      (reservoirAffineProjectivePoint_zero_ne_zero P hprime rho)
      hmultiplicity hproduct hbox
  intro z hz s i
  exact integralResiduePacket_specializesTo_reservoirAffineProjectivePoint
    P hprime Z rho hz s i

end

end TranslatedDepthSeven
