import TranslatedDepthSeven.RankSevenPacketSalbergerComposition
import TranslatedDepthSeven.LocalizedJacobianComponentMultiplicityOne
import TranslatedDepthSeven.SquarefreeRpow
import TranslatedDepthSeven.FiniteResiduePacketRescaling

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

theorem isPointOn_projectiveSpecialFiber_of_integralZero
    {N p : ℕ} [Fact p.Prime]
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (x : Fin (N + 1) → ℤ)
    (hx : ∀ f ∈ I, MvPolynomial.eval (fun i ↦ (x i : ℚ)) f = 0)
    (P : Fin (N + 1) → ZMod p)
    (hP : ∀ i, (x i : ZMod p) = P i) :
    IsPointOnSpecialFiber (projectiveSpecialFiberIdeal I) P := by
  rw [IsPointOnSpecialFiber, projectiveSpecialFiberIdeal,
    Ideal.map_le_iff_le_comap]
  intro f hf
  change MvPolynomial.map (Int.castRingHom (ZMod p)) f ∈
    RingHom.ker (specialFiberEvaluation P)
  change MvPolynomial.map (Int.castRingHom ℚ) f ∈ I at hf
  rw [RingHom.mem_ker]
  change MvPolynomial.eval P
    (MvPolynomial.map (Int.castRingHom (ZMod p)) f) = 0
  have hrat := hx (MvPolynomial.map (Int.castRingHom ℚ) f) hf
  rw [eval_map_intCast] at hrat
  have hint : MvPolynomial.eval x f = 0 := by
    exact_mod_cast hrat
  rw [← funext hP, eval_map_intCast, hint, Int.cast_zero]

theorem isPointOn_standardAffineChart_of_zero_eq_one
    {N p : ℕ} [Fact p.Prime]
    (J : Ideal (MvPolynomial (Fin (N + 1)) (ZMod p)))
    (P : Fin (N + 1) → ZMod p)
    (hP : IsPointOnSpecialFiber J P) (hPzero : P 0 = 1) :
    IsPointOnSpecialFiber (standardAffineChartIdeal J)
      (standardAffineChartPoint P) := by
  rw [IsPointOnSpecialFiber, standardAffineChartIdeal,
    Ideal.map_le_iff_le_comap]
  intro f hf
  rw [Ideal.mem_comap]
  have heval :
      (specialFiberEvaluation (standardAffineChartPoint P)).comp
          dehomogenizeAtZeroHom =
        specialFiberEvaluation P := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [specialFiberEvaluation, dehomogenizeAtZeroHom]
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp [specialFiberEvaluation, dehomogenizeAtZeroHom, hPzero]
      · simp [specialFiberEvaluation, dehomogenizeAtZeroHom,
          standardAffineChartPoint, hPzero]
  change specialFiberEvaluation (standardAffineChartPoint P)
      (dehomogenizeAtZeroHom f) = 0
  rw [← RingHom.comp_apply, heval]
  exact hP hf

/-- The canonical residue point of an occupied packet is a point of the
special fibre of every actual source-section component containing the
packet point. -/
theorem rankSevenSourceComponent_reservoirPoint_isPointOnSpecialFiber
    (Z : Finset (IntVector 13))
    (P : Finset ℕ) (hprime : ∀ s ∈ P, s.Prime)
    (rho : Fin 13 → ZMod (primeProduct P))
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    {z : IntVector 13}
    (hz : z ∈ rankSevenPacketPointsOnSourceComponent
      (integralResiduePacket Z rho) I)
    (s : {s // s ∈ P}) [Fact s.1.Prime] :
    IsPointOnSpecialFiber (projectiveSpecialFiberIdeal I)
      (reservoirAffineProjectivePoint P rho s) := by
  apply isPointOn_projectiveSpecialFiber_of_integralZero I
    (integralAffineChartVector z)
  · exact (mem_rankSevenPacketPointsOnSourceComponent_iff
      (integralResiduePacket Z rho) I z).mp hz |>.2
  · intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp
    · have hj :=
        integralResiduePacket_specializesTo_reservoirAffineProjectivePoint
          P hprime Z rho
          ((mem_rankSevenPacketPointsOnSourceComponent_iff
            (integralResiduePacket Z rho) I z).mp hz).1 s j
      simpa using hj

/-- The canonical residue point also lies on the dehomogenized special
fibre used in the literal Hilbert--Samuel predicate. -/
theorem rankSevenSourceComponent_reservoirAffinePoint_isPointOnSpecialFiber
    (Z : Finset (IntVector 13))
    (P : Finset ℕ) (hprime : ∀ s ∈ P, s.Prime)
    (rho : Fin 13 → ZMod (primeProduct P))
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    {z : IntVector 13}
    (hz : z ∈ rankSevenPacketPointsOnSourceComponent
      (integralResiduePacket Z rho) I)
    (s : {s // s ∈ P}) [Fact s.1.Prime] :
    IsPointOnSpecialFiber
      (standardAffineChartIdeal (projectiveSpecialFiberIdeal I))
      (standardAffineChartPoint (reservoirAffineProjectivePoint P rho s)) := by
  apply isPointOn_standardAffineChart_of_zero_eq_one
  · exact rankSevenSourceComponent_reservoirPoint_isPointOnSpecialFiber
      Z P hprime rho I hz s
  · exact reservoirAffineProjectivePoint_zero P rho s

/-- Explicit local equations for the actual reduced source component,
together with a clearing denominator and one nonzero `11 x 11` Jacobian
minor, prove multiplicity one at every canonical reservoir point.  The
point-on-fibre assertion is deduced from packet membership rather than
assumed. -/
theorem rankSevenResiduePacketComponent_multiplicityOne_of_localEquations
    (Z : Finset (IntVector 13))
    (P : Finset ℕ) (hprime : ∀ s ∈ P, s.Prime)
    (rho : Fin 13 → ZMod (primeProduct P))
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (hnonempty :
      (rankSevenPacketPointsOnSourceComponent
        (integralResiduePacket Z rho) I).Nonempty)
    (localEquations : ∀ s : {s // s ∈ P},
      Fin 11 → MvPolynomial (Fin 13) (ZMod s.1))
    (selectedVar : ∀ _s : {s // s ∈ P}, Fin 11 → Fin 13)
    (hselected : ∀ s, Function.Injective (selectedVar s))
    (u : ∀ s : {s // s ∈ P}, MvPolynomial (Fin 13) (ZMod s.1))
    (hIJ : ∀ s,
      Ideal.span (Set.range (localEquations s)) ≤
        @standardAffineChartIdeal 13 s.1 ⟨hprime s.1 s.2⟩
          (projectiveSpecialFiberIdeal I))
    (hclear : ∀ (s : {s // s ∈ P})
        (f : MvPolynomial (Fin 13) (ZMod s.1)),
      f ∈ @standardAffineChartIdeal 13 s.1 ⟨hprime s.1 s.2⟩
          (projectiveSpecialFiberIdeal I) →
      u s * f ∈ Ideal.span (Set.range (localEquations s)))
    (hu : ∀ s,
      MvPolynomial.aeval
        (@standardAffineChartPoint 13 s.1 ⟨hprime s.1 s.2⟩
          (reservoirAffineProjectivePoint P rho s)) (u s) ≠ 0)
    (hminor : ∀ s,
      MvPolynomial.aeval
        (@standardAffineChartPoint 13 s.1 ⟨hprime s.1 s.2⟩
          (reservoirAffineProjectivePoint P rho s))
        (selectedJacobianDeterminant
          (localEquations s) (selectedVar s)) ≠ 0) :
    ∀ s : {s // s ∈ P},
      HasHilbertSamuelMultiplicityAt (hprime s.1 s.2)
        (projectiveSpecialFiberIdeal I)
        (reservoirAffineProjectivePoint P rho s) 2 1 := by
  obtain ⟨z, hz⟩ := hnonempty
  intro s
  letI : Fact s.1.Prime := ⟨hprime s.1 s.2⟩
  have hpoint :=
    rankSevenSourceComponent_reservoirAffinePoint_isPointOnSpecialFiber
      Z P hprime rho I hz s
  simpa using
    (hasHilbertSamuelMultiplicityAt_one_of_local_equations_selectedJacobian
      (hprime s.1 s.2) (projectiveSpecialFiberIdeal I)
      (reservoirAffineProjectivePoint P rho s) hpoint
      (localEquations s) (selectedVar s) (hselected s) (u s)
      (hIJ s) (hclear s) (hu s) (hminor s))

/-- The normalized chart definition supplies the real box hypothesis for
each of its residue packets at the same integral side used in the tangent
argument. -/
theorem depthSevenNormalizedChartResiduePacket_realBox
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (P : Finset ℕ) (rho : Fin 13 → ZMod (primeProduct P)) :
    ∀ z ∈ integralResiduePacket
        (depthSevenNormalizedJacobianChartCell p x₀ equations CF C) rho,
      ∀ i, |(z i : ℝ)| ≤ (2 * surfaceTangentNaturalSide p : ℕ) := by
  intro z hz i
  have hnat := depthSevenNormalized_coordinate_le_two_surfaceTangentNaturalSide
    p x₀ equations CF
      ((mem_depthSevenNormalizedJacobianChartCell_iff
        p x₀ equations CF C z).mp
          (mem_integralResiduePacket_iff.mp hz).1).1 i
  have hreal : ((z i).natAbs : ℝ) ≤
      ((2 * surfaceTangentNaturalSide p : ℕ) : ℝ) := by
    exact_mod_cast hnat
  simpa only [Nat.cast_natAbs, Int.cast_abs] using hreal

/-- Dividing one normalized chart packet by its square-free modulus puts it
in the literal box of side `1 + 4 T / q`.  The added one changes a weak
inequality into the strict inequality required by Pila's theorem. -/
theorem depthSevenNormalizedChartResiduePacket_quotientBox
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (P : Finset ℕ) (hprime : ∀ s ∈ P, s.Prime)
    (rho : Fin 13 → ZMod (primeProduct P))
    (hrho : rho ∈ occupiedIntegralResidues (primeProduct P)
      (depthSevenNormalizedJacobianChartCell p x₀ equations CF C)) :
    ∀ z ∈ integralResiduePacket
        (depthSevenNormalizedJacobianChartCell p x₀ equations CF C) rho,
      ∀ i,
        |(congruenceDisplacementOrZero (primeProduct P)
          (integralResiduePacketBase
            (depthSevenNormalizedJacobianChartCell p x₀ equations CF C)
            rho hrho) z i : ℝ)| <
          1 + (4 * surfaceTangentNaturalSide p : ℝ) / primeProduct P := by
  intro z hz i
  let Z := depthSevenNormalizedJacobianChartCell p x₀ equations CF C
  let base := integralResiduePacketBase Z rho hrho
  have hqpos : 0 < primeProduct P :=
    Nat.pos_of_ne_zero (primeProduct_ne_zero hprime)
  have hzcong : IntVectorCongruent (primeProduct P) z base :=
    intVectorCongruent_of_mem_same_integralResiduePacket hz
      (integralResiduePacketBase_mem Z rho hrho)
  have hzbox : ∀ j, |(z j : ℝ) - 0| ≤
      (2 * surfaceTangentNaturalSide p : ℕ) := by
    intro j
    simpa using depthSevenNormalizedChartResiduePacket_realBox
      p x₀ equations CF C P rho z hz j
  have hbasebox : ∀ j, |(base j : ℝ) - 0| ≤
      (2 * surfaceTangentNaturalSide p : ℕ) := by
    intro j
    simpa [base, Z] using depthSevenNormalizedChartResiduePacket_realBox
      p x₀ equations CF C P rho base
        (integralResiduePacketBase_mem Z rho hrho) j
  have hbound := congruenceDisplacementOrZero_coordinate_bound
    hqpos base z hzcong (center := fun _ ↦ 0)
      (R := (2 * surfaceTangentNaturalSide p : ℕ)) hzbox hbasebox i
  have hrewrite :
      2 * ((2 * surfaceTangentNaturalSide p : ℕ) : ℝ) /
          (primeProduct P : ℝ) =
        (4 * surfaceTangentNaturalSide p : ℝ) / primeProduct P := by
    norm_num
    ring
  rw [hrewrite] at hbound
  linarith

/-- The rank-seven Salberger--Pila estimate with its multiplicity premise
replaced by literal local equations for each actual reduced component.  The
several-prime numerical condition is written as the single real power of
the square-free reservoir modulus. -/
theorem rankSevenResiduePacketComponent_card_le_of_localEquations
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
    (localEquations : ∀ s : {s // s ∈ P},
      Fin 11 → MvPolynomial (Fin 13) (ZMod s.1))
    (selectedVar : ∀ _s : {s // s ∈ P}, Fin 11 → Fin 13)
    (hselected : ∀ s, Function.Injective (selectedVar s))
    (u : ∀ s : {s // s ∈ P}, MvPolynomial (Fin 13) (ZMod s.1))
    (hIJ : ∀ s,
      Ideal.span (Set.range (localEquations s)) ≤
        @standardAffineChartIdeal 13 s.1 ⟨hprime s.1 s.2⟩
          (projectiveSpecialFiberIdeal I))
    (hclear : ∀ (s : {s // s ∈ P})
        (f : MvPolynomial (Fin 13) (ZMod s.1)),
      f ∈ @standardAffineChartIdeal 13 s.1 ⟨hprime s.1 s.2⟩
          (projectiveSpecialFiberIdeal I) →
      u s * f ∈ Ideal.span (Set.range (localEquations s)))
    (hu : ∀ s,
      MvPolynomial.aeval
        (@standardAffineChartPoint 13 s.1 ⟨hprime s.1 s.2⟩
          (reservoirAffineProjectivePoint P rho s)) (u s) ≠ 0)
    (hminor : ∀ s,
      MvPolynomial.aeval
        (@standardAffineChartPoint 13 s.1 ⟨hprime s.1 s.2⟩
          (reservoirAffineProjectivePoint P rho s))
        (selectedJacobianDeterminant
          (localEquations s) (selectedVar s)) ≠ 0)
    (hproduct : B ^ (1 + εSalberger) ≤
      (primeProduct P : ℝ) ^
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
  apply rankSevenResiduePacketComponent_card_le_salbergerLines_add_pilaCurves
    hSalberger hPila x₀ hm equations hhomogeneous A Z P hprime rho I hI
      hnonempty hIdimensionDegree hεSalberger hεPila hB
  · exact rankSevenResiduePacketComponent_multiplicityOne_of_localEquations
      Z P hprime rho I hnonempty localEquations selectedVar hselected u
        hIJ hclear hu hminor
  · simpa only [primeSubtype_prod_natCast_rpow_eq_primeProduct] using hproduct
  · exact hbox

end
end TranslatedDepthSeven
