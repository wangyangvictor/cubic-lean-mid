import TranslatedDepthSeven.FixedConeOccupiedResidueCRT
import TranslatedDepthSeven.ConcreteTangentPacketCover
import TranslatedDepthSeven.SurfaceReservoirTangentBridge

/-!
# Occupied tangent packets for the literal depth-seven point set

Here the finite set of normalized points is exactly
`depthSevenNormalizedDisplacementFinset p x₀ equations CF`.  The first
lemmas extract its defining common-zero and box conditions.  They are then
inserted directly into the fixed-cone CRT estimate and the concrete
tangent-packet theorem.

Thus the indexing set is the literal finite set of occupied residue vectors,
not an abstract family of occurrences.  Its cardinality is at most
`H^ε q^6`, and, under the displayed rank-seven hypotheses, every indexed
packet is contained in a rational affine subspace of direction dimension at
most nine.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- Every normalized point in the literal target maps to a common integral
zero of the original equations. -/
theorem depthSevenNormalized_integralCommonZero
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {z : IntVector 13}
    (hz : z ∈ depthSevenNormalizedDisplacementFinset p x₀ equations CF) :
    IntegralCommonZero equations (integralAffineMap x₀ z p.m) := by
  classical
  have h := (Finset.mem_filter.mp hz).2
  dsimp only at h
  exact h.2.1

/-- Pointwise evaluation form of
`depthSevenNormalized_integralCommonZero`. -/
theorem depthSevenNormalized_eval_eq_zero
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {z : IntVector 13}
    (hz : z ∈ depthSevenNormalizedDisplacementFinset p x₀ equations CF)
    {g : MvPolynomial (Fin 13) ℤ} (hg : g ∈ equations) :
    MvPolynomial.eval (integralAffineMap x₀ z p.m) g = 0 :=
  depthSevenNormalized_integralCommonZero p x₀ equations CF hz g hg

/-- The affine image of a normalized target point lies in the literal
translated box. -/
theorem depthSevenNormalized_affineImage_mem_translatedBox
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {z : IntVector 13}
    (hz : z ∈ depthSevenNormalizedDisplacementFinset p x₀ equations CF) :
    p.InTranslatedBox
      (fun i ↦ (integralAffineMap x₀ z p.m i : ℝ)) := by
  classical
  have h := (Finset.mem_filter.mp hz).2
  dsimp only at h
  exact h.1

/-- Consequently every coordinate of the original affine image is bounded
by the explicit integral side used in the fixed equation certificate. -/
theorem depthSevenNormalized_affineImage_coordinate_le
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {z : IntVector 13}
    (hz : z ∈ depthSevenNormalizedDisplacementFinset p x₀ equations CF)
    (j : Fin 13) :
    (integralAffineMap x₀ z p.m j).natAbs ≤ ⌈p.B + p.L⌉₊ := by
  have hmem := mem_integerSupNormBox_of_mem_translatedBox p
    (integralAffineMap x₀ z p.m)
    (depthSevenNormalized_affineImage_mem_translatedBox
      p x₀ equations CF hz)
  exact (mem_integerSupNormBox_iff _).mp hmem j

/-- The exact fixed-cone CRT estimate for the occupied residue vectors of
the literal normalized depth-seven set. -/
theorem card_depthSevenNormalized_occupiedResidues_primeProduct_cast_le
    {M₀ ε : ℝ} (hM₀ : 0 ≤ M₀) (hε : 0 < ε)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (hprime : ∀ s ∈ P, s.Prime)
    (hgoodm : ∀ s ∈ P, ¬ s ∣ p.m)
    (hgoodden : ∀ s ∈ P, ¬ s ∣ model.denominator.natAbs)
    (hPcard : P.card ≤ reservoirDepth M₀ p.H)
    (hH : reservoirSubpowerThreshold M₀
      (model.localConstant : ℝ) ε ≤ p.H) :
    ((occupiedIntegralResidues (primeProduct P)
      (depthSevenNormalizedDisplacementFinset p x₀ equations CF)).card : ℝ)
      ≤ p.H ^ ε * (primeProduct P : ℝ) ^ 6 := by
  apply card_occupiedIntegralResidues_primeProduct_cast_le_rpow_mul
    hM₀ hε equations model
      (depthSevenNormalizedDisplacementFinset p x₀ equations CF)
      x₀ p.m
  · intro z hz g hg
    exact depthSevenNormalized_eval_eq_zero p x₀ equations CF hz hg
  · exact hprime
  · exact hgoodm
  · exact hgoodden
  · exact hPcard
  · exact hH

/-- Prime divisors of the literal reservoir modulus avoid the affine scale
when every prime used to form that modulus does. -/
theorem prime_dvd_primeProduct_not_dvd_scale
    (p : Parameters) (P : Finset ℕ)
    (hprime : ∀ s ∈ P, s.Prime)
    (hgoodm : ∀ s ∈ P, ¬ s ∣ p.m) :
    ∀ s, s.Prime → s ∣ primeProduct P → ¬ s ∣ p.m := by
  intro s hs hsprod
  apply hgoodm s
  rw [← primeFactors_primeProduct hprime]
  exact Nat.mem_primeFactors.mpr
    ⟨hs, hsprod, primeProduct_ne_zero hprime⟩

/-- Under literal rank-seven reduction at each occupied packet base, every
occupied packet is contained in a rational affine nine-plane. -/
theorem exists_ninePlane_for_each_depthSevenNormalized_occupiedPacket
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (P : Finset ℕ) (hprime : ∀ s ∈ P, s.Prime)
    (hgoodm : ∀ s ∈ P, ¬ s ∣ p.m)
    (hlower : manuscriptReservoirTarget normalizedSurfaceReservoirConstant
      p.T (5 / 7) ≤ primeProduct P)
    (hrank : ∀ (rho : Fin 13 → ZMod (primeProduct P)),
      (hrho : rho ∈ occupiedIntegralResidues (primeProduct P)
        (depthSevenNormalizedDisplacementFinset p x₀ equations CF)) →
      ∀ s, s.Prime → s ∣ primeProduct P →
        7 ≤ (jacobianMatrix (indexedFinsetFamily equations)
          (integralAffineMap x₀
            (integralResiduePacketBase
              (depthSevenNormalizedDisplacementFinset p x₀ equations CF)
              rho hrho) p.m) s).rank) :
    ∀ (rho : Fin 13 → ZMod (primeProduct P)),
      (hrho : rho ∈ occupiedIntegralResidues (primeProduct P)
        (depthSevenNormalizedDisplacementFinset p x₀ equations CF)) →
      ∃ A : AffineSubspace ℚ (Fin 13 → ℚ),
        Module.finrank ℚ A.direction ≤ 9 ∧
        ∀ z ∈ integralResiduePacket
            (depthSevenNormalizedDisplacementFinset p x₀ equations CF) rho,
          (fun j ↦ (z j : ℚ)) ∈ A := by
  intro rho hrho
  apply exists_surface_affineSubspace_for_occupied_packet
    equations x₀ p.m (primeProduct P) (surfaceTangentNaturalSide p)
      (depthSevenNormalizedDisplacementFinset p x₀ equations CF)
  · exact one_le_surfaceTangentNaturalSide p
  · exact Nat.pos_of_ne_zero (primeProduct_ne_zero hprime)
  · exact primeProduct_squarefree hprime
  · exact surfaceTangentQThreshold_le_of_normalized_reservoir_lower p hlower
  · intro z hz
    exact depthSevenNormalized_integralCommonZero p x₀ equations CF hz
  · intro z hz
    exact depthSevenNormalized_coordinate_le_two_surfaceTangentNaturalSide
      p x₀ equations CF hz
  · exact prime_dvd_primeProduct_not_dvd_scale p P hprime hgoodm
  · exact hrank rho hrho

/-- The preceding affine spaces may be chosen simultaneously and indexed by
the literal subtype of occupied residue vectors. -/
theorem exists_ninePlanes_indexed_by_depthSevenNormalized_occupiedResidues
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (P : Finset ℕ) (hprime : ∀ s ∈ P, s.Prime)
    (hgoodm : ∀ s ∈ P, ¬ s ∣ p.m)
    (hlower : manuscriptReservoirTarget normalizedSurfaceReservoirConstant
      p.T (5 / 7) ≤ primeProduct P)
    (hrank : ∀ (rho : Fin 13 → ZMod (primeProduct P)),
      (hrho : rho ∈ occupiedIntegralResidues (primeProduct P)
        (depthSevenNormalizedDisplacementFinset p x₀ equations CF)) →
      ∀ s, s.Prime → s ∣ primeProduct P →
        7 ≤ (jacobianMatrix (indexedFinsetFamily equations)
          (integralAffineMap x₀
            (integralResiduePacketBase
              (depthSevenNormalizedDisplacementFinset p x₀ equations CF)
              rho hrho) p.m) s).rank) :
    ∃ planes :
        {rho // rho ∈ occupiedIntegralResidues (primeProduct P)
          (depthSevenNormalizedDisplacementFinset p x₀ equations CF)} →
          AffineSubspace ℚ (Fin 13 → ℚ),
      ∀ rho,
        Module.finrank ℚ (planes rho).direction ≤ 9 ∧
        ∀ z ∈ integralResiduePacket
            (depthSevenNormalizedDisplacementFinset p x₀ equations CF) rho.1,
          (fun j ↦ (z j : ℚ)) ∈ planes rho := by
  classical
  have hplane : ∀ rho :
      {rho // rho ∈ occupiedIntegralResidues (primeProduct P)
        (depthSevenNormalizedDisplacementFinset p x₀ equations CF)},
      ∃ A : AffineSubspace ℚ (Fin 13 → ℚ),
        Module.finrank ℚ A.direction ≤ 9 ∧
        ∀ z ∈ integralResiduePacket
            (depthSevenNormalizedDisplacementFinset p x₀ equations CF) rho.1,
          (fun j ↦ (z j : ℚ)) ∈ A := by
    intro rho
    exact exists_ninePlane_for_each_depthSevenNormalized_occupiedPacket
      p x₀ equations CF P hprime hgoodm hlower
        (fun sigma hsigma ↦ hrank sigma hsigma) rho.1 rho.2
  choose planes hplanes using hplane
  exact ⟨planes, hplanes⟩

/-- Combined literal packet cover: the indexing subtype has cardinality at
most `H^ε q^6`, and every one of its packets lies in its chosen rational
affine nine-plane. -/
theorem exists_depthSevenNormalized_packetCover_with_card_bound
    {M₀ ε : ℝ} (hM₀ : 0 ≤ M₀) (hε : 0 < ε)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (hprime : ∀ s ∈ P, s.Prime)
    (hgoodm : ∀ s ∈ P, ¬ s ∣ p.m)
    (hgoodden : ∀ s ∈ P, ¬ s ∣ model.denominator.natAbs)
    (hPcard : P.card ≤ reservoirDepth M₀ p.H)
    (hH : reservoirSubpowerThreshold M₀
      (model.localConstant : ℝ) ε ≤ p.H)
    (hlower : manuscriptReservoirTarget normalizedSurfaceReservoirConstant
      p.T (5 / 7) ≤ primeProduct P)
    (hrank : ∀ (rho : Fin 13 → ZMod (primeProduct P)),
      (hrho : rho ∈ occupiedIntegralResidues (primeProduct P)
        (depthSevenNormalizedDisplacementFinset p x₀ equations CF)) →
      ∀ s, s.Prime → s ∣ primeProduct P →
        7 ≤ (jacobianMatrix (indexedFinsetFamily equations)
          (integralAffineMap x₀
            (integralResiduePacketBase
              (depthSevenNormalizedDisplacementFinset p x₀ equations CF)
              rho hrho) p.m) s).rank) :
    ∃ planes :
        {rho // rho ∈ occupiedIntegralResidues (primeProduct P)
          (depthSevenNormalizedDisplacementFinset p x₀ equations CF)} →
          AffineSubspace ℚ (Fin 13 → ℚ),
      ((Fintype.card
        {rho // rho ∈ occupiedIntegralResidues (primeProduct P)
          (depthSevenNormalizedDisplacementFinset p x₀ equations CF)} : ℕ) : ℝ)
          ≤ p.H ^ ε * (primeProduct P : ℝ) ^ 6 ∧
      ∀ rho,
        Module.finrank ℚ (planes rho).direction ≤ 9 ∧
        ∀ z ∈ integralResiduePacket
            (depthSevenNormalizedDisplacementFinset p x₀ equations CF) rho.1,
          (fun j ↦ (z j : ℚ)) ∈ planes rho := by
  obtain ⟨planes, hplanes⟩ :=
    exists_ninePlanes_indexed_by_depthSevenNormalized_occupiedResidues
      p x₀ equations CF P hprime hgoodm hlower hrank
  refine ⟨planes, ?_, hplanes⟩
  simpa only [Fintype.card_coe] using
    card_depthSevenNormalized_occupiedResidues_primeProduct_cast_le
      hM₀ hε p x₀ equations CF model P hprime hgoodm hgoodden hPcard hH

/-- At each rationally rank-seven occupied base point, the literal equation
height bound furnishes a nonzero integral minor.  If the fixed reservoir
modulus is coprime to the scale and to that minor, the packet lies in a
rational affine nine-plane. -/
theorem exists_bounded_certificate_for_depthSevenNormalized_occupiedPacket
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (P : Finset ℕ) (hprime : ∀ s ∈ P, s.Prime)
    (hlower : manuscriptReservoirTarget normalizedSurfaceReservoirConstant
      p.T (5 / 7) ≤ primeProduct P)
    (rho : Fin 13 → ZMod (primeProduct P))
    (hrho : rho ∈ occupiedIntegralResidues (primeProduct P)
      (depthSevenNormalizedDisplacementFinset p x₀ equations CF))
    (hregular : IsDepthSevenJacobianRegularAt equations
      (integralAffineMap x₀
        (integralResiduePacketBase
          (depthSevenNormalizedDisplacementFinset p x₀ equations CF)
          rho hrho) p.m)) :
    ∃ rows : Fin 7 → Fin equations.card,
      ∃ cols : Fin 7 → Fin 13,
        Function.Injective rows ∧ Function.Injective cols ∧
        integralJacobianMinor (indexedFinsetFamily equations)
          (integralAffineMap x₀
            (integralResiduePacketBase
              (depthSevenNormalizedDisplacementFinset p x₀ equations CF)
              rho hrho) p.m) rows cols ≠ 0 ∧
        (integralJacobianMinor (indexedFinsetFamily equations)
          (integralAffineMap x₀
            (integralResiduePacketBase
              (depthSevenNormalizedDisplacementFinset p x₀ equations CF)
              rho hrho) p.m) rows cols).natAbs ≤
          Nat.factorial 7 *
            (equationFamilySupportBound equations *
              equationFamilyDegreeBound equations *
              equationFamilyCoefficientBound equations *
              max 1 ⌈p.B + p.L⌉₊ ^ equationFamilyDegreeBound equations) ^ 7 ∧
        (Nat.Coprime (primeProduct P) p.m →
          Nat.Coprime (primeProduct P)
            (integralJacobianMinor (indexedFinsetFamily equations)
              (integralAffineMap x₀
                (integralResiduePacketBase
                  (depthSevenNormalizedDisplacementFinset p x₀ equations CF)
                  rho hrho) p.m) rows cols).natAbs →
          ∃ A : AffineSubspace ℚ (Fin 13 → ℚ),
            Module.finrank ℚ A.direction ≤ 9 ∧
            ∀ z ∈ integralResiduePacket
                (depthSevenNormalizedDisplacementFinset p x₀ equations CF) rho,
              (fun j ↦ (z j : ℚ)) ∈ A) := by
  apply exists_bounded_certificate_for_occupied_packet_then_surface_plane
    equations x₀ p.m (primeProduct P) (surfaceTangentNaturalSide p)
      ⌈p.B + p.L⌉₊
      (depthSevenNormalizedDisplacementFinset p x₀ equations CF)
  · exact one_le_surfaceTangentNaturalSide p
  · exact Nat.pos_of_ne_zero (primeProduct_ne_zero hprime)
  · exact primeProduct_squarefree hprime
  · exact surfaceTangentQThreshold_le_of_normalized_reservoir_lower p hlower
  · intro z hz
    exact depthSevenNormalized_integralCommonZero p x₀ equations CF hz
  · intro z hz
    exact depthSevenNormalized_coordinate_le_two_surfaceTangentNaturalSide
      p x₀ equations CF hz
  · exact hregular
  · intro j
    exact depthSevenNormalized_affineImage_coordinate_le
      p x₀ equations CF
        (mem_integralResiduePacket_iff.mp
          (integralResiduePacketBase_mem
            (depthSevenNormalizedDisplacementFinset p x₀ equations CF)
            rho hrho)).1 j

end

end TranslatedDepthSeven
