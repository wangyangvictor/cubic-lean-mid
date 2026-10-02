import TranslatedDepthSeven.RankSevenPersistentOccupiedResidueBound
import TranslatedDepthSeven.StrictRankSevenFiniteRecordBridge

/-!
# The rank-seven record occurrence scale

The reservoir construction supplies two elementary facts: there are at most
`2 * H^δ` vertices and directed edges altogether, and every relevant
modulus (or edge lcm) is at most a fixed constant times
`T^(5/7) * H^δ`.  The fixed-cone CRT estimate contributes one further
factor `H^δ` and the sixth power of that modulus.  This file records the
resulting exact calculation

`H^δ * H^δ * (T^(5/7) * H^δ)^6 = T^(30/7) * H^(8δ)`.

No geometric counting theorem is used here.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- A finite family with `O(H^δ)` members, each carrying an occurrence mass
`H^δ q^6`, and with `q = O(T^(5/7) H^δ)`, has total occurrence mass
`O(T^(30/7) H^(8δ))`. -/
theorem finite_sum_sixth_power_at_reservoir_scale
    {ι : Type} [Fintype ι]
    {H T C δ M : ℝ}
    (hH : 0 < H) (hT : 0 ≤ T) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hcard : (Fintype.card ι : ℝ) ≤ 2 * H ^ δ)
    (q : ι → ℝ) (hqnonneg : ∀ i, 0 ≤ q i)
    (hqupper : ∀ i, q i ≤ C * T ^ (5 / 7 : ℝ) * H ^ δ) :
    (∑ i : ι, H ^ δ * (q i) ^ 6 * M) ≤
      2 * C ^ 6 * M * T ^ (30 / 7 : ℝ) * H ^ (8 * δ) := by
  have hHpow : 0 ≤ H ^ δ := Real.rpow_nonneg hH.le δ
  have hTpow : 0 ≤ T ^ (5 / 7 : ℝ) :=
    Real.rpow_nonneg hT (5 / 7 : ℝ)
  have hbase : 0 ≤ C * T ^ (5 / 7 : ℝ) * H ^ δ := by positivity
  calc
    (∑ i : ι, H ^ δ * (q i) ^ 6 * M) ≤
        ∑ _i : ι,
          H ^ δ * (C * T ^ (5 / 7 : ℝ) * H ^ δ) ^ 6 * M := by
      apply Finset.sum_le_sum
      intro i _hi
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (hqnonneg i) (hqupper i) 6) hHpow)
        hM
    _ = (Fintype.card ι : ℝ) *
        (H ^ δ * (C * T ^ (5 / 7 : ℝ) * H ^ δ) ^ 6 * M) := by
      simp
    _ ≤ (2 * H ^ δ) *
        (H ^ δ * (C * T ^ (5 / 7 : ℝ) * H ^ δ) ^ 6 * M) := by
      exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 2 * C ^ 6 * M * T ^ (30 / 7 : ℝ) * H ^ (8 * δ) := by
      rw [mul_pow, mul_pow]
      rw [← Real.rpow_mul_natCast hT (5 / 7 : ℝ) 6]
      rw [← Real.rpow_mul_natCast hH.le δ 6]
      rw [show (5 / 7 : ℝ) * (6 : ℕ) = 30 / 7 by norm_num]
      rw [show δ * (6 : ℕ) = 6 * δ by ring]
      rw [show 8 * δ = δ + δ + 6 * δ by ring,
        Real.rpow_add hH, Real.rpow_add hH]
      ring

/-- The vertex part of the manuscript family bound also bounds the literal
finite type of reservoir moduli. -/
theorem reservoirModulus_card_cast_le_of_family_bound
    {H δ : ℝ} {P : Finset ℕ} {k : ℕ}
    (hP : ∀ s ∈ P, s.Prime)
    (hfamily : ((((modulusReservoir P k).card +
      (modulusReservoirDirectedEdges P k hP).card : ℕ) : ℝ) ≤
        2 * H ^ δ)) :
    (Fintype.card (ReservoirModulus P k) : ℝ) ≤ 2 * H ^ δ := by
  calc
    (Fintype.card (ReservoirModulus P k) : ℝ) =
        ((modulusReservoir P k).card : ℝ) := by
      rw [card_reservoirModulus hP k,
        card_modulusReservoir_of_primes hP k]
    _ ≤ (((modulusReservoir P k).card +
        (modulusReservoirDirectedEdges P k hP).card : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_right _ _
    _ ≤ 2 * H ^ δ := hfamily

/-- Occupancy descends along reduction of the modulus. -/
theorem reduceResidueVector_mem_occupiedIntegralResidues
    {N q R : ℕ} (h : q ∣ R) (Z : Finset (IntVector N))
    {rho : Fin N → ZMod R}
    (hrho : rho ∈ occupiedIntegralResidues R Z) :
    reduceResidueVector h rho ∈ occupiedIntegralResidues q Z := by
  obtain ⟨z, hz, hzr⟩ := mem_occupiedIntegralResidues_iff.mp hrho
  refine mem_occupiedIntegralResidues_iff.mpr ⟨z, hz, ?_⟩
  rw [← hzr]
  exact (reduceResidueVector_integralResidueVector h z).symm

/-- The directed-edge part of the manuscript family bound controls the
literal finite type of adjacent ordered pairs. -/
theorem reservoirDirectedEdge_card_cast_le_of_family_bound
    {H δ : ℝ} {P : Finset ℕ} {k : ℕ}
    (hP : ∀ s ∈ P, s.Prime)
    (hfamily : ((((modulusReservoir P k).card +
      (modulusReservoirDirectedEdges P k hP).card : ℕ) : ℝ) ≤
        2 * H ^ δ)) :
    (Fintype.card (↑(modulusReservoirDirectedEdges P k hP)) : ℝ) ≤
      2 * H ^ δ := by
  calc
    (Fintype.card (↑(modulusReservoirDirectedEdges P k hP)) : ℝ) =
        ((modulusReservoirDirectedEdges P k hP).card : ℝ) := by simp
    _ ≤ (((modulusReservoir P k).card +
        (modulusReservoirDirectedEdges P k hP).card : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_left _ _
    _ ≤ 2 * H ^ δ := hfamily

/-- Summing the exact fixed-cone occurrence estimate over all surviving
non-surface node records gives the canonical `T^(30/7)` occurrence scale. -/
theorem sum_occupiedRankSevenSurvivingNonSurfaceNodeRecords_cast_le_scale
    {M₀ δ C₀ : ℝ} (hM₀ : 0 ≤ M₀) (hδ : 0 < δ) (hC₀ : 0 ≤ C₀)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k : ℕ) (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (D : ℕ)
    (hcomponents : ∀ (q : ReservoirModulus P k)
        (rho : Fin 13 → ZMod q.1),
      rho ∈ occupiedIntegralResidues q.1
          (depthSevenNormalizedJacobianChartCell p x₀ equations CF C) →
      (rankSevenNonSurfaceNodeComponents
        p x₀ equations CF C q.1 rho).card ≤ D)
    (hk : k ≤ reservoirDepth M₀ p.H)
    (hH : reservoirSubpowerThreshold M₀
      (model.localConstant : ℝ) δ ≤ p.H)
    (hfamily : ((((modulusReservoir P k).card +
      (modulusReservoirDirectedEdges P k hP).card : ℕ) : ℝ) ≤
        2 * p.H ^ δ))
    (hupper : ∀ q : ReservoirModulus P k,
      (q.1 : ℝ) ≤ C₀ * p.T ^ (5 / 7 : ℝ) * p.H ^ δ) :
    (∑ q : ReservoirModulus P k,
      ((occupiedRankSevenSurvivingNonSurfaceNodeRecords
        p x₀ equations CF C model.denominator P k hP hlower q).card : ℝ)) ≤
      2 * C₀ ^ 6 * D * p.T ^ (30 / 7 : ℝ) * p.H ^ (8 * δ) := by
  calc
    (∑ q : ReservoirModulus P k,
      ((occupiedRankSevenSurvivingNonSurfaceNodeRecords
        p x₀ equations CF C model.denominator P k hP hlower q).card : ℝ)) ≤
        ∑ q : ReservoirModulus P k,
          p.H ^ δ * (q.1 : ℝ) ^ 6 * D := by
      apply Finset.sum_le_sum
      intro q _hq
      exact card_occupiedRankSevenSurvivingNonSurfaceNodeRecords_cast_le
        hM₀ hδ p x₀ equations CF C model P k hP hlower q D
          (hcomponents q) hk hH
    _ ≤ 2 * C₀ ^ 6 * D * p.T ^ (30 / 7 : ℝ) *
        p.H ^ (8 * δ) := by
      exact finite_sum_sixth_power_at_reservoir_scale
        p.H_pos p.T_pos.le hC₀ (Nat.cast_nonneg D)
          (reservoirModulus_card_cast_le_of_family_bound hP hfamily)
          (fun q : ReservoirModulus P k ↦ (q.1 : ℝ))
          (fun q ↦ Nat.cast_nonneg q.1) hupper

/-- The retained persistent records satisfy the same occurrence estimate;
the finite mark menu and component-degree mass remain as explicit constant
factors. -/
theorem card_occupiedRankSevenPersistentMultiplicityOneRecords_cast_le_scale
    {M₀ δ C₀ : ℝ} (hM₀ : 0 ≤ M₀) (hδ : 0 < δ) (hC₀ : 0 ≤ C₀)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k markCount D : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13))
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (hcomponents : ∀ (q : ReservoirModulus P k)
        (rho : Fin 13 → ZMod q.1),
      rho ∈ occupiedIntegralResidues q.1
          (depthSevenNormalizedJacobianChartCell p x₀ equations CF C) →
      (rankSevenSurfaceNodeComponents
        p x₀ equations CF C q.1 rho).card ≤ D)
    (hk : k ≤ reservoirDepth M₀ p.H)
    (hH : reservoirSubpowerThreshold M₀
      (model.localConstant : ℝ) δ ≤ p.H)
    (hfamily : ((((modulusReservoir P k).card +
      (modulusReservoirDirectedEdges P k hP).card : ℕ) : ℝ) ≤
        2 * p.H ^ δ))
    (hupper : ∀ q : ReservoirModulus P k,
      (q.1 : ℝ) ≤ C₀ * p.T ^ (5 / 7 : ℝ) * p.H ^ δ) :
    ((occupiedRankSevenPersistentMultiplicityOneRecords
      p x₀ equations CF C model.denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf).card : ℝ) ≤
      2 * C₀ ^ 6 * (D * markCount) * p.T ^ (30 / 7 : ℝ) *
        p.H ^ (8 * δ) := by
  apply (card_occupiedRankSevenPersistentMultiplicityOneRecords_cast_le_sum
    hM₀ hδ p x₀ equations CF C model P k markCount D hP hlower X
      localEquations selectedVar menu markOf hcomponents hk hH).trans
  exact finite_sum_sixth_power_at_reservoir_scale
    p.H_pos p.T_pos.le hC₀
      (mul_nonneg (Nat.cast_nonneg D) (Nat.cast_nonneg markCount))
      (reservoirModulus_card_cast_le_of_family_bound hP hfamily)
      (fun q : ReservoirModulus P k ↦ (q.1 : ℝ))
      (fun q ↦ Nat.cast_nonneg q.1) hupper

/-- Summing the fixed-cone occurrence estimate over the actual directed
edge set gives the same canonical scale.  The component bound is required
only for the literal node component lists; occupancy at the two endpoint
moduli follows by reducing the occupied lcm residue. -/
theorem sum_occupiedRankSevenSurvivingSurfaceEdgeRecords_over_edges_cast_le_scale
    {M₀ δ C₀ : ℝ} (hM₀ : 0 ≤ M₀) (hδ : 0 < δ) (hC₀ : 0 ≤ C₀)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k : ℕ) (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (D : ℕ)
    (hcomponents : ∀ (q : ReservoirModulus P k)
        (rho : Fin 13 → ZMod q.1),
      rho ∈ occupiedIntegralResidues q.1
          (depthSevenNormalizedJacobianChartCell p x₀ equations CF C) →
      (rankSevenSurfaceNodeComponents
        p x₀ equations CF C q.1 rho).card ≤ D)
    (hfactorDepth : 2 * k ≤ reservoirDepth M₀ p.H)
    (hH : reservoirSubpowerThreshold M₀
      (model.localConstant : ℝ) δ ≤ p.H)
    (hfamily : ((((modulusReservoir P k).card +
      (modulusReservoirDirectedEdges P k hP).card : ℕ) : ℝ) ≤
        2 * p.H ^ δ))
    (hmoduli : ∀ q : ReservoirModulus P k, Squarefree q.1)
    (hupper : ∀ q r : ReservoirModulus P k,
      (modulusReservoirGraph P k hP).Adj q r →
      (Nat.lcm q.1 r.1 : ℝ) ≤
        C₀ * p.T ^ (5 / 7 : ℝ) * p.H ^ δ) :
    (∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
      ((occupiedRankSevenSurvivingSurfaceEdgeRecords
        p x₀ equations CF C model.denominator P k hP hlower
          qr.1.1 qr.1.2).card : ℝ)) ≤
      2 * C₀ ^ 6 * (D * D) * p.T ^ (30 / 7 : ℝ) *
        p.H ^ (8 * δ) := by
  classical
  let Z := depthSevenNormalizedJacobianChartCell p x₀ equations CF C
  calc
    (∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
      ((occupiedRankSevenSurvivingSurfaceEdgeRecords
        p x₀ equations CF C model.denominator P k hP hlower
          qr.1.1 qr.1.2).card : ℝ)) ≤
        ∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
          p.H ^ δ * (Nat.lcm qr.1.1.1 qr.1.2.1 : ℝ) ^ 6 *
            (D * D) := by
      apply Finset.sum_le_sum
      intro qr _hqr
      have hleft : ∀ rho ∈ occupiedIntegralResidues
          (Nat.lcm qr.1.1.1 qr.1.2.1) Z,
          (rankSevenSurfaceNodeComponents p x₀ equations CF C qr.1.1.1
            (reduceResidueVector
              (Nat.dvd_lcm_left qr.1.1.1 qr.1.2.1) rho)).card ≤ D := by
        intro rho hrho
        exact hcomponents qr.1.1 _
          (reduceResidueVector_mem_occupiedIntegralResidues
            (Nat.dvd_lcm_left qr.1.1.1 qr.1.2.1) Z hrho)
      have hright : ∀ rho ∈ occupiedIntegralResidues
          (Nat.lcm qr.1.1.1 qr.1.2.1) Z,
          (rankSevenSurfaceNodeComponents p x₀ equations CF C qr.1.2.1
            (reduceResidueVector
              (Nat.dvd_lcm_right qr.1.1.1 qr.1.2.1) rho)).card ≤ D := by
        intro rho hrho
        exact hcomponents qr.1.2 _
          (reduceResidueVector_mem_occupiedIntegralResidues
            (Nat.dvd_lcm_right qr.1.1.1 qr.1.2.1) Z hrho)
      exact card_occupiedRankSevenSurvivingSurfaceEdgeRecords_cast_le
        hM₀ hδ p x₀ equations CF C model P k hP hlower qr.1.1 qr.1.2
          (hmoduli qr.1.1) (hmoduli qr.1.2) D hleft hright
          ((card_primeFactors_lcm_reservoir_le_two_mul hP
            qr.1.1 qr.1.2).trans hfactorDepth) hH
    _ ≤ 2 * C₀ ^ 6 * (D * D) * p.T ^ (30 / 7 : ℝ) *
        p.H ^ (8 * δ) := by
      apply finite_sum_sixth_power_at_reservoir_scale
        p.H_pos p.T_pos.le hC₀
          (mul_nonneg (Nat.cast_nonneg D) (Nat.cast_nonneg D))
          (reservoirDirectedEdge_card_cast_le_of_family_bound hP hfamily)
          (fun qr : ↑(modulusReservoirDirectedEdges P k hP) ↦
            (Nat.lcm qr.1.1.1 qr.1.2.1 : ℝ))
          (fun qr ↦ Nat.cast_nonneg (Nat.lcm qr.1.1.1 qr.1.2.1))
      intro qr
      exact hupper qr.1.1 qr.1.2 (Finset.mem_filter.mp qr.2).2

end

end TranslatedDepthSeven
