import TranslatedDepthSeven.ManuscriptModulusReservoir
import TranslatedDepthSeven.DepthSevenNormalizedJacobianPartition
import Mathlib.Data.ZMod.Coprime

namespace TranslatedDepthSeven

noncomputable section

theorem zmod_eval_eq_of_coordinate_cast_eq
    {n q : ℕ} (f : MvPolynomial (Fin n) ℤ)
    (x y : Fin n → ℤ)
    (hxy : ∀ i, (x i : ZMod q) = (y i : ZMod q)) :
    (MvPolynomial.eval x f : ZMod q) = MvPolynomial.eval y f := by
  have hx := MvPolynomial.eval₂_comp_left
    (Int.castRingHom (ZMod q)) (RingHom.id ℤ) x f
  have hy := MvPolynomial.eval₂_comp_left
    (Int.castRingHom (ZMod q)) (RingHom.id ℤ) y f
  rw [MvPolynomial.eval₂_id] at hx hy
  change (Int.castRingHom (ZMod q)) (MvPolynomial.eval x f) =
    (Int.castRingHom (ZMod q)) (MvPolynomial.eval y f)
  rw [hx, hy]
  congr 1
  funext i
  exact hxy i

theorem coprime_eval_natAbs_of_coordinate_cast_eq
    {n q : ℕ} (f : MvPolynomial (Fin n) ℤ)
    (x y : Fin n → ℤ)
    (hxy : ∀ i, (x i : ZMod q) = (y i : ZMod q))
    (hcop : Nat.Coprime q (MvPolynomial.eval x f).natAbs) :
    Nat.Coprime q (MvPolynomial.eval y f).natAbs := by
  have heq := zmod_eval_eq_of_coordinate_cast_eq f x y hxy
  have hu : IsUnit ((MvPolynomial.eval x f : ℤ) : ZMod q) := by
    rw [ZMod.coe_int_isUnit_iff_isCoprime,
      Int.isCoprime_iff_nat_coprime]
    simpa using hcop
  rw [heq] at hu
  rw [ZMod.coe_int_isUnit_iff_isCoprime] at hu
  rw [Int.isCoprime_iff_nat_coprime] at hu
  simpa using hu

/-- Determinant coprimality at a chart point passes to any occupied-packet
base whose affine image is coordinatewise congruent modulo the same
composite modulus. -/
theorem coprime_chartDeterminant_at_packetBase
    {q : ℕ} (p : Parameters) (x₀ z base : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (hcongr : ∀ i,
      (integralAffineMap x₀ z p.m i : ZMod q) =
        (integralAffineMap x₀ base p.m i : ZMod q))
    (hcop : Nat.Coprime q
      (MvPolynomial.eval (integralAffineMap x₀ z p.m)
        C.determinant).natAbs) :
    Nat.Coprime q
      (MvPolynomial.eval (integralAffineMap x₀ base p.m)
        C.determinant).natAbs := by
  exact coprime_eval_natAbs_of_coordinate_cast_eq C.determinant
    (integralAffineMap x₀ z p.m) (integralAffineMap x₀ base p.m)
    hcongr hcop

/-- The points of one literal rank-seven chart for which one reservoir
modulus avoids both the fixed scale/denominator certificate and the chart
determinant evaluated at that point. -/
def rankSevenChartReservoirCell
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (q : ℕ) : Finset (IntVector 13) := by
  classical
  exact (depthSevenNormalizedJacobianChartCell p x₀ equations CF C).filter
    fun z ↦ Nat.Coprime q ((p.m : ℤ) * denominator).natAbs ∧
      Nat.Coprime q
        (MvPolynomial.eval (integralAffineMap x₀ z p.m)
          C.determinant).natAbs

/-- A pointwise surviving modulus gives an exact finite cover of the chart
cell by the static two-certificate cells. -/
theorem rankSevenChartCell_eq_biUnion_reservoirCells
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (reservoir : Finset ℕ)
    (hsurvives : ∀ z ∈ depthSevenNormalizedJacobianChartCell
        p x₀ equations CF C,
      ∃ q ∈ reservoir,
        Nat.Coprime q ((p.m : ℤ) * denominator).natAbs ∧
        Nat.Coprime q
          (MvPolynomial.eval (integralAffineMap x₀ z p.m)
            C.determinant).natAbs) :
    depthSevenNormalizedJacobianChartCell p x₀ equations CF C =
      reservoir.biUnion
        (rankSevenChartReservoirCell p x₀ equations CF C denominator) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨q, hq, hcop⟩ := hsurvives z hz
    exact Finset.mem_biUnion.mpr
      ⟨q, hq, Finset.mem_filter.mpr ⟨hz, hcop⟩⟩
  · intro hz
    obtain ⟨q, _hq, hzq⟩ := Finset.mem_biUnion.mp hz
    exact (Finset.mem_filter.mp hzq).1

/-- Corresponding cardinal inequality, with no assignment or stopping
construction: it is just the cardinality of a finite union. -/
theorem card_rankSevenChartCell_le_sum_reservoirCells
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (reservoir : Finset ℕ)
    (hsurvives : ∀ z ∈ depthSevenNormalizedJacobianChartCell
        p x₀ equations CF C,
      ∃ q ∈ reservoir,
        Nat.Coprime q ((p.m : ℤ) * denominator).natAbs ∧
        Nat.Coprime q
          (MvPolynomial.eval (integralAffineMap x₀ z p.m)
            C.determinant).natAbs) :
    (depthSevenNormalizedJacobianChartCell p x₀ equations CF C).card ≤
      ∑ q ∈ reservoir,
        (rankSevenChartReservoirCell
          p x₀ equations CF C denominator q).card := by
  rw [rankSevenChartCell_eq_biUnion_reservoirCells
    p x₀ equations CF C denominator reservoir hsurvives]
  exact Finset.card_biUnion_le

/-- Literal specialization of the manuscript reservoir's two-certificate
survival clause. -/
theorem exists_reservoirModulus_coprime_two_certificates
    {P : Finset ℕ} {k : ℕ} (hP : ∀ s ∈ P, s.Prime)
    {H A : ℝ}
    (hsurvival : ∀ D₁ D₂ : ℤ, D₁ ≠ 0 → D₂ ≠ 0 →
      (D₁.natAbs : ℝ) ≤ H ^ A → (D₂.natAbs : ℝ) ≤ H ^ A →
      Nonempty (ReservoirModulus
        (certificateAllowedPrimesTwo P D₁ D₂) k))
    (D₁ D₂ : ℤ) (hD₁ : D₁ ≠ 0) (hD₂ : D₂ ≠ 0)
    (hD₁size : (D₁.natAbs : ℝ) ≤ H ^ A)
    (hD₂size : (D₂.natAbs : ℝ) ≤ H ^ A) :
    ∃ q ∈ modulusReservoir P k,
      Nat.Coprime q D₁.natAbs ∧ Nat.Coprime q D₂.natAbs := by
  let allowed := certificateAllowedPrimesTwo P D₁ D₂
  obtain ⟨q⟩ := hsurvival D₁ D₂ hD₁ hD₂ hD₁size hD₂size
  have hq := (mem_certificateAllowedTwo_modulusReservoir_iff
    hP D₁ D₂).mp q.2
  exact ⟨q.1, hq.1, hq.2.1, hq.2.2⟩

/-- Pointwise two-certificate survival instantiates the exact static chart
cover and its cardinal inequality.  All height and nonvanishing conditions
are displayed explicitly; they are precisely the final clause returned by
`eventually_exists_manuscriptModulusReservoir`. -/
theorem card_rankSevenChartCell_le_sum_reservoirCells_of_twoCertificateSurvival
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime) (H A : ℝ)
    (hsurvival : ∀ D₁ D₂ : ℤ, D₁ ≠ 0 → D₂ ≠ 0 →
      (D₁.natAbs : ℝ) ≤ H ^ A → (D₂.natAbs : ℝ) ≤ H ^ A →
      Nonempty (ReservoirModulus
        (certificateAllowedPrimesTwo P D₁ D₂) k))
    (hfixedNe : (p.m : ℤ) * denominator ≠ 0)
    (hfixedSize : ((((p.m : ℤ) * denominator).natAbs : ℕ) : ℝ) ≤ H ^ A)
    (hdetNe : ∀ z ∈ depthSevenNormalizedJacobianChartCell
      p x₀ equations CF C,
      MvPolynomial.eval (integralAffineMap x₀ z p.m) C.determinant ≠ 0)
    (hdetSize : ∀ z ∈ depthSevenNormalizedJacobianChartCell
      p x₀ equations CF C,
      (((MvPolynomial.eval (integralAffineMap x₀ z p.m)
        C.determinant).natAbs : ℕ) : ℝ) ≤ H ^ A) :
    (depthSevenNormalizedJacobianChartCell p x₀ equations CF C).card ≤
      ∑ q ∈ modulusReservoir P k,
        (rankSevenChartReservoirCell
          p x₀ equations CF C denominator q).card := by
  apply card_rankSevenChartCell_le_sum_reservoirCells
  intro z hz
  exact exists_reservoirModulus_coprime_two_certificates hP hsurvival
    ((p.m : ℤ) * denominator)
    (MvPolynomial.eval (integralAffineMap x₀ z p.m) C.determinant)
    hfixedNe (hdetNe z hz) hfixedSize (hdetSize z hz)

end

end TranslatedDepthSeven
