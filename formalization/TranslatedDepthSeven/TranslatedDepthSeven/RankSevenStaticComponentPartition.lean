import TranslatedDepthSeven.RankSevenStaticSectionChoice
import TranslatedDepthSeven.StrictChartReservoirBridge

/-!
# The literal static component partition on a rank-seven chart

For each normalized chart point `z` and each reservoir modulus surviving its
two certificates, `RankSevenStaticSectionChoice` supplies a fixed finite
source-section equation family containing the entire residue packet of `z`.
The connected deleted-prime reservoir partition may therefore be applied to
the actual selected minimal-prime components of those equations.

The vertex/off-locus term is empty, because `z` itself belongs to every
surviving source section.  What remains is the exact finite inequality by
distinct labels across a surviving directed edge and by one nonempty label
which persists over all surviving moduli.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The selected actual rational minimal-prime component of the source
section attached to `(q,z)`. -/
def rankSevenStaticSelectedComponent
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (z : IntVector 13) (q : ReservoirModulus P k) :
    Option (Ideal (MvPolynomial (Fin 14) ℚ)) :=
  selectedFiniteEquationComponent
    (rankSevenStaticSourceSectionEquations
      p x₀ equations CF C denominator P k hP hlower q z)
    (fun i ↦ (integralAffineChartVector z i : ℚ))

/-- The selected component is a literal function of the node `(q,ρ)`:
two integral lifts with the same residue vector modulo `q` have the same
source equations and the same affine evaluation point modulo no further
data.  The rational evaluation point is still different, so this statement
requires that the two integral lifts themselves coincide.  The useful
residue-only invariant is the source equation family above; component labels
through different rational lifts are intentionally not identified. -/
theorem rankSevenStaticSourceEquations_eq_of_residue_eq
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q : ReservoirModulus P k) (z w : IntVector 13)
    (hresidue : (integralResidueVector z : Fin 13 → ZMod q.1) =
      integralResidueVector w) :
    rankSevenStaticSourceSectionEquations
        p x₀ equations CF C denominator P k hP hlower q z =
      rankSevenStaticSourceSectionEquations
        p x₀ equations CF C denominator P k hP hlower q w :=
  rankSevenStaticSourceSectionEquations_eq_of_residue_eq
    p x₀ equations CF C denominator P k hP hlower q z w hresidue

/-- The finite set of nonempty-or-empty component labels which actually
occurs at a surviving point--modulus pair on one chart. -/
def occurringRankSevenStaticComponents
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1) :
    Finset (Option (Ideal (MvPolynomial (Fin 14) ℚ))) :=
  occurringCertificateDeletedLabels
    (depthSevenNormalizedJacobianChartCell p x₀ equations CF C)
    (fun _ ↦ (p.m : ℤ) * denominator)
    (fun z ↦ MvPolynomial.eval (integralAffineMap x₀ z p.m) C.determinant)
    (fun z q ↦ rankSevenStaticSelectedComponent
      p x₀ equations CF C denominator P k hP hlower z q)

/-- Static rank-seven component comparison, with pointwise connectedness
deduced from the exact two-certificate reservoir clause.

Every term is a literal finite set.  The first sum is absent because each
point lies on every source section indexed by a modulus surviving its two
certificates. -/
theorem card_rankSevenChart_le_edge_add_persistent_components
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (H A : ℝ)
    (hsurvival : ∀ E₁ E₂ : ℤ, E₁ ≠ 0 → E₂ ≠ 0 →
      (E₁.natAbs : ℝ) ≤ H ^ A → (E₂.natAbs : ℝ) ≤ H ^ A →
      Nonempty (ReservoirModulus
        (certificateAllowedPrimesTwo P E₁ E₂) k) ∧
      (modulusReservoirGraph
        (certificateAllowedPrimesTwo P E₁ E₂) k
        (fun s hs ↦ hP s (Finset.mem_filter.mp hs).1)).Connected)
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
      (∑ q : ReservoirModulus P k, ∑ r : ReservoirModulus P k,
        ((depthSevenNormalizedJacobianChartCell p x₀ equations CF C).filter
          fun z ↦
            survivesTwoCertificates q ((p.m : ℤ) * denominator)
              (MvPolynomial.eval (integralAffineMap x₀ z p.m)
                C.determinant) ∧
            survivesTwoCertificates r ((p.m : ℤ) * denominator)
              (MvPolynomial.eval (integralAffineMap x₀ z p.m)
                C.determinant) ∧
            (modulusReservoirGraph P k hP).Adj q r ∧
            rankSevenStaticSelectedComponent
                p x₀ equations CF C denominator P k hP hlower z q ≠
              rankSevenStaticSelectedComponent
                p x₀ equations CF C denominator P k hP hlower z r).card) +
      (∑ o ∈ occurringRankSevenStaticComponents
          p x₀ equations CF C denominator P k hP hlower,
        ((depthSevenNormalizedJacobianChartCell p x₀ equations CF C).filter
          fun z ↦ o ≠ none ∧ ∀ q : ReservoirModulus P k,
            survivesTwoCertificates q ((p.m : ℤ) * denominator)
              (MvPolynomial.eval (integralAffineMap x₀ z p.m)
                C.determinant) →
            rankSevenStaticSelectedComponent
              p x₀ equations CF C denominator P k hP hlower z q = o).card) := by
  let X := depthSevenNormalizedJacobianChartCell p x₀ equations CF C
  let D₁ : IntVector 13 → ℤ := fun _ ↦ (p.m : ℤ) * denominator
  let D₂ : IntVector 13 → ℤ := fun z ↦
    MvPolynomial.eval (integralAffineMap x₀ z p.m) C.determinant
  let family : IntVector 13 → ReservoirModulus P k →
      Finset (MvPolynomial (Fin 14) ℚ) := fun z q ↦
    rankSevenStaticSourceSectionEquations
      p x₀ equations CF C denominator P k hP hlower q z
  let coordinate : IntVector 13 → Fin 14 → ℚ := fun z i ↦
    (integralAffineChartVector z i : ℚ)
  have hpartition :=
    card_le_sum_certificateDeleted_equationComponents_of_survival
      hP H A hsurvival X D₁ D₂ family coordinate
      (fun _z _hz ↦ hfixedNe) hdetNe
      (fun _z _hz ↦ hfixedSize) hdetSize
  have hoff : (∑ q : ReservoirModulus P k,
      (X.filter fun z ↦
        survivesTwoCertificates q (D₁ z) (D₂ z) ∧
        coordinate z ∉ finiteAffineCommonZeroLocus (family z q)).card) = 0 := by
    apply Finset.sum_eq_zero
    intro q _hq
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨hzX, hzSurvives, hzOff⟩ := Finset.mem_filter.mp hz
    have hzCell : z ∈ rankSevenChartReservoirCell
        p x₀ equations CF C denominator q.1 := by
      exact Finset.mem_filter.mpr ⟨hzX, hzSurvives⟩
    apply hzOff
    exact integralAffineChartVector_mem_rankSevenStaticSourceSectionEquations
      p x₀ equations CF hhomogeneous C denominator P k hP hlower q z hzCell
  rw [hoff, zero_add] at hpartition
  simpa only [X, D₁, D₂, family, coordinate,
    rankSevenStaticSelectedComponent,
    occurringRankSevenStaticComponents] using hpartition

end

end TranslatedDepthSeven
