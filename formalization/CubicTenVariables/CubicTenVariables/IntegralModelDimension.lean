import CubicTenVariables.RationalEquationDimension
import CubicTenVariables.FixedEquationPrimeCount

/-! Dimension and prime counts for a fixed integral model whose geometric
ideal is identified with the actual vanishing ideal of a nonempty set. -/

noncomputable section
namespace CubicTenVariables.IntegralModelDimension
open MvPolynomial HessianTheorem11

variable {σ : Type*} {t : ℕ}

/-- The actual integral equations extended to the rationals. -/
def rationalIdeal (G : Fin t → MvPolynomial σ ℤ) : Ideal (MvPolynomial σ ℚ) :=
  Ideal.span (Set.range (fun i => map (Int.castRingHom ℚ) (G i)))

/-- The same equations extended directly to the geometric field. -/
def geometricIdeal (G : Fin t → MvPolynomial σ ℤ) : Ideal (MvPolynomial σ GeometricField) :=
  Ideal.span (Set.range (fun i => map (Int.castRingHom GeometricField) (G i)))

/-- Passing through the rational coefficient field gives exactly the
direct geometric equation ideal. -/
theorem map_rationalIdeal (G : Fin t → MvPolynomial σ ℤ) :
    (rationalIdeal G).map (map (algebraMap ℚ GeometricField)) = geometricIdeal G := by
  have hcomp : (algebraMap ℚ GeometricField).comp (Int.castRingHom ℚ) =
      Int.castRingHom GeometricField := by
    ext a
    simp
  rw [rationalIdeal, geometricIdeal, Ideal.map_span, ← Set.range_comp]
  simp only [Function.comp_def, map_map, hcomp]

/-- Nonemptiness of the identified geometric set proves properness of
the original rational equation ideal. No rational point is required. -/
theorem rationalIdeal_ne_top (G : Fin t → MvPolynomial σ ℤ)
    (Z : Set (σ → GeometricField)) (hZ : Z.Nonempty)
    (hmodel : geometricIdeal G = vanishingIdeal GeometricField Z) :
    rationalIdeal G ≠ ⊤ := by
  intro htop
  have he : (⊤ : Ideal (MvPolynomial σ GeometricField)) = vanishingIdeal GeometricField Z := by
    rw [← hmodel, ← map_rationalIdeal, htop, Ideal.map_top]
  obtain ⟨x,hx⟩ := hZ
  have h1 : (1 : MvPolynomial σ GeometricField) ∈ vanishingIdeal GeometricField Z := by
    rw [← he]
    trivial
  have hz := h1 x hx
  simp at hz

/-- Exact geometric ideal identification transfers Krull dimension to
the rational equation quotient, even without a primeness assumption. -/
theorem rational_quotient_dimension_eq (G : Fin t → MvPolynomial σ ℤ)
    (Z : Set (σ → GeometricField)) (hZ : Z.Nonempty)
    (hmodel : geometricIdeal G = vanishingIdeal GeometricField Z) :
    ringKrullDim (MvPolynomial σ ℚ ⧸ rationalIdeal G) = affineDimension Z := by
  have h := RationalEquationDimension.qbar_quotient_dimension (rationalIdeal G)
    (rationalIdeal_ne_top G Z hZ hmodel)
  rw [map_rationalIdeal, hmodel] at h
  exact h.symm

/-- A fixed identified integral model has a uniform all-prime bound for
all modular solutions of its actual equations. This does not identify its
special fibers with any separately defined geometric parameter locus. -/
theorem exists_uniform_bound [Fintype σ] (G : Fin t → MvPolynomial σ ℤ)
    (Z : Set (σ → GeometricField)) (hZ : Z.Nonempty)
    (hmodel : geometricIdeal G = vanishingIdeal GeometricField Z)
    (r : ℕ) (hdim : affineDimension Z ≤ (r : Dimension)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ p : ℕ, p.Prime →
      Nat.card {x : σ → ZMod p //
        ∀ i, eval₂ (Int.castRingHom (ZMod p)) x (G i) = 0} ≤ C*p^r := by
  apply FixedEquationPrimeCount.exists_uniform_bound G (rationalIdeal_ne_top G Z hZ hmodel)
  change ringKrullDim (MvPolynomial σ ℚ ⧸ rationalIdeal G) ≤ _
  rw [rational_quotient_dimension_eq G Z hZ hmodel]
  exact hdim

end CubicTenVariables.IntegralModelDimension
