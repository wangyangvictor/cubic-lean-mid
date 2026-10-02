import CubicTenVariables.CubicConePointCountBound

/-! The part of the cubic point-count estimate already supplied by the
explicit Hooley--Katz premise. The singular-cone dimension hypothesis is
retained: this does not settle the large-singular-locus cases of Browning's
nonconical cubic theorem. In the required nine-variable hyperplane
application the cutoff is affine singular dimension five. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CubicSmallSingularPointCount
open MvPolynomial Literature
open scoped BigOperators

/-- Hooley--Katz gives the cubic exponent when the actual geometric singular
cone has codimension at least four in affine space. The constant precedes
every finite field and every polynomial; no nonconicality assumption is needed. -/
theorem exists_bound (hk : HooleyKatzPointCount) (n : ℕ) (hn : 5 ≤ n) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (K : Type) [Field K] [Fintype K]
      (F : MvPolynomial (Fin n) K), F.IsHomogeneous 3 →
      GeometricallyIntegralForm F →
      ReducedGaussSection.coordinateDimension (geometricSingularCone F) ≤
        ((n-4 : ℕ) : WithBot ℕ∞) →
      |(affineZeroCount F : ℝ)-(Fintype.card K : ℝ)^(n-1)| ≤
        C*((Fintype.card K : ℝ)-1)*(Fintype.card K : ℝ)^((n : ℝ)-3) := by
  obtain ⟨C,hC,hcount⟩ := hk n 3 (n-5) (by decide) (by omega)
  refine ⟨C,hC,?_⟩
  intro K _ _ F hF hI hS
  have hdim : n-5+1=n-4 := by omega
  have h := hcount K F hF hI (by simpa only [hdim] using hS)
  have hcast : ((n-5 : ℕ) : ℝ)=(n : ℝ)-5 := by
    rw [Nat.cast_sub hn]
    norm_num
  have he : ((n : ℝ)-1+((n-5 : ℕ) : ℝ))/2=(n : ℝ)-3 := by
    rw [hcast]
    ring
  simpa only [he] using h

/-- The literal nine-variable estimate needed for a hyperplane section,
provided its geometric affine singular cone has dimension at most five. -/
theorem exists_nine_variable_bound (hk : HooleyKatzPointCount) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (K : Type) [Field K] [Fintype K]
      (F : MvPolynomial (Fin 9) K), F.IsHomogeneous 3 →
      GeometricallyIntegralForm F →
      ReducedGaussSection.coordinateDimension (geometricSingularCone F) ≤
        (5 : WithBot ℕ∞) →
      |(affineZeroCount F : ℝ)-(Fintype.card K : ℝ)^8| ≤
        C*((Fintype.card K : ℝ)-1)*(Fintype.card K : ℝ)^6 := by
  have h := exists_bound hk 9 (by decide)
  norm_num at h
  exact h

end CubicTenVariables.CubicSmallSingularPointCount
