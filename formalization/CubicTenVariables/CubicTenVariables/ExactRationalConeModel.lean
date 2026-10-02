import CubicTenVariables.RationalConeIntegralModel
import CubicTenVariables.FixedEquationDimensionAll

/-!
# Empty-preserving rational cone models

Here rational closure means precisely the geometric closure of the actual
rational points; the origin is not adjoined. A nonempty cone contains zero
and uses the existing rational cone model. The empty cone uses the single
homogeneous equation 1=0. The same fixed integer equations retain exact
rational and geometric ideals and point sets, and their dimension bounds
specialize uniformly outside one finite set of characteristics.
-/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ExactRationalConeModel

open MvPolynomial HessianTheorem11 RationalConeClosure

/-- Literal rational-point closure, preserving the empty set. -/
def rationalClosure {n : ℕ} (C : Set (GeometricPoint n)) : Set (GeometricPoint n) :=
  geometricClosure (rationalEmbedding '' rationalPoints C)

@[simp] theorem rationalClosure_empty (n : ℕ) :
    rationalClosure (∅ : Set (GeometricPoint n)) = ∅ := by
  simp [rationalClosure,rationalPoints,geometricClosure,vanishingIdeal_empty,zeroLocus_top]

/-- For a set already containing zero, adjoining the origin is redundant. -/
theorem rationalClosure_eq_adjoined {n : ℕ} (C : Set (GeometricPoint n))
    (hzero : (0 : GeometricPoint n) ∈ C) :
    rationalClosure C = rationalConeClosure C := by
  have hz : (0 : GeometricPoint n) ∈ rationalClosure C :=
    subset_geometricClosure _ ⟨0,by simpa only [rationalPoints,Set.mem_setOf_eq,
      rationalEmbedding_zero] using hzero,rationalEmbedding_zero⟩
  symm
  exact Set.union_eq_left.mpr (Set.singleton_subset_iff.mpr hz)

/-- A finite homogeneous integral model of the exact rational closure,
including the empty cone. Neither rational points nor zero are added. -/
theorem exists_homogeneous_model {n : ℕ}
    (C : Set (GeometricPoint n)) (hcone : IsAffineCone C)
    (hclosed : AlgebraicallyClosedSet C) :
    ∃ (m : ℕ) (G : Fin m → MvPolynomial (Fin n) ℤ) (d : Fin m → ℕ),
      (∀ i, (G i).IsHomogeneous (d i)) ∧
      IntegralModelDimension.rationalIdeal G = vanishingIdeal ℚ (rationalPoints C) ∧
      IntegralModelDimension.geometricIdeal G =
        vanishingIdeal GeometricField (rationalClosure C) ∧
      (∀ x : GeometricPoint n, x ∈ rationalClosure C ↔
        ∀ i, eval₂ (Int.castRingHom GeometricField) x (G i) = 0) ∧
      ∀ q : Fin n → ℚ, (∀ i, eval₂ (Int.castRingHom ℚ) q (G i) = 0) ↔
        rationalEmbedding q ∈ C := by
  by_cases hne : C.Nonempty
  · have hzero : (0 : GeometricPoint n) ∈ C := by
      obtain ⟨x,hx⟩ := hne
      simpa only [zero_smul] using hcone 0 x hx
    obtain ⟨m,G,d,hd,hQ,hG,hmodel,hpoints⟩ :=
      RationalConeIntegralModel.exists_homogeneous_model_exact_rational_points
        C hcone hclosed hzero
    have he := rationalClosure_eq_adjoined C hzero
    refine ⟨m,G,d,hd,?_,?_,?_,hpoints⟩
    · rw [hQ,RationalConeIntegralModel.rationalIdeal,
        RationalConeIntegralModel.rationalPoints_eq C hclosed hzero]
    · rw [he]
      exact hG
    · rw [he]
      exact hmodel
  · have hC : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst C
    refine ⟨1,fun _ => 1,fun _ => 0,fun _ => isHomogeneous_one _ _,?_,?_,?_,?_⟩
    · simp [IntegralModelDimension.rationalIdeal,rationalPoints,vanishingIdeal_empty]
    · simp [IntegralModelDimension.geometricIdeal,vanishingIdeal_empty]
    · intro x
      simp
    · intro q
      simp

/-- Exact geometric-ideal identification gives the same quotient dimension
also for the unit ideal. This includes empty geometric zero sets. -/
theorem rational_quotient_dimension_eq {n m : ℕ}
    (G : Fin m → MvPolynomial (Fin n) ℤ) (Z : Set (GeometricPoint n))
    (hmodel : IntegralModelDimension.geometricIdeal G = vanishingIdeal GeometricField Z) :
    ringKrullDim (MvPolynomial (Fin n) ℚ ⧸ IntegralModelDimension.rationalIdeal G) =
      affineDimension Z := by
  by_cases ht : IntegralModelDimension.rationalIdeal G = ⊤
  · rw [ht,ringKrullDim_eq_bot_of_subsingleton]
    rw [affineDimension,← hmodel,← IntegralModelDimension.map_rationalIdeal,ht,
      Ideal.map_top,ringKrullDim_eq_bot_of_subsingleton]
  · have h := RationalEquationDimension.qbar_quotient_dimension
      (IntegralModelDimension.rationalIdeal G) ht
    rw [IntegralModelDimension.map_rationalIdeal,hmodel] at h
    exact h.symm

/-- The equation list is fixed before the exceptional integer and every
prime/field. Both the original equation quotient and its actual reduced
zero-set coordinate ring satisfy the supplied characteristic-zero dimension
bound, without a nonempty-cone or zero-membership premise. -/
theorem exists_model_good_characteristic_dimension_bound {n r : ℕ}
    (C : Set (GeometricPoint n)) (hcone : IsAffineCone C)
    (hclosed : AlgebraicallyClosedSet C)
    (hdim : affineDimension (rationalClosure C) ≤ (r : Dimension)) :
    ∃ (m : ℕ) (G : Fin m → MvPolynomial (Fin n) ℤ) (d : Fin m → ℕ),
      (∀ i, (G i).IsHomogeneous (d i)) ∧
      IntegralModelDimension.rationalIdeal G = vanishingIdeal ℚ (rationalPoints C) ∧
      IntegralModelDimension.geometricIdeal G =
        vanishingIdeal GeometricField (rationalClosure C) ∧
      (∀ x : GeometricPoint n, x ∈ rationalClosure C ↔
        ∀ i, eval₂ (Int.castRingHom GeometricField) x (G i) = 0) ∧
      (∀ q : Fin n → ℚ, (∀ i, eval₂ (Int.castRingHom ℚ) q (G i) = 0) ↔
        rationalEmbedding q ∈ C) ∧
      ∃ D : ℕ, 1 ≤ D ∧ ∀ p : ℕ, p.Prime → ¬ p ∣ D →
        ∀ (K : Type) [Field K] [CharP K p],
          ringKrullDim (MvPolynomial (Fin n) K ⧸
            FixedEquationNormalization.equationIdeal G K) ≤ (r : Dimension) ∧
          ringKrullDim (MvPolynomial (Fin n) K ⧸ vanishingIdeal K
            (FixedEquationDimensionReduction.zeroSet G K)) ≤ (r : Dimension) := by
  obtain ⟨m,G,d,hd,hQ,hG,hmodel,hpoints⟩ := exists_homogeneous_model C hcone hclosed
  refine ⟨m,G,d,hd,hQ,hG,hmodel,hpoints,?_⟩
  apply FixedEquationDimensionAll.exists_good_characteristic_dimension_bound G
  change ringKrullDim (MvPolynomial (Fin n) ℚ ⧸ IntegralModelDimension.rationalIdeal G) ≤ _
  rw [rational_quotient_dimension_eq G (rationalClosure C) hG]
  exact hdim

end CubicTenVariables.ExactRationalConeModel
