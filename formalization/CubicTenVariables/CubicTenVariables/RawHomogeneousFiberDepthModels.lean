import CubicTenVariables.HomogeneousDepthEquations
import CubicTenVariables.IntegralGeometricFiberDepth

/-! One finite integral equation list for the exact positive geometric depth
locus of a homogeneous family, uniformly in every characteristic. These raw
equations are not asserted to generate a reduced or homogeneous parameter
ideal; those are separate characteristic-zero model operations. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.RawHomogeneousFiberDepthModels
open MvPolynomial HessianTheorem11 IntegralGeometricFiberDepth

private theorem threshold {j : ℕ} (hj : 0 < j) (D : WithBot ℕ∞) :
    ((j-1 : ℕ) : WithBot ℕ∞) < D ↔ (j : WithBot ℕ∞) ≤ D := by
  rw [← WithBot.add_one_le_iff]
  norm_cast
  rw [Nat.sub_add_cancel hj]

/-- A fixed finite integer equation list has the same zero condition before
and after extending a field to its algebraic closure. -/
theorem zeros_algebraicClosure_iff {m u : ℕ}
    (G : Fin u → MvPolynomial (Fin m) ℤ)
    (K : Type*) [Field K] (v : Fin m → K) :
    (∀ i, eval₂ (Int.castRingHom K) v (G i) = 0) ↔
      ∀ i, eval₂ (Int.castRingHom (AlgebraicClosure K))
        (fun j => algebraMap K (AlgebraicClosure K) (v j)) (G i) = 0 := by
  let a := algebraMap K (AlgebraicClosure K)
  have hc : a.comp (Int.castRingHom K) = Int.castRingHom (AlgebraicClosure K) :=
    RingHom.ext_int _ _
  have he (i : Fin u) :
      eval₂ (Int.castRingHom (AlgebraicClosure K)) (fun j => a (v j)) (G i) =
        a (eval₂ (Int.castRingHom K) v (G i)) := by
    simpa only [hc] using (map_eval₂Hom (Int.castRingHom K) v a (G i)).symm
  apply forall_congr'
  intro i
  rw [he]
  exact (map_eq_zero a).symm

/-- Exact raw equations for the actual fibers. Homogeneity is required only
in the fiber variables; parameter homogeneity is not needed at this stage. -/
theorem exists_equations {m n t j : ℕ} (hj : 0 < j)
    (f : Fin t → MvPolynomial (Fin n) (MvPolynomial (Fin m) ℤ))
    (dx : Fin t → ℕ) (hf : ∀ i, (f i).IsHomogeneous (dx i)) :
    ∃ u : ℕ, ∃ G : Fin u → MvPolynomial (Fin m) ℤ,
      (∀ v : GeometricPoint m,
        (∀ i, eval₂ (Int.castRingHom GeometricField) v (G i) = 0) ↔
          (j : Dimension) ≤ ReducedGaussSection.coordinateDimension (fiber f GeometricField v)) ∧
      ∀ (K : Type) [Field K] (v : Fin m → K),
        (∀ i, eval₂ (Int.castRingHom K) v (G i) = 0) ↔
          (j : WithBot ℕ∞) ≤ geometricFiberDimension f K v := by
  obtain ⟨u,G,_,hG⟩ := HomogeneousDepthEquations.exists_equations f dx hf (j-1)
  have hfield (K : Type) [Field K] [Infinite K] (v : Fin m → K) :
      (∀ i, eval₂ (Int.castRingHom K) v (G i) = 0) ↔
        (j : WithBot ℕ∞) ≤ ringKrullDim
          (MvPolynomial (Fin n) K ⧸ Literature.integralFamilyFiberIdeal f K v) := by
    exact (hG K (eval₂Hom (Int.castRingHom K) v)).trans (threshold hj _)
  refine ⟨u,G,?_,?_⟩
  · intro v
    rw [coordinateDimension_fiber_eq]
    exact hfield GeometricField v
  · intro K _ v
    rw [zeros_algebraicClosure_iff G K v]
    exact hfield (AlgebraicClosure K) _

end CubicTenVariables.RawHomogeneousFiberDepthModels
