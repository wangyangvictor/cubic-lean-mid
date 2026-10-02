import CubicTenVariables.Literature.FiberDimensionSpreading
import CubicTenVariables.FixedEquationDimensionReduction
import CubicTenVariables.ReducedGaussSection
import HessianTheorem11.UnconditionalCutDimension

/-! Literal geometric fiber depth for nested integral polynomial equations.
The coefficient variables are parameters and the outer variables are fiber
coordinates. Dimensions are those of the actual equation quotient over an
algebraic closure, and agree with the reduced coordinate-ring dimensions of
the actual geometric fibers. Empty fibers retain dimension bottom.

The final containment adapter uses only the existing, explicit generic
fiber-dimension spreading input. No trace statement or point-count estimate
is part of the definitions or their unconditional properties. -/

noncomputable section
namespace CubicTenVariables.IntegralGeometricFiberDepth
open MvPolynomial Literature HessianTheorem11

variable {m n : ℕ} {ι : Type*}

/-- The actual common zeros of the specialized nested equations. -/
def fiber (f : ι → MvPolynomial (Fin n) (MvPolynomial (Fin m) ℤ))
    (K : Type*) [Field K] (v : Fin m → K) : Set (Fin n → K) :=
  {x | ∀ i, eval x (map (eval₂Hom (Int.castRingHom K) v) (f i)) = 0}

theorem fiber_eq_zeroLocus
    (f : ι → MvPolynomial (Fin n) (MvPolynomial (Fin m) ℤ))
    (K : Type*) [Field K] (v : Fin m → K) :
    fiber f K v = zeroLocus K (integralFamilyFiberIdeal f K v) := by
  rw [integralFamilyFiberIdeal, zeroLocus_span]
  ext x
  simp [fiber, aeval_def]

/-- Nullstellensatz and invariance under radical identify the literal fiber
with its equation quotient, including the empty-fiber case. -/
theorem coordinateDimension_fiber_eq
    (f : ι → MvPolynomial (Fin n) (MvPolynomial (Fin m) ℤ))
    (K : Type*) [Field K] [IsAlgClosed K] (v : Fin m → K) :
    ReducedGaussSection.coordinateDimension (fiber f K v) =
      ringKrullDim (MvPolynomial (Fin n) K ⧸ integralFamilyFiberIdeal f K v) := by
  rw [fiber_eq_zeroLocus, ReducedGaussSection.coordinateDimension,
    vanishingIdeal_zeroLocus_eq_radical,
    UnconditionalCutDimension.quotient_radical_dimension]

/-- The fiber over a geometric point above the given field-valued parameter. -/
def geometricFiber
    (f : ι → MvPolynomial (Fin n) (MvPolynomial (Fin m) ℤ))
    (K : Type*) [Field K] (v : Fin m → K) :
    Set (Fin n → AlgebraicClosure K) :=
  fiber f (AlgebraicClosure K) (fun i => algebraMap K (AlgebraicClosure K) (v i))

/-- The geometric dimension of the literal specialized equation quotient. -/
def geometricFiberDimension
    (f : ι → MvPolynomial (Fin n) (MvPolynomial (Fin m) ℤ))
    (K : Type*) [Field K] (v : Fin m → K) : WithBot ℕ∞ :=
  ringKrullDim (MvPolynomial (Fin n) (AlgebraicClosure K) ⧸
    integralFamilyFiberIdeal f (AlgebraicClosure K)
      (fun i => algebraMap K (AlgebraicClosure K) (v i)))

theorem geometricFiberDimension_eq_coordinateDimension
    (f : ι → MvPolynomial (Fin n) (MvPolynomial (Fin m) ℤ))
    (K : Type*) [Field K] (v : Fin m → K) :
    geometricFiberDimension f K v =
      ReducedGaussSection.coordinateDimension (geometricFiber f K v) :=
  (coordinateDimension_fiber_eq f (AlgebraicClosure K) _).symm

/-- Every geometric fiber has finite dimension at most the number of fiber
variables. No nonemptiness is assumed or asserted. -/
theorem geometricFiberDimension_le
    (f : ι → MvPolynomial (Fin n) (MvPolynomial (Fin m) ℤ))
    (K : Type*) [Field K] (v : Fin m → K) :
    geometricFiberDimension f K v ≤ (n : WithBot ℕ∞) := by
  exact (ringKrullDim_le_of_surjective (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective).trans
      (le_of_eq (FixedEquationDimensionReduction.polynomial_dimension
        (AlgebraicClosure K) n))

/-- The geometric depth locus at a nonnegative affine-dimension threshold. -/
def depthLocus
    (f : ι → MvPolynomial (Fin n) (MvPolynomial (Fin m) ℤ))
    (K : Type*) [Field K] (j : ℕ) : Set (Fin m → K) :=
  {v | (j : WithBot ℕ∞) ≤ geometricFiberDimension f K v}

theorem mem_depthLocus_iff_coordinateDimension
    (f : ι → MvPolynomial (Fin n) (MvPolynomial (Fin m) ℤ))
    (K : Type*) [Field K] (j : ℕ) (v : Fin m → K) :
    v ∈ depthLocus f K j ↔ (j : WithBot ℕ∞) ≤
      ReducedGaussSection.coordinateDimension (geometricFiber f K v) := by
  simp only [depthLocus, Set.mem_setOf_eq,
    geometricFiberDimension_eq_coordinateDimension]

theorem depthLocus_antitone
    (f : ι → MvPolynomial (Fin n) (MvPolynomial (Fin m) ℤ))
    (K : Type*) [Field K] {j k : ℕ} (hjk : j ≤ k) :
    depthLocus f K k ⊆ depthLocus f K j := by
  intro v hv
  exact (show (j : WithBot ℕ∞) ≤ (k : WithBot ℕ∞) by exact_mod_cast hjk).trans hv

/-- The existing generic spreading theorem applies to these literal
geometric depth loci, uniformly in every field of every good characteristic.
The characteristic-zero premise concerns all geometric parameters. -/
theorem exists_depthLocus_containment
    (spread : FiberDimensionContainmentSpreading)
    (m n j : ℕ) (ι κ : Type) [Fintype ι] [Fintype κ]
    (f : ι → MvPolynomial (Fin n) (MvPolynomial (Fin m) ℤ))
    (G : κ → MvPolynomial (Fin m) ℤ)
    (hgeneric : ∀ v : GeometricPoint m,
      (j : Dimension) ≤ ReducedGaussSection.coordinateDimension
        (fiber f GeometricField v) →
      ∀ i, eval₂ (Int.castRingHom GeometricField) v (G i) = 0) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ p : ℕ, p.Prime → ¬ p ∣ D →
      ∀ (K : Type) [Field K] [CharP K p],
        depthLocus f K j ⊆ {v | ∀ i, eval₂ (Int.castRingHom K) v (G i) = 0} := by
  obtain ⟨D,hD,hgood⟩ := spread m n j ι κ f G (by
    intro v hv
    apply hgeneric v
    rwa [coordinateDimension_fiber_eq])
  refine ⟨D,hD,?_⟩
  intro p hp hpD K _ _ v hv i
  let a := algebraMap K (AlgebraicClosure K)
  have hc : a.comp (Int.castRingHom K) = Int.castRingHom (AlgebraicClosure K) :=
    RingHom.ext_int _ _
  have he : eval₂ (Int.castRingHom (AlgebraicClosure K)) (fun i => a (v i)) (G i) =
      a (eval₂ (Int.castRingHom K) v (G i)) := by
    simpa only [hc] using (map_eval₂Hom (Int.castRingHom K) v a (G i)).symm
  have hz := hgood p hp hpD (AlgebraicClosure K) (fun i => a (v i)) hv i
  rw [he] at hz
  exact a.injective (by simpa only [map_zero] using hz)

end CubicTenVariables.IntegralGeometricFiberDepth
