import CubicTenVariables.RationalClosureIdempotent
import CubicTenVariables.GaloisClosedSetModel
import CubicTenVariables.IntegralConeNormalization
import TranslatedDepthSeven.IntegralHomogeneousIdealModel

/-!
# Homogeneous integral equations for the actual rational cone closure

The rational ideal is the vanishing ideal of the actual rational points of
`rationalConeClosure C`. Rational density and the existing Galois descent
prove that its extension to Qbar equals the actual geometric vanishing
ideal. Existing finite homogeneous generators and denominator clearing then
supply one finite integral equation family for this same cone. For a closed
original set containing zero, its rational points are exactly the rational
solutions of these equations. No characteristic-p identification or
singular-support existence result is asserted.
-/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.RationalConeIntegralModel

open MvPolynomial HessianTheorem11
open RationalConeClosure RationalClosureIdempotent RationalComponentDescent
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The source-defined rational vanishing ideal, not an arbitrary ideal
chosen to have the desired dimension. -/
def rationalIdeal {n : ℕ} (C : Set (GeometricPoint n)) :
    Ideal (MvPolynomial (Fin n) ℚ) :=
  vanishingIdeal ℚ (rationalPoints (rationalConeClosure C))

theorem mem_rationalIdeal_iff {n : ℕ} (C : Set (GeometricPoint n))
    (f : MvPolynomial (Fin n) ℚ) :
    f ∈ rationalIdeal C ↔ map (algebraMap ℚ GeometricField) f ∈
      vanishingIdeal GeometricField (rationalConeClosure C) := by
  rw [← rationalPoints_dense_any C, vanishingIdeal_geometricClosure]
  constructor
  · intro hf x hx
    obtain ⟨q,hq,rfl⟩ := hx
    change eval (rationalEmbedding q) (map (algebraMap ℚ GeometricField) f) = 0
    have he := map_eval (algebraMap ℚ GeometricField) q f
    rw [show eval q f = 0 from hf q hq, map_zero] at he
    simpa only [rationalEmbedding, Function.comp_def] using he.symm
  · intro hf q hq
    have hz := hf _ ⟨q,hq,rfl⟩
    change eval (rationalEmbedding q) (map (algebraMap ℚ GeometricField) f) = 0 at hz
    apply (algebraMap ℚ GeometricField).injective
    change algebraMap ℚ GeometricField (eval q f) = algebraMap ℚ GeometricField 0
    rw [map_zero]
    exact (map_eval (algebraMap ℚ GeometricField) q f).trans hz

/-- The ideal extension is exact, not merely equal after taking radicals. -/
theorem map_rationalIdeal {n : ℕ} (C : Set (GeometricPoint n)) :
    (rationalIdeal C).map (map (algebraMap ℚ GeometricField)) =
      vanishingIdeal GeometricField (rationalConeClosure C) := by
  apply le_antisymm
  · exact Ideal.map_le_iff_le_comap.mpr (fun f hf => (mem_rationalIdeal_iff C f).mp hf)
  · obtain ⟨m,f,hf⟩ := GaloisClosedSetModel.exists_rational_generators
      (vanishingIdeal GeometricField (rationalConeClosure C))
      (GaloisClosedSetModel.coefficientMap_mem _
        (galoisPoint_mem_of_rational_dense _ (rationalPoints_dense_any C)))
    rw [← hf]
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    apply Ideal.mem_map_of_mem
    apply (mem_rationalIdeal_iff C (f i)).mpr
    rw [← hf]
    exact Ideal.subset_span ⟨i,rfl⟩

theorem rationalIdeal_isHomogeneous {n : ℕ} (C : Set (GeometricPoint n))
    (hC : IsAffineCone C) :
    (rationalIdeal C).IsHomogeneous (homogeneousSubmodule (Fin n) ℚ) := by
  apply DavenportHomogeneity.vanishingIdeal_isHomogeneous_of_nonzero_smul
  intro a _ q hq
  change rationalEmbedding (a • q) ∈ rationalConeClosure C
  rw [rationalEmbedding_smul]
  exact rationalConeClosure_isAffineCone C hC _ _ hq

/-- The adjoined origin changes no rational points when the original closed
set already contains it. -/
theorem rationalPoints_eq {n : ℕ} (C : Set (GeometricPoint n))
    (hC : AlgebraicallyClosedSet C) (hzero : (0 : GeometricPoint n) ∈ C) :
    rationalPoints (rationalConeClosure C) = rationalPoints C := by
  rw [rationalPoints_rationalConeClosure C hC]
  apply Set.union_eq_left.mpr
  apply Set.singleton_subset_iff.mpr
  simpa only [rationalPoints, Set.mem_setOf_eq, rationalEmbedding_zero] using hzero

/-- One finite family of integral homogeneous equations generates the
source-defined rational ideal and the actual reduced geometric ideal. -/
theorem exists_homogeneous_model {n : ℕ} (C : Set (GeometricPoint n))
    (hC : IsAffineCone C) :
    ∃ (m : ℕ) (G : Fin m → MvPolynomial (Fin n) ℤ) (d : Fin m → ℕ),
      (∀ i, (G i).IsHomogeneous (d i)) ∧
      IntegralModelDimension.rationalIdeal G = rationalIdeal C ∧
      IntegralModelDimension.geometricIdeal G =
        vanishingIdeal GeometricField (rationalConeClosure C) ∧
      ∀ x : GeometricPoint n, x ∈ rationalConeClosure C ↔
        ∀ i, eval₂ (Int.castRingHom GeometricField) x (G i) = 0 := by
  classical
  obtain ⟨E,hE,heq⟩ := TranslatedDepthSeven.exists_integral_homogeneous_equations_map_ideal_eq
    (rationalIdeal C) (rationalIdeal_isHomogeneous C hC)
  let e : Fin (Fintype.card E) ≃ E := (Fintype.equivFin E).symm
  let G : Fin (Fintype.card E) → MvPolynomial (Fin n) ℤ := fun i => (e i).val
  have hrange : Set.range G = (E : Set (MvPolynomial (Fin n) ℤ)) := by
    ext f
    constructor
    · rintro ⟨i,rfl⟩
      exact (e i).property
    · intro hf
      exact ⟨e.symm ⟨f,hf⟩,by simp [G]⟩
  have hdegree : ∀ i, ∃ d : ℕ, (G i).IsHomogeneous d :=
    fun i => hE (G i) (e i).property
  choose d hd using hdegree
  have hQ : IntegralModelDimension.rationalIdeal G = rationalIdeal C := by
    rw [Ideal.map_span, ← hrange, ← Set.range_comp] at heq
    exact heq
  have hG : IntegralModelDimension.geometricIdeal G =
      vanishingIdeal GeometricField (rationalConeClosure C) := by
    rw [← IntegralModelDimension.map_rationalIdeal, hQ, map_rationalIdeal]
  refine ⟨Fintype.card E,G,d,hd,hQ,hG,?_⟩
  intro x
  rw [← rationalConeClosure_closed C]
  change x ∈ zeroLocus GeometricField (vanishingIdeal GeometricField (rationalConeClosure C)) ↔ _
  rw [← hG, IntegralModelDimension.geometricIdeal, zeroLocus_span]
  change (∀ g ∈ Set.range (fun i => map (Int.castRingHom GeometricField) (G i)),
    eval x g = 0) ↔ _
  simp only [Set.forall_mem_range, eval_map]

/-- The same integral equations have exactly the original rational points.
Their characteristic-zero zero set remains the actual rational closure. -/
theorem exists_homogeneous_model_exact_rational_points {n : ℕ}
    (C : Set (GeometricPoint n)) (hC : IsAffineCone C)
    (hclosed : AlgebraicallyClosedSet C) (hzero : (0 : GeometricPoint n) ∈ C) :
    ∃ (m : ℕ) (G : Fin m → MvPolynomial (Fin n) ℤ) (d : Fin m → ℕ),
      (∀ i, (G i).IsHomogeneous (d i)) ∧
      IntegralModelDimension.rationalIdeal G = rationalIdeal C ∧
      IntegralModelDimension.geometricIdeal G =
        vanishingIdeal GeometricField (rationalConeClosure C) ∧
      (∀ x : GeometricPoint n, x ∈ rationalConeClosure C ↔
        ∀ i, eval₂ (Int.castRingHom GeometricField) x (G i) = 0) ∧
      ∀ q : Fin n → ℚ, (∀ i, eval₂ (Int.castRingHom ℚ) q (G i) = 0) ↔
        rationalEmbedding q ∈ C := by
  obtain ⟨m,G,d,hd,hQ,hG,hmodel⟩ := exists_homogeneous_model C hC
  refine ⟨m,G,d,hd,hQ,hG,hmodel,?_⟩
  intro q
  have hc : (algebraMap ℚ GeometricField).comp (Int.castRingHom ℚ) =
      Int.castRingHom GeometricField := by ext a; simp
  have he (i : Fin m) : eval₂ (Int.castRingHom GeometricField) (rationalEmbedding q) (G i) =
      algebraMap ℚ GeometricField (eval₂ (Int.castRingHom ℚ) q (G i)) := by
    simpa only [hc,Function.comp_def,rationalEmbedding] using
      (eval₂_comp_left (algebraMap ℚ GeometricField) (Int.castRingHom ℚ) q (G i)).symm
  have hzeros : (∀ i, eval₂ (Int.castRingHom ℚ) q (G i) = 0) ↔
      ∀ i, eval₂ (Int.castRingHom GeometricField) (rationalEmbedding q) (G i) = 0 := by
    apply forall_congr'
    intro i
    rw [he]
    exact (map_eq_zero (algebraMap ℚ GeometricField)).symm
  rw [hzeros, ← hmodel, rationalEmbedding_mem_iff C hclosed]
  constructor
  · rintro (hq | rfl)
    · exact hq
    · simpa only [rationalEmbedding_zero] using hzero
  · exact Or.inl

end CubicTenVariables.RationalConeIntegralModel
