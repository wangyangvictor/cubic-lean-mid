import CubicTenVariables.GaloisClosedSetModel
import CubicTenVariables.DavenportHomogeneity
import TranslatedDepthSeven.IntegralHomogeneousIdealModel

/-! Finite integral homogeneous equations for an actual Galois-stable closed
cone over Qbar. The rational ideal is the contraction of its actual geometric
vanishing ideal, so no rational-point density or rational closure is used.
The extended integral equation ideal is exactly the reduced geometric ideal.
No assertion about positive-characteristic fibers is made in this module. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.GaloisClosedConeIntegralModel
open MvPolynomial HessianTheorem11 RationalComponentDescent
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Coefficient maps commute with the literal homogeneous components. -/
theorem map_homogeneousComponent {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (ρ : R →+* S) (d : ℕ) (f : MvPolynomial σ R) :
    map ρ (homogeneousComponent d f) = homogeneousComponent d (map ρ f) := by
  classical
  ext u
  by_cases hu : u.degree = d
  · simp only [coeff_map, coeff_homogeneousComponent, if_pos hu]
  · simp only [coeff_map, coeff_homogeneousComponent, if_neg hu, map_zero]

/-- Contraction of the actual Qbar vanishing ideal. -/
def rationalIdeal {n : ℕ} (Z : Set (GeometricPoint n)) : Ideal (MvPolynomial (Fin n) ℚ) :=
  (vanishingIdeal GeometricField Z).comap (map (algebraMap ℚ GeometricField))

/-- Galois descent identifies the extension of that contraction exactly.
It does not replace the geometric set by the closure of rational points. -/
theorem map_rationalIdeal {n : ℕ} (Z : Set (GeometricPoint n))
    (hstable : ∀ (σ : GeometricField ≃ₐ[ℚ] GeometricField),
      ∀ x ∈ Z, galoisPoint σ x ∈ Z) :
    (rationalIdeal Z).map (map (algebraMap ℚ GeometricField)) =
      vanishingIdeal GeometricField Z := by
  apply le_antisymm
  · exact Ideal.map_le_iff_le_comap.mpr le_rfl
  · obtain ⟨r, f, hf⟩ := GaloisClosedSetModel.exists_rational_generators
      (vanishingIdeal GeometricField Z)
      (GaloisClosedSetModel.coefficientMap_mem Z hstable)
    rw [← hf]
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply Ideal.mem_map_of_mem
    change map (algebraMap ℚ GeometricField) (f i) ∈ vanishingIdeal GeometricField Z
    rw [← hf]
    exact Ideal.subset_span ⟨i, rfl⟩

/-- Conicality of the actual geometric set makes its contracted rational
vanishing ideal homogeneous, including empty cones. -/
theorem rationalIdeal_isHomogeneous {n : ℕ} (Z : Set (GeometricPoint n))
    (hcone : IsAffineCone Z) :
    (rationalIdeal Z).IsHomogeneous (homogeneousSubmodule (Fin n) ℚ) := by
  have hI := DavenportHomogeneity.vanishingIdeal_isHomogeneous_of_nonzero_smul Z
    (fun a _ x hx => hcone a x hx)
  intro d f hf
  change (MvPolynomial.decomposition.decompose' f d : MvPolynomial (Fin n) ℚ) ∈ _
  rw [MvPolynomial.decomposition.decompose'_apply]
  change map (algebraMap ℚ GeometricField) (homogeneousComponent d f) ∈
    vanishingIdeal GeometricField Z
  rw [map_homogeneousComponent]
  change map (algebraMap ℚ GeometricField) f ∈ vanishingIdeal GeometricField Z at hf
  have hd := hI d hf
  change (MvPolynomial.decomposition.decompose'
    (map (algebraMap ℚ GeometricField) f) d : GeometricPolynomial n) ∈ _ at hd
  rwa [MvPolynomial.decomposition.decompose'_apply] at hd

/-- One fixed integral homogeneous family generates the actual reduced
geometric ideal, with an exact pointwise zero criterion. -/
theorem exists_homogeneous_model {n : ℕ} (Z : Set (GeometricPoint n))
    (hclosed : AlgebraicallyClosedSet Z) (hcone : IsAffineCone Z)
    (hstable : ∀ (σ : GeometricField ≃ₐ[ℚ] GeometricField),
      ∀ x ∈ Z, galoisPoint σ x ∈ Z) :
    ∃ (r : ℕ) (G : Fin r → MvPolynomial (Fin n) ℤ) (d : Fin r → ℕ),
      (∀ i, (G i).IsHomogeneous (d i)) ∧
      Ideal.span (Set.range (fun i => map (Int.castRingHom ℚ) (G i))) = rationalIdeal Z ∧
      Ideal.span (Set.range (fun i => map (Int.castRingHom GeometricField) (G i))) =
        vanishingIdeal GeometricField Z ∧
      ∀ x : GeometricPoint n, x ∈ Z ↔
        ∀ i, eval₂Hom (Int.castRingHom GeometricField) x (G i) = 0 := by
  classical
  obtain ⟨E, hE, heq⟩ := TranslatedDepthSeven.exists_integral_homogeneous_equations_map_ideal_eq
    (rationalIdeal Z) (rationalIdeal_isHomogeneous Z hcone)
  let a : Fin (Fintype.card E) ≃ E := (Fintype.equivFin E).symm
  let G : Fin (Fintype.card E) → MvPolynomial (Fin n) ℤ := fun i => (a i).val
  have hrange : Set.range G = (E : Set (MvPolynomial (Fin n) ℤ)) := by
    ext f
    constructor
    · rintro ⟨i, rfl⟩
      exact (a i).property
    · intro hf
      exact ⟨a.symm ⟨f,hf⟩, by simp [G]⟩
  have hdegree : ∀ i, ∃ d : ℕ, (G i).IsHomogeneous d := fun i => hE (G i) (a i).property
  choose d hd using hdegree
  have hQ : Ideal.span (Set.range (fun i => map (Int.castRingHom ℚ) (G i))) =
      rationalIdeal Z := by
    rw [Ideal.map_span, ← hrange, ← Set.range_comp] at heq
    exact heq
  have hcomp : (algebraMap ℚ GeometricField).comp (Int.castRingHom ℚ) =
      Int.castRingHom GeometricField := RingHom.ext_int _ _
  have hG : Ideal.span (Set.range (fun i => map (Int.castRingHom GeometricField) (G i))) =
      vanishingIdeal GeometricField Z := by
    have hmap := congrArg (fun I : Ideal (MvPolynomial (Fin n) ℚ) =>
      I.map (map (algebraMap ℚ GeometricField))) hQ
    dsimp only at hmap
    rw [map_rationalIdeal Z hstable, Ideal.map_span, ← Set.range_comp] at hmap
    simpa only [Function.comp_def, map_map, hcomp] using hmap
  refine ⟨Fintype.card E, G, d, hd, hQ, hG, ?_⟩
  intro x
  rw [← hclosed]
  change x ∈ zeroLocus GeometricField (vanishingIdeal GeometricField Z) ↔ _
  rw [← hG, zeroLocus_span]
  change (∀ P ∈ Set.range (fun i => map (Int.castRingHom GeometricField) (G i)),
    eval x P = 0) ↔ _
  simp only [Set.forall_mem_range, eval_map]
  rfl

end CubicTenVariables.GaloisClosedConeIntegralModel
