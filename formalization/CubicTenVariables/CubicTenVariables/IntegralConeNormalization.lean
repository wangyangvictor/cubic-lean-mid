import CubicTenVariables.IntegralLinearNormalization
import CubicTenVariables.IntegralModelDimension
import CubicTenVariables.DavenportHomogeneity
import CubicTenVariables.TranslatedIntegerBoxes

/-! Integral normalization and progression counts for an actual fixed cone
model. The hypotheses identify the extended equation ideal with the actual
vanishing ideal; homogeneity of the rational ideal is proved by descent. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.IntegralConeNormalization
open MvPolynomial HessianTheorem11
attribute [local instance] MvPolynomial.gradedAlgebra

variable {n t : ℕ}

/-- The original ideal equations are equivalent to the supplied generators,
over every coefficient ring, including every residue ring. -/
theorem forall_eval_span_iff (G : Fin t → MvPolynomial (Fin n) ℤ)
    {K : Type*} [CommRing K] (x : Fin n → K) :
    (∀ f ∈ Ideal.span (Set.range G), eval₂ (Int.castRingHom K) x f = 0) ↔
      ∀ i, eval₂ (Int.castRingHom K) x (G i) = 0 := by
  constructor
  · intro h i
    exact h (G i) (Ideal.subset_span (Set.mem_range_self i))
  · intro h
    have he : Ideal.span (Set.range G) ≤ RingHom.ker (eval₂Hom (Int.castRingHom K) x) := by
      apply Ideal.span_le.mpr
      rintro f ⟨i, rfl⟩
      exact h i
    exact fun f hf => he hf

theorem map_homogeneousComponent {σ K L : Type*} [CommSemiring K] [CommSemiring L]
    (f : K →+* L) (d : ℕ) (p : MvPolynomial σ K) :
    map f (homogeneousComponent d p) = homogeneousComponent d (map f p) := by
  classical
  ext m
  simp only [coeff_map, coeff_homogeneousComponent]
  split_ifs <;> simp

local instance {σ : Type*} :
    Algebra (MvPolynomial σ ℚ) (MvPolynomial σ GeometricField) :=
  MvPolynomial.algebraMvPolynomial

/-- Homogeneity descends from the algebraic closure by faithful flatness. -/
theorem isHomogeneous_of_geometric_extension {σ : Type*}
    (I : Ideal (MvPolynomial σ ℚ))
    (hI : (I.map (map (algebraMap ℚ GeometricField))).IsHomogeneous
      (homogeneousSubmodule σ GeometricField)) :
    I.IsHomogeneous (homogeneousSubmodule σ ℚ) := by
  have hcontract :
      (I.map (map (algebraMap ℚ GeometricField))).comap
        (map (algebraMap ℚ GeometricField)) = I :=
    Ideal.comap_map_eq_self_of_faithfullyFlat I
  intro d f hf
  change (MvPolynomial.decomposition.decompose' f d : MvPolynomial σ ℚ) ∈ I
  rw [MvPolynomial.decomposition.decompose'_apply, ← hcontract]
  change map (algebraMap ℚ GeometricField) (homogeneousComponent d f) ∈
    I.map (map (algebraMap ℚ GeometricField))
  rw [map_homogeneousComponent]
  have h := hI d (Ideal.mem_map_of_mem (map (algebraMap ℚ GeometricField)) hf)
  change (MvPolynomial.decomposition.decompose'
    (map (algebraMap ℚ GeometricField) f) d : MvPolynomial σ GeometricField) ∈
      I.map (map (algebraMap ℚ GeometricField)) at h
  simpa only [MvPolynomial.decomposition.decompose'_apply] using h

theorem rationalIdeal_span (G : Fin t → MvPolynomial (Fin n) ℤ) :
    IntegralLinearNormalization.rationalIdeal (Ideal.span (Set.range G)) =
      IntegralModelDimension.rationalIdeal G := by
  rw [IntegralLinearNormalization.rationalIdeal, Ideal.map_span, ← Set.range_comp]
  rfl

/-- Dilation stability of the actual geometric set supplies the missing
homogeneity hypothesis for its rational equation ideal. -/
theorem rationalIdeal_isHomogeneous (G : Fin t → MvPolynomial (Fin n) ℤ)
    (Z : Set (Fin n → GeometricField))
    (hscale : ∀ (c : GeometricField), c ≠ 0 → ∀ x ∈ Z, c • x ∈ Z)
    (hmodel : IntegralModelDimension.geometricIdeal G = vanishingIdeal GeometricField Z) :
    (IntegralModelDimension.rationalIdeal G).IsHomogeneous
      (homogeneousSubmodule (Fin n) ℚ) := by
  apply isHomogeneous_of_geometric_extension
  rw [IntegralModelDimension.map_rationalIdeal, hmodel]
  exact DavenportHomogeneity.vanishingIdeal_isHomogeneous_of_nonzero_smul Z hscale

/-- The same descent in the original integral-ideal extension notation. -/
theorem rational_homogeneity_of_model (G : Fin t → MvPolynomial (Fin n) ℤ)
    (Z : Set (Fin n → GeometricField))
    (hscale : ∀ (c : GeometricField), c ≠ 0 → ∀ x ∈ Z, c • x ∈ Z)
    (hmodel : IntegralModelDimension.geometricIdeal G = vanishingIdeal GeometricField Z) :
    ((Ideal.span (Set.range G)).map (map (Int.castRingHom ℚ))).IsHomogeneous
      (homogeneousSubmodule (Fin n) ℚ) := by
  change (IntegralLinearNormalization.rationalIdeal _).IsHomogeneous _
  rw [rationalIdeal_span]
  exact rationalIdeal_isHomogeneous G Z hscale hmodel

/-- The certificate retains membership in the original integral ideal, so
its equations remain valid at every modulus, including bad primes. -/
theorem exists_certificate (G : Fin t → MvPolynomial (Fin n) ℤ)
    (Z : Set (Fin n → GeometricField)) (hZ : Z.Nonempty)
    (hscale : ∀ (c : GeometricField), c ≠ 0 → ∀ x ∈ Z, c • x ∈ Z)
    (hmodel : IntegralModelDimension.geometricIdeal G = vanishingIdeal GeometricField Z)
    (r : ℕ) (hdim : affineDimension Z ≤ (r : Dimension)) :
    Nonempty (IntegralLinearNormalization.Certificate (Ideal.span (Set.range G)) r) := by
  apply IntegralLinearNormalization.exists_certificate
  · rw [rationalIdeal_span]
    exact IntegralModelDimension.rationalIdeal_ne_top G Z hZ hmodel
  · rw [rationalIdeal_span]
    exact rationalIdeal_isHomogeneous G Z hscale hmodel
  · rw [rationalIdeal_span, IntegralModelDimension.rational_quotient_dimension_eq G Z hZ hmodel]
    exact hdim

/-- One constant works for all closed real-centered boxes and all positive
progression moduli, on the literal original integral equation locus. -/
theorem exists_model_count_bound (G : Fin t → MvPolynomial (Fin n) ℤ)
    (Z : Set (Fin n → GeometricField)) (hZ : Z.Nonempty)
    (hscale : ∀ (c : GeometricField), c ≠ 0 → ∀ x ∈ Z, c • x ∈ Z)
    (hmodel : IntegralModelDimension.geometricIdeal G = vanishingIdeal GeometricField Z)
    (r : ℕ) (hdim : affineDimension Z ≤ (r : Dimension)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (u : Fin n → ℝ) (L : ℝ), 0 ≤ L →
      ∀ (m : ℕ), 0 < m → ∀ b : Fin n → ℤ,
      ((TranslatedIntegerBoxes.modelPoints (Ideal.span (Set.range G)) u L m b).card : ℝ) ≤
        C * (1 + L / (m : ℝ)) ^ r := by
  apply TranslatedIntegerBoxes.exists_model_count_bound
  · change IntegralLinearNormalization.rationalIdeal _ ≠ ⊤
    rw [rationalIdeal_span]
    exact IntegralModelDimension.rationalIdeal_ne_top G Z hZ hmodel
  · change (IntegralLinearNormalization.rationalIdeal _).IsHomogeneous _
    rw [rationalIdeal_span]
    exact rationalIdeal_isHomogeneous G Z hscale hmodel
  · change ringKrullDim (MvPolynomial (Fin n) ℚ ⧸ IntegralLinearNormalization.rationalIdeal _) ≤ _
    rw [rationalIdeal_span, IntegralModelDimension.rational_quotient_dimension_eq G Z hZ hmodel]
    exact hdim

end CubicTenVariables.IntegralConeNormalization
