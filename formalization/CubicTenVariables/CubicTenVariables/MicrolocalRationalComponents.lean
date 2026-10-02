import CubicTenVariables.ProjectiveMicrolocalModels
import CubicTenVariables.RationalComponentDescent
import HessianTheorem11.ConeComponents
import TranslatedDepthSeven.QbarDetectsGeometricPrimeness

/-! Actual geometric components of the rational microlocal depth closure
have dense rational points. Consequently each component descends, with
finite homogeneous integral equations whose rational ideal is prime and
whose extension to every coefficient field is prime. The finite cover and
its dimensions are constructed, rather than supplied as hypotheses.
Empty rational loci require no exceptional component or adjoined origin.
No new literature premise or counting statement is introduced. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CubicTenVariables.MicrolocalRationalComponents

open MvPolynomial HessianTheorem11 TranslatedDepthSeven
open ProjectiveMicrolocalData ProjectiveMicrolocalModels
open BihomogeneousIncidenceFamily RationalConeClosure RationalConeComponents
attribute [local instance] MvPolynomial.gradedAlgebra

variable {n t j : ℕ} {F : MvPolynomial (Fin n) ℤ}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial n n}

/-- Density passes to each actual geometric component of the exact,
empty-preserving rational closure. -/
theorem component_rational_dense (h : Geometry F f) (hj : 0 < j)
    (Y : Set (GeometricPoint n)) (hY : IsIrreducibleComponent (rationalDepth f j) Y) :
    geometricClosure (rationalEmbedding '' rationalPoints Y) = Y := by
  let A := rationalEmbedding '' rationalPoints (ProjectiveMicrolocalDepth.depth f j)
  have hd := closure_inter_component_of_dense (rationalDepth f j) A Y
    (rationalDepth_closed j) (show geometricClosure A = rationalDepth f j from rfl) hY
  have he : A ∩ Y = rationalEmbedding '' rationalPoints Y := by
    ext x
    constructor
    · rintro ⟨⟨q,hq,rfl⟩,hqY⟩
      exact ⟨q,hqY,rfl⟩
    · rintro ⟨q,hq,rfl⟩
      exact ⟨⟨q,rationalDepth_subset h hj (hY.subset hq),rfl⟩,hq⟩
  rwa [he] at hd

/-- Each component is stable under every rational Galois automorphism;
there is no remaining non-descending geometric-component branch. -/
theorem component_galois_stable (h : Geometry F f) (hj : 0 < j)
    (Y : Set (GeometricPoint n)) (hY : IsIrreducibleComponent (rationalDepth f j) Y)
    (σ : GeometricField ≃ₐ[ℚ] GeometricField) (x : GeometricPoint n) (hx : x ∈ Y) :
    RationalComponentDescent.galoisPoint σ x ∈ Y :=
  RationalComponentDescent.galoisPoint_mem_of_rational_dense Y
    (component_rational_dense h hj Y hY) σ x hx

theorem component_isAffineCone (h : Geometry F f)
    (Y : Set (GeometricPoint n)) (hY : IsIrreducibleComponent (rationalDepth f j) Y) :
    IsAffineCone Y :=
  hY.isAffineCone Unconditional.concentrationGeometry.toAffineComponentsInput
    (rationalDepth_closed j) (rationalDepth_cone h j)

/-- One actual component has a finite integral model, with exact reduced
geometric ideal and exact rational ideal. Primality over Q and all field
extensions is proved from the actual geometric irreducibility. -/
theorem exists_component_model (h : Geometry F f) (hj : 0 < j)
    (Y : Set (GeometricPoint n)) (hY : IsIrreducibleComponent (rationalDepth f j) Y) :
    ∃ (s : ℕ) (G : Fin s → MvPolynomial (Fin n) ℤ) (d : Fin s → ℕ),
      (∀ a, (G a).IsHomogeneous (d a)) ∧
      IntegralModelDimension.rationalIdeal G = vanishingIdeal ℚ (rationalPoints Y) ∧
      IntegralModelDimension.geometricIdeal G = vanishingIdeal GeometricField Y ∧
      (IntegralModelDimension.rationalIdeal G).IsPrime ∧
      GeometricallyPrimeMvPolynomialIdeal (IntegralModelDimension.rationalIdeal G) ∧
      (IntegralModelDimension.rationalIdeal G).IsHomogeneous (homogeneousSubmodule (Fin n) ℚ) ∧
      ringKrullDim (MvPolynomial (Fin n) ℚ ⧸ IntegralModelDimension.rationalIdeal G) =
        affineDimension Y ∧
      ∀ x : GeometricPoint n, x ∈ Y ↔
        ∀ a, eval₂ (Int.castRingHom GeometricField) x (G a) = 0 := by
  have hcone := component_isAffineCone h Y hY
  have hdense := component_rational_dense h hj Y hY
  obtain ⟨s,G,d,hd,hQ,hG,hpoints,_⟩ :=
    ExactRationalConeModel.exists_homogeneous_model Y hcone hY.closed
  have hclosure : ExactRationalConeModel.rationalClosure Y = Y := hdense
  rw [hclosure] at hG hpoints
  have hgeom : ((IntegralModelDimension.rationalIdeal G).map
      (map (algebraMap ℚ GeometricField))).IsPrime := by
    rw [IntegralModelDimension.map_rationalIdeal,hG]
    exact hY.irreducible
  have hgeometric : GeometricallyPrimeMvPolynomialIdeal
      (IntegralModelDimension.rationalIdeal G) :=
    geometricallyPrime_of_qbarCoefficientExtension_isPrime _ hgeom
  have hprime : (IntegralModelDimension.rationalIdeal G).IsPrime := by
    letI : Algebra (MvPolynomial (Fin n) ℚ) (MvPolynomial (Fin n) GeometricField) :=
      MvPolynomial.algebraMvPolynomial
    letI := hgeom
    have hc : ((IntegralModelDimension.rationalIdeal G).map
        (map (algebraMap ℚ GeometricField))).comap
          (map (algebraMap ℚ GeometricField)) = IntegralModelDimension.rationalIdeal G :=
      Ideal.comap_map_eq_self_of_faithfullyFlat (IntegralModelDimension.rationalIdeal G)
    rw [← hc]
    exact Ideal.IsPrime.comap _
  have hhom : (IntegralModelDimension.rationalIdeal G).IsHomogeneous
      (homogeneousSubmodule (Fin n) ℚ) := by
    rw [hQ]
    apply DavenportHomogeneity.vanishingIdeal_isHomogeneous_of_nonzero_smul
    intro a _ q hq
    change rationalEmbedding (a • q) ∈ Y
    rw [rationalEmbedding_smul]
    exact hcone _ _ hq
  exact ⟨s,G,d,hd,hQ,hG,hprime,hgeometric,hhom,
    IntegralModelDimension.rational_quotient_dimension_eq G Y hY.irreducible.nonempty hG,
    hpoints⟩

/-- Finite actual component equations of the source-defined rational depth
locus. The upper bound is affine dimension n-(j+1); no Hilbert-degree or
geometrically integral cover premise is supplied. -/
theorem exists_components (h : Geometry F f)
    (hF : Anisotropic (map (Int.castRingHom ℚ) F)) (hj : 0 < j) (hjn : j < n) :
    ∃ (c : ℕ) (Y : Fin c → Set (GeometricPoint n))
      (s : Fin c → ℕ) (G : ∀ i, Fin (s i) → MvPolynomial (Fin n) ℤ)
      (d : ∀ i, Fin (s i) → ℕ),
      rationalDepth f j = ⋃ i, Y i ∧
      ∀ i, IsIrreducibleComponent (rationalDepth f j) (Y i) ∧
        (∀ a, (G i a).IsHomogeneous (d i a)) ∧
        IntegralModelDimension.rationalIdeal (G i) = vanishingIdeal ℚ (rationalPoints (Y i)) ∧
        IntegralModelDimension.geometricIdeal (G i) = vanishingIdeal GeometricField (Y i) ∧
        (IntegralModelDimension.rationalIdeal (G i)).IsPrime ∧
        GeometricallyPrimeMvPolynomialIdeal (IntegralModelDimension.rationalIdeal (G i)) ∧
        (IntegralModelDimension.rationalIdeal (G i)).IsHomogeneous
          (homogeneousSubmodule (Fin n) ℚ) ∧
        ringKrullDim (MvPolynomial (Fin n) ℚ ⧸ IntegralModelDimension.rationalIdeal (G i)) =
          affineDimension (Y i) ∧
        ringKrullDim (MvPolynomial (Fin n) ℚ ⧸ IntegralModelDimension.rationalIdeal (G i)) ≤
          ((n-(j+1) : ℕ) : Dimension) ∧
        ∀ x : GeometricPoint n, x ∈ Y i ↔
          ∀ a, eval₂ (Int.castRingHom GeometricField) x (G i a) = 0 := by
  classical
  obtain ⟨c,Y,hcover,hY⟩ := ReducedMaximalComponent.finite_components
    (rationalDepth f j) (rationalDepth_closed j)
  choose s G d hd hQ hG hprime hgeom hhom hdim hpoints using
    fun i => exists_component_model h hj (Y i) (hY i)
  refine ⟨c,Y,s,G,d,hcover,?_⟩
  intro i
  refine ⟨hY i,hd i,hQ i,hG i,hprime i,hgeom i,hhom i,hdim i,?_,hpoints i⟩
  rw [hdim i]
  exact (affineDimension_mono (hY i).subset).trans (rationalDepth_dimension_le h hF hj hjn)

end CubicTenVariables.MicrolocalRationalComponents
