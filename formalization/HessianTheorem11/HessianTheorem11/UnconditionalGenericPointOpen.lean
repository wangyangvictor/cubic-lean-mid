import HessianTheorem11.UnconditionalSpectrumPointOpen
import HessianTheorem11.UnconditionalLocalizedOpenMap

/-! Every polynomial map from a closed irreducible affine set has an actual
source point at which all principal neighborhoods have open images locally.
This is proved from the generic smooth locus and closed-point lifting. -/
noncomputable section
namespace HessianTheorem11.UnconditionalGenericPointOpen
open MvPolynomial Ideal UnconditionalFiberClosed UnconditionalChevalley
  UnconditionalSpectrumPointOpen UnconditionalGeneric

/-- One actual source point simultaneously works for every chosen source
principal neighborhood. No point-selection or openness input is assumed. -/
theorem exists_open_point {σ τ : Type} [Fintype σ] [Fintype τ]
    (P : τ → MvPolynomial σ GeometricField) (Z : Set (σ → GeometricField))
    (hZ : AlgebraicallyClosedSet Z) (hi : GeometricallyIrreducible Z) :
    ∃ x ∈ Z, ∀ b : MvPolynomial σ GeometricField, eval x b ≠ 0 →
      ∃ g : MvPolynomial τ GeometricField, eval (polynomialMap P x) g ≠ 0 ∧
        ∀ y ∈ geometricClosure (polynomialMap P '' Z), eval y g ≠ 0 →
          y ∈ polynomialMap P '' {z | z ∈ Z ∧ eval z b ≠ 0} := by
  let B := CoordinateRing (polynomialMap P '' Z)
  let A := CoordinateRing Z
  letI : (vanishingIdeal GeometricField Z).IsPrime := hi
  letI : (vanishingIdeal GeometricField (polynomialMap P '' Z)).IsPrime := hi.polynomialMap_image P
  let f := coordinateMap P Z
  letI : Algebra B A := f.toAlgebra
  letI : IsScalarTower GeometricField B A := IsScalarTower.of_algHom f
  letI : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr
    (coordinateMap_injective P Z)
  letI : CharZero B := (RingHom.charZero_iff (algebraMap GeometricField B).injective).mp inferInstance
  letI : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType GeometricField B A
  letI : Algebra.FinitePresentation B A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨a, ha, hopen⟩ := exists_open_principal_spectrum_map B A
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨x, hx, hpx⟩ : ∃ x ∈ Z, eval x p ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact ha (Ideal.Quotient.eq_zero_iff_mem.mpr hn)
  refine ⟨x, hx, ?_⟩
  intro b hbx
  have ho := isOpen_image_basicOpen_mul
    (Ideal.Quotient.mk (vanishingIdeal GeometricField Z) p)
    (Ideal.Quotient.mk (vanishingIdeal GeometricField Z) b) hopen
  have hpb : eval x (p*b) ≠ 0 := by simpa only [map_mul] using mul_ne_zero hpx hbx
  have ho' : IsOpen (f.toRingHom.specComap ''
      (PrimeSpectrum.basicOpen (Ideal.Quotient.mk (vanishingIdeal GeometricField Z) (p*b)) :
        Set (PrimeSpectrum A))) := by
    simpa only [map_mul] using ho
  obtain ⟨g, hg, hsub⟩ := exists_principal_image_neighborhood P Z hZ (p*b) x hx hpb ho'
  refine ⟨g, hg, ?_⟩
  intro y hy hgy
  obtain ⟨z, ⟨hz, hpbz⟩, hez⟩ := hsub y hy hgy
  refine ⟨z, ⟨hz, ?_⟩, hez⟩
  intro hbz
  exact hpbz (by simp [hbz])

end HessianTheorem11.UnconditionalGenericPointOpen
