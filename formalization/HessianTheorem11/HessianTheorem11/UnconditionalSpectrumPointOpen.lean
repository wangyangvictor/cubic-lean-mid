import HessianTheorem11.UnconditionalChevalleyOpen

/-! Spectral openness gives principal neighborhoods in the actual geometric
image, via the basic-open basis and Jacobson closed-point lifting. -/
noncomputable section
namespace HessianTheorem11.UnconditionalSpectrumPointOpen
open MvPolynomial Ideal UnconditionalFiberClosed UnconditionalChevalley
  UnconditionalChevalleyOpen

/-- An actual source point gives the corresponding point in the spectral
image, retaining the source principal-open condition. -/
theorem source_point_mem_spectral_image {σ τ : Type} [Fintype σ] [Fintype τ]
    (P : τ → MvPolynomial σ GeometricField) (Z : Set (σ → GeometricField))
    (b : MvPolynomial σ GeometricField) (x : σ → GeometricField) (hx : x ∈ Z)
    (hbx : eval x b ≠ 0) :
    let y := polynomialMap P x
    let hy : y ∈ geometricClosure (polynomialMap P '' Z) := subset_geometricClosure _ ⟨x,hx,rfl⟩
    let m := RingHom.ker (closureEvaluation (polynomialMap P '' Z) y hy)
    (⟨m, RingHom.ker_isPrime _⟩ : PrimeSpectrum (CoordinateRing (polynomialMap P '' Z))) ∈
      (coordinateMap P Z).toRingHom.specComap ''
        (PrimeSpectrum.basicOpen (Ideal.Quotient.mk (vanishingIdeal GeometricField Z) b) :
          Set (PrimeSpectrum (CoordinateRing Z))) := by
  dsimp only
  let M := RingHom.ker (pointEvaluation Z x hx)
  refine ⟨⟨M, RingHom.ker_isPrime _⟩, hbx, ?_⟩
  apply PrimeSpectrum.ext
  ext a
  obtain ⟨q,rfl⟩ := Ideal.Quotient.mk_surjective a
  change pointEvaluation Z x hx (coordinateMap P Z (Ideal.Quotient.mk _ q)) = 0 ↔
    closureEvaluation _ (polynomialMap P x) _ (Ideal.Quotient.mk _ q) = 0
  simp only [coordinateMap_mk, pointEvaluation_mk, closureEvaluation_mk, eval_polynomialMap]

/-- If the image of the source basic open is spectrally open, every actual
source point in it has a principal neighborhood inside its actual image. -/
theorem exists_principal_image_neighborhood {σ τ : Type} [Fintype σ] [Fintype τ]
    (P : τ → MvPolynomial σ GeometricField) (Z : Set (σ → GeometricField))
    (hZ : AlgebraicallyClosedSet Z) (b : MvPolynomial σ GeometricField)
    (x : σ → GeometricField) (hx : x ∈ Z) (hbx : eval x b ≠ 0)
    (hopen : IsOpen ((coordinateMap P Z).toRingHom.specComap ''
      (PrimeSpectrum.basicOpen (Ideal.Quotient.mk (vanishingIdeal GeometricField Z) b) :
        Set (PrimeSpectrum (CoordinateRing Z))))) :
    ∃ g : MvPolynomial τ GeometricField, eval (polynomialMap P x) g ≠ 0 ∧
      ∀ y ∈ geometricClosure (polynomialMap P '' Z), eval y g ≠ 0 →
        y ∈ polynomialMap P '' {z | z ∈ Z ∧ eval z b ≠ 0} := by
  let y := polynomialMap P x
  have hy : y ∈ geometricClosure (polynomialMap P '' Z) := subset_geometricClosure _ ⟨x,hx,rfl⟩
  let m := RingHom.ker (closureEvaluation (polynomialMap P '' Z) y hy)
  let p : PrimeSpectrum (CoordinateRing (polynomialMap P '' Z)) := ⟨m, RingHom.ker_isPrime _⟩
  have hp : p ∈ (coordinateMap P Z).toRingHom.specComap ''
      (PrimeSpectrum.basicOpen (Ideal.Quotient.mk (vanishingIdeal GeometricField Z) b) :
        Set (PrimeSpectrum (CoordinateRing Z))) := source_point_mem_spectral_image P Z b x hx hbx
  obtain ⟨_,⟨a,rfl⟩,ha,hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp hopen p hp
  obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨g, ha, ?_⟩
  intro z hz hgz
  apply open_image_point_of_spectrum P Z hZ b z hz
  apply hsub
  change ¬ closureEvaluation (polynomialMap P '' Z) z hz (Ideal.Quotient.mk _ g) = 0
  exact hgz

end HessianTheorem11.UnconditionalSpectrumPointOpen
