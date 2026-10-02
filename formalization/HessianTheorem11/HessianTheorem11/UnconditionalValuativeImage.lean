import HessianTheorem11.UnconditionalValuativeCenter
import HessianTheorem11.UnconditionalChevalley
import Mathlib.RingTheory.Localization.FractionRing

/-! The generic point of an actual affine source specializes valuatively
to every point in the closure of its polynomial image. The valuation is
constructed in the genuine fraction field of the source coordinate ring. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
namespace HessianTheorem11.UnconditionalValuative
open MvPolynomial Ideal UnconditionalFiberClosed UnconditionalChevalley

variable {σ τ : Type*}

def genericPoint (Z : Set (σ → GeometricField)) :
    σ → FractionRing (CoordinateRing Z) := fun i =>
  algebraMap (CoordinateRing Z) (FractionRing (CoordinateRing Z))
    (Ideal.Quotient.mk _ (X i))

theorem eval_genericPoint (Z : Set (σ → GeometricField))
    (q : MvPolynomial σ GeometricField) :
    eval₂ (algebraMap GeometricField (FractionRing (CoordinateRing Z)))
      (genericPoint Z) q =
      algebraMap (CoordinateRing Z) (FractionRing (CoordinateRing Z))
        (Ideal.Quotient.mk _ q) := by
  let f := (algebraMap (CoordinateRing Z) (FractionRing (CoordinateRing Z))).comp
    (Ideal.Quotient.mk (vanishingIdeal GeometricField Z))
  have he : eval₂Hom (algebraMap GeometricField (FractionRing (CoordinateRing Z)))
      (genericPoint Z) = f := by
    apply MvPolynomial.ringHom_ext
    · intro c
      rw [eval₂Hom_C]
      exact IsScalarTower.algebraMap_apply GeometricField (CoordinateRing Z)
        (FractionRing (CoordinateRing Z)) c
    · intro i
      simp [genericPoint,f]
  exact congrArg (fun h => h q) he

/-- The actual generic source point satisfies every source equation. -/
theorem genericPoint_equations (Z : Set (σ → GeometricField))
    (q : MvPolynomial σ GeometricField) (hq : q ∈ vanishingIdeal GeometricField Z) :
    eval₂ (algebraMap GeometricField (FractionRing (CoordinateRing Z)))
      (genericPoint Z) q = 0 := by
  rw [eval_genericPoint,Ideal.Quotient.eq_zero_iff_mem.mpr hq,map_zero]

/-- Every actual point of the image closure is the center of a valuation
of the actual source function field. The coordinate specialization is
specified for every polynomial, not merely the coordinate generators. -/
theorem exists_image_valuation
    (P : τ → MvPolynomial σ GeometricField) (Z : Set (σ → GeometricField))
    (hi : GeometricallyIrreducible Z) (y : τ → GeometricField)
    (hy : y ∈ geometricClosure (polynomialMap P '' Z)) :
    letI : (vanishingIdeal GeometricField Z).IsPrime := hi
    ∃ V : ValuationSubring (FractionRing (CoordinateRing Z)),
      ∃ g : CoordinateRing (polynomialMap P '' Z) →+* V,
      (∀ q : MvPolynomial τ GeometricField,
        (g (Ideal.Quotient.mk _ q) : FractionRing (CoordinateRing Z)) =
          eval₂ (algebraMap GeometricField (FractionRing (CoordinateRing Z)))
            (genericPoint Z) (aeval P q)) ∧
      (∀ q : MvPolynomial τ GeometricField,
        g (Ideal.Quotient.mk _ q) ∈ IsLocalRing.maximalIdeal V ↔ eval y q = 0) := by
  letI : (vanishingIdeal GeometricField Z).IsPrime := hi
  let A := CoordinateRing Z
  let B := CoordinateRing (polynomialMap P '' Z)
  let K := FractionRing A
  let f : B →+* K := (algebraMap A K).comp (coordinateMap P Z).toRingHom
  have hf : Function.Injective f :=
    (IsFractionRing.injective A K).comp (coordinateMap_injective P Z)
  let m := RingHom.ker (closureEvaluation (polynomialMap P '' Z) y hy)
  letI : m.IsPrime := RingHom.ker_isPrime _
  obtain ⟨V,g,hg,hcenter⟩ := exists_valuation_center f hf m
  refine ⟨V,g,?_,?_⟩
  · intro q
    rw [hg,eval_genericPoint]
    rfl
  · intro q
    have he := congrArg (fun I : Ideal B => Ideal.Quotient.mk _ q ∈ I) hcenter
    exact Iff.of_eq he

end HessianTheorem11.UnconditionalValuative
