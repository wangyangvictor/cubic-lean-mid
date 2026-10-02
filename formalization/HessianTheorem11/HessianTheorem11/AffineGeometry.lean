import HessianTheorem11.AffineDimension

/-! Actual affine closures and polynomial images. These elementary facts
are proved directly from vanishing ideals; they are not external AG inputs. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial

variable {σ τ υ : Type*}

def geometricClosure (Z : Set (σ → GeometricField)) : Set (σ → GeometricField) :=
  zeroLocus GeometricField (vanishingIdeal GeometricField Z)

def AlgebraicallyClosedSet (Z : Set (σ → GeometricField)) : Prop := geometricClosure Z = Z

def GeometricallyIrreducible (Z : Set (σ → GeometricField)) : Prop :=
  (vanishingIdeal GeometricField Z).IsPrime

theorem subset_geometricClosure (Z : Set (σ → GeometricField)) : Z ⊆ geometricClosure Z :=
  zeroLocus_vanishingIdeal_le Z

theorem geometricClosure_mono {A B : Set (σ → GeometricField)} (h : A ⊆ B) :
    geometricClosure A ⊆ geometricClosure B :=
  zeroLocus_anti_mono (vanishingIdeal_anti_mono h)

theorem geometricClosure_subset_closed {A B : Set (σ → GeometricField)}
    (h : A ⊆ B) (hB : AlgebraicallyClosedSet B) : geometricClosure A ⊆ B := by
  have h' := geometricClosure_mono h
  rwa [hB] at h'

theorem algebraicallyClosedSet_zeroLocus (I : Ideal (MvPolynomial σ GeometricField)) :
    AlgebraicallyClosedSet (zeroLocus GeometricField I) := by
  apply le_antisymm
  · exact zeroLocus_anti_mono (le_vanishingIdeal_zeroLocus I)
  · exact subset_geometricClosure _

def IsAffineCone (Z : Set (σ → GeometricField)) : Prop :=
  ∀ a : GeometricField, ∀ x ∈ Z, a • x ∈ Z

theorem vanishingIdeal_geometricClosure (Z : Set (σ → GeometricField)) :
    vanishingIdeal GeometricField (geometricClosure Z) = vanishingIdeal GeometricField Z := by
  exact le_antisymm (vanishingIdeal_anti_mono (subset_geometricClosure Z))
    (le_vanishingIdeal_zeroLocus _)

theorem geometricClosure_idem (Z : Set (σ → GeometricField)) :
    geometricClosure (geometricClosure Z) = geometricClosure Z := by
  unfold geometricClosure at *
  rw [show vanishingIdeal GeometricField
    (zeroLocus GeometricField (vanishingIdeal GeometricField Z)) =
      vanishingIdeal GeometricField Z from vanishingIdeal_geometricClosure Z]

theorem algebraicallyClosedSet_geometricClosure (Z : Set (σ → GeometricField)) :
    AlgebraicallyClosedSet (geometricClosure Z) := geometricClosure_idem Z

theorem affineDimension_closure (Z : Set (σ → GeometricField)) :
    affineDimension (geometricClosure Z) = affineDimension Z := by
  unfold affineDimension
  rw [vanishingIdeal_geometricClosure]

theorem geometricallyIrreducible_closure_iff (Z : Set (σ → GeometricField)) :
    GeometricallyIrreducible (geometricClosure Z) ↔ GeometricallyIrreducible Z := by
  simp only [GeometricallyIrreducible, vanishingIdeal_geometricClosure]

theorem GeometricallyIrreducible.nonempty {Z : Set (σ → GeometricField)}
    (h : GeometricallyIrreducible Z) : Z.Nonempty := by
  by_contra he
  have hz : Z = ∅ := Set.not_nonempty_iff_eq_empty.mp he
  exact h.ne_top (by rw [hz, vanishingIdeal_empty])

theorem geometricClosure_subset_of_polynomial_vanishes
    (Z : Set (σ → GeometricField)) (F : MvPolynomial σ GeometricField)
    (h : ∀ x ∈ Z, eval x F = 0) :
    ∀ x ∈ geometricClosure Z, eval x F = 0 := by
  intro x hx
  exact hx F h

def polynomialMap (P : τ → MvPolynomial σ GeometricField)
    (x : σ → GeometricField) : τ → GeometricField := fun i => eval x (P i)

theorem eval_polynomialMap (P : τ → MvPolynomial σ GeometricField)
    (x : σ → GeometricField) (F : MvPolynomial τ GeometricField) :
    eval (polynomialMap P x) F = eval x (aeval P F) := by
  change aeval (polynomialMap P x) F = aeval x (aeval P F)
  rw [MvPolynomial.comp_aeval_apply]
  rfl

theorem vanishingIdeal_polynomialMap_image
    (P : τ → MvPolynomial σ GeometricField) (Z : Set (σ → GeometricField)) :
    vanishingIdeal GeometricField (polynomialMap P '' Z) =
      (vanishingIdeal GeometricField Z).comap (aeval P).toRingHom := by
  ext F
  constructor
  · intro h x hx
    exact (eval_polynomialMap P x F).symm.trans (h (polynomialMap P x) ⟨x, hx, rfl⟩)
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact (eval_polynomialMap P x F).trans (h x hx)

theorem polynomialMap_image_closure_subset
    (P : τ → MvPolynomial σ GeometricField) (Z : Set (σ → GeometricField)) :
    polynomialMap P '' geometricClosure Z ⊆ geometricClosure (polynomialMap P '' Z) := by
  rintro _ ⟨x, hx, rfl⟩ F hF
  rw [vanishingIdeal_polynomialMap_image] at hF
  change eval (polynomialMap P x) F = 0
  rw [eval_polynomialMap]
  exact hx (aeval P F) hF

theorem geometricClosure_polynomialMap_image_closure
    (P : τ → MvPolynomial σ GeometricField) (Z : Set (σ → GeometricField)) :
    geometricClosure (polynomialMap P '' geometricClosure Z) =
      geometricClosure (polynomialMap P '' Z) := by
  apply le_antisymm
  · have h := geometricClosure_mono (polynomialMap_image_closure_subset P Z)
    rwa [geometricClosure_idem] at h
  · exact geometricClosure_mono (Set.image_mono (subset_geometricClosure Z))

theorem GeometricallyIrreducible.polynomialMap_image
    {Z : Set (σ → GeometricField)} (h : GeometricallyIrreducible Z)
    (P : τ → MvPolynomial σ GeometricField) :
    GeometricallyIrreducible (polynomialMap P '' Z) := by
  unfold GeometricallyIrreducible
  rw [vanishingIdeal_polynomialMap_image]
  exact h.comap _

end HessianTheorem11
