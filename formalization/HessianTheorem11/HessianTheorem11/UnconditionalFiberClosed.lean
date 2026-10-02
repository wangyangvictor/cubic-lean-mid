import HessianTheorem11.UnconditionalFiberHeight
import HessianTheorem11.UnconditionalCutDimension

/-! Fiber dimension for actual closed irreducible affine sets, without
any generic-rank or fiber-dimension input. -/
noncomputable section
namespace HessianTheorem11.UnconditionalFiberClosed
open MvPolynomial Ideal UnconditionalFiberHeight UnconditionalCutDimension

abbrev CoordinateRing {σ : Type*} (Z : Set (σ → GeometricField)) :=
  MvPolynomial σ GeometricField ⧸ vanishingIdeal GeometricField Z

def coordinateMap {σ τ : Type*} (P : τ → MvPolynomial σ GeometricField)
    (Z : Set (σ → GeometricField)) :
    CoordinateRing (polynomialMap P '' Z) →ₐ[GeometricField] CoordinateRing Z :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ GeometricField _).comp (aeval P)) (by
    intro q hq
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [vanishingIdeal_polynomialMap_image] at hq
    exact hq)

@[simp] theorem coordinateMap_mk {σ τ : Type*}
    (P : τ → MvPolynomial σ GeometricField) (Z : Set (σ → GeometricField))
    (q : MvPolynomial τ GeometricField) :
    coordinateMap P Z (Ideal.Quotient.mk _ q) = Ideal.Quotient.mk _ (aeval P q) := rfl

def pointEvaluation {σ : Type*} (Z : Set (σ → GeometricField))
    (x : σ → GeometricField) (hx : x ∈ Z) : CoordinateRing Z →+* GeometricField :=
  Ideal.Quotient.lift _ (eval x) (fun q hq => hq x hx)

@[simp] theorem pointEvaluation_mk {σ : Type*} (Z : Set (σ → GeometricField))
    (x : σ → GeometricField) (hx : x ∈ Z) (q : MvPolynomial σ GeometricField) :
    pointEvaluation Z x hx (Ideal.Quotient.mk _ q) = eval x q := rfl

theorem pointEvaluation_surjective {σ : Type*} (Z : Set (σ → GeometricField))
    (x : σ → GeometricField) (hx : x ∈ Z) :
    Function.Surjective (pointEvaluation Z x hx) := by
  intro c
  exact ⟨Ideal.Quotient.mk _ (C c), by simp⟩

theorem quotient_comap_dimension {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (J : Ideal S) :
    ringKrullDim (R ⧸ J.comap f) = ringKrullDim (S ⧸ J) := by
  let g := (Ideal.Quotient.mk J).comp f
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hf
  have he : RingHom.ker g = J.comap f := by ext x; simp [g, Ideal.Quotient.eq_zero_iff_mem]
  rw [← he]
  exact (RingHom.quotientKerEquivOfSurjective hg).ringKrullDim

/-- The scheme-theoretic fiber ideal has exactly the actual point fiber
as zero locus; nilpotents are removed only when taking the vanishing ideal. -/
theorem fiber_zeroLocus {σ τ : Type*}
    (P : τ → MvPolynomial σ GeometricField) (Z : Set (σ → GeometricField))
    (hZ : AlgebraicallyClosedSet Z) (x : σ → GeometricField) (hx : x ∈ Z) :
    let f := (coordinateMap P Z).toRingHom
    let m := RingHom.ker (pointEvaluation Z x hx)
    zeroLocus GeometricField (((m.comap f).map f).comap (Ideal.Quotient.mk _)) =
      {z | z ∈ Z ∧ polynomialMap P z = polynomialMap P x} := by
  dsimp only
  let f := (coordinateMap P Z).toRingHom
  let m := RingHom.ker (pointEvaluation Z x hx)
  let J := (m.comap f).map f
  ext z
  constructor
  · intro hz
    have hzZ : z ∈ Z := by
      rw [← hZ]
      intro q hq
      apply hz q
      change Ideal.Quotient.mk _ q ∈ J
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hq]
      exact J.zero_mem
    refine ⟨hzZ, ?_⟩
    ext i
    have hm : Ideal.Quotient.mk (vanishingIdeal GeometricField (polynomialMap P '' Z))
        (X i - C (polynomialMap P x i)) ∈ m.comap f := by
      change pointEvaluation Z x hx (coordinateMap P Z (Ideal.Quotient.mk _ _)) = 0
      simp [← eval_polynomialMap, polynomialMap]
    have hh := hz (P i - C (polynomialMap P x i)) (by
      change Ideal.Quotient.mk _ (P i - C (polynomialMap P x i)) ∈ J
      have hh := Ideal.mem_map_of_mem f hm
      simpa [f] using hh)
    apply sub_eq_zero.mp
    simpa [polynomialMap] using hh
  · rintro ⟨hzZ, he⟩ q hq
    have hJ : J ≤ RingHom.ker (pointEvaluation Z z hzZ) := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
      change pointEvaluation Z z hzZ (coordinateMap P Z (Ideal.Quotient.mk _ b)) = 0
      change pointEvaluation Z x hx (coordinateMap P Z (Ideal.Quotient.mk _ b)) = 0 at ha
      simpa only [coordinateMap_mk, pointEvaluation_mk, ← eval_polynomialMap, he] using ha
    exact hJ hq

theorem closed_fiber_dimension {σ τ : Type} [Fintype σ] [Fintype τ]
    (P : τ → MvPolynomial σ GeometricField) (Z : Set (σ → GeometricField))
    (hZ : AlgebraicallyClosedSet Z) (hi : GeometricallyIrreducible Z)
    (x : σ → GeometricField) (hx : x ∈ Z) :
    affineDimension Z ≤ affineDimension (polynomialMap P '' Z) +
      affineDimension {z | z ∈ Z ∧ polynomialMap P z = polynomialMap P x} := by
  let R := CoordinateRing (polynomialMap P '' Z)
  let S := CoordinateRing Z
  letI : (vanishingIdeal GeometricField Z).IsPrime := hi
  let f := coordinateMap P Z
  let m := RingHom.ker (pointEvaluation Z x hx)
  letI : m.IsMaximal := RingHom.ker_isMaximal_of_surjective _ (pointEvaluation_surjective Z x hx)
  have h := dimension_le_base_add_fiber R S f m
  have he : affineDimension {z | z ∈ Z ∧ polynomialMap P z = polynomialMap P x} =
      ringKrullDim (S ⧸ (m.comap f.toRingHom).map f.toRingHom) := by
    rw [← fiber_zeroLocus P Z hZ x hx]
    unfold affineDimension
    rw [vanishingIdeal_zeroLocus_eq_radical, quotient_radical_dimension]
    exact quotient_comap_dimension _ Ideal.Quotient.mk_surjective _
  rw [he]
  exact h

end HessianTheorem11.UnconditionalFiberClosed
