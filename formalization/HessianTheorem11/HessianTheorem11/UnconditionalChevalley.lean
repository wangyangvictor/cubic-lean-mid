import HessianTheorem11.UnconditionalChevalleySpectrum
import HessianTheorem11.UnconditionalFiberClosed
import HessianTheorem11.AffineOpenSets

/-! Actual point-set Chevalley for closed irreducible affine sources:
the polynomial image contains a dense principal open in its actual closure.
All statements are proved, with no external AG interface. -/
noncomputable section
namespace HessianTheorem11.UnconditionalChevalley
open MvPolynomial Ideal UnconditionalFiberClosed UnconditionalChevalleySpectrum

/-- The coordinate map into the actual image coordinate ring is injective. -/
theorem coordinateMap_injective {σ τ : Type*}
    (P : τ → MvPolynomial σ GeometricField) (Z : Set (σ → GeometricField)) :
    Function.Injective (coordinateMap P Z) := by
  apply (injective_iff_map_eq_zero (coordinateMap P Z)).mpr
  intro a ha
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [vanishingIdeal_polynomialMap_image]
  change aeval P q ∈ vanishingIdeal GeometricField Z
  exact Ideal.Quotient.eq_zero_iff_mem.mp (show Ideal.Quotient.mk _ (aeval P q) = 0 from ha)

def closureEvaluation {σ : Type*} (Z : Set (σ → GeometricField))
    (x : σ → GeometricField) (hx : x ∈ geometricClosure Z) :
    CoordinateRing Z →+* GeometricField :=
  Ideal.Quotient.lift _ (eval x) (fun q hq => hx q hq)

@[simp] theorem closureEvaluation_mk {σ : Type*} (Z : Set (σ → GeometricField))
    (x : σ → GeometricField) (hx : x ∈ geometricClosure Z)
    (q : MvPolynomial σ GeometricField) :
    closureEvaluation Z x hx (Ideal.Quotient.mk _ q) = eval x q := rfl

theorem closureEvaluation_surjective {σ : Type*} (Z : Set (σ → GeometricField))
    (x : σ → GeometricField) (hx : x ∈ geometricClosure Z) :
    Function.Surjective (closureEvaluation Z x hx) := by
  intro c
  exact ⟨Ideal.Quotient.mk _ (C c), by simp⟩

/-- A closed image point whose ideal lies in the spectral image is the
image of an actual geometric source point. -/
theorem image_point_of_spectrum {σ τ : Type} [Fintype σ] [Fintype τ]
    (P : τ → MvPolynomial σ GeometricField) (Z : Set (σ → GeometricField))
    (hZ : AlgebraicallyClosedSet Z) (y : τ → GeometricField)
    (hy : y ∈ geometricClosure (polynomialMap P '' Z))
    (h : let m := RingHom.ker (closureEvaluation (polynomialMap P '' Z) y hy)
      (⟨m, RingHom.ker_isPrime _⟩ : PrimeSpectrum (CoordinateRing (polynomialMap P '' Z))) ∈
        Set.range (coordinateMap P Z).toRingHom.specComap) :
    y ∈ polynomialMap P '' Z := by
  let m := RingHom.ker (closureEvaluation (polynomialMap P '' Z) y hy)
  letI : m.IsMaximal := RingHom.ker_isMaximal_of_surjective _
    (closureEvaluation_surjective (polynomialMap P '' Z) y hy)
  obtain ⟨M, hM, hMm⟩ := exists_maximal_over (coordinateMap P Z).toRingHom m h
  letI : M.IsMaximal := hM
  let N := M.comap (Ideal.Quotient.mk (vanishingIdeal GeometricField Z))
  letI : N.IsMaximal := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨x, hx⟩ := (MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton).mp
    (inferInstance : N.IsMaximal)
  have hxZ : x ∈ Z := by
    rw [← hZ]
    intro q hq
    have hqN : q ∈ N := by
      change Ideal.Quotient.mk _ q ∈ M
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hq]
      exact M.zero_mem
    rw [hx] at hqN
    exact hqN x (Set.mem_singleton x)
  refine ⟨x, hxZ, ?_⟩
  ext i
  have hk : Ideal.Quotient.mk (vanishingIdeal GeometricField (polynomialMap P '' Z))
      (X i - C (y i)) ∈ m := by
    change closureEvaluation _ y hy (Ideal.Quotient.mk _ _) = 0
    simp
  have hkM : Ideal.Quotient.mk (vanishingIdeal GeometricField Z) (P i - C (y i)) ∈ M := by
    rw [← hMm] at hk
    simpa using hk
  have hkN : P i - C (y i) ∈ N := hkM
  rw [hx] at hkN
  have hz := hkN x (Set.mem_singleton x)
  apply sub_eq_zero.mp
  simpa [polynomialMap] using hz

/-- A polynomial image contains a principal open in its actual closure,
and that principal open meets the actual image. -/
theorem exists_principal_open_in_image {σ τ : Type} [Fintype σ] [Fintype τ]
    (P : τ → MvPolynomial σ GeometricField) (Z : Set (σ → GeometricField))
    (hZ : AlgebraicallyClosedSet Z) (hi : GeometricallyIrreducible Z) :
    ∃ g : MvPolynomial τ GeometricField,
      (∃ y ∈ polynomialMap P '' Z, eval y g ≠ 0) ∧
      ∀ y ∈ geometricClosure (polynomialMap P '' Z), eval y g ≠ 0 →
        y ∈ polynomialMap P '' Z := by
  let B := CoordinateRing (polynomialMap P '' Z)
  let A := CoordinateRing Z
  letI : (vanishingIdeal GeometricField Z).IsPrime := hi
  letI : (vanishingIdeal GeometricField (polynomialMap P '' Z)).IsPrime :=
    hi.polynomialMap_image P
  let f := coordinateMap P Z
  letI : Algebra B A := f.toAlgebra
  letI : IsScalarTower GeometricField B A := IsScalarTower.of_algHom f
  letI : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType GeometricField B A
  have hfp : f.toRingHom.FinitePresentation :=
    RingHom.FinitePresentation.of_finiteType.mp
      (RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType B A))
  obtain ⟨a, ha, hopen⟩ := exists_basicOpen_subset_range f.toRingHom hfp
    (coordinateMap_injective P Z)
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨g, ?_, ?_⟩
  · by_contra hn
    push_neg at hn
    exact ha (Ideal.Quotient.eq_zero_iff_mem.mpr hn)
  · intro y hy hgy
    apply image_point_of_spectrum P Z hZ y hy
    apply hopen
    change ¬ closureEvaluation (polynomialMap P '' Z) y hy (Ideal.Quotient.mk _ g) = 0
    exact hgy

/-- The same theorem packaged with the project's actual relative-open,
nonempty, and dense conventions. -/
theorem exists_dense_open_subset_image {σ τ : Type} [Fintype σ] [Fintype τ]
    (P : τ → MvPolynomial σ GeometricField) (Z : Set (σ → GeometricField))
    (hZ : AlgebraicallyClosedSet Z) (hi : GeometricallyIrreducible Z) :
    ∃ O : Set (τ → GeometricField),
      RelativelyOpenSet (geometricClosure (polynomialMap P '' Z)) O ∧ O.Nonempty ∧
      geometricClosure O = geometricClosure (polynomialMap P '' Z) ∧
      O ⊆ polynomialMap P '' Z := by
  obtain ⟨g, ⟨y, hy, hgy⟩, hsub⟩ := exists_principal_open_in_image P Z hZ hi
  let O := {y | y ∈ geometricClosure (polynomialMap P '' Z) ∧ eval y g ≠ 0}
  have hopen : RelativelyOpenSet (geometricClosure (polynomialMap P '' Z)) O := by
    refine ⟨zeroLocus GeometricField (Ideal.span {g}), algebraicallyClosedSet_zeroLocus _, ?_⟩
    ext y
    simp [O, zeroLocus_span, mem_zeroLocus_iff]
  have hne : O.Nonempty := ⟨y, subset_geometricClosure _ hy, hgy⟩
  refine ⟨O, hopen, hne, ?_, fun y hy => hsub y hy.1 hy.2⟩
  exact hopen.dense_of_nonempty (algebraicallyClosedSet_geometricClosure _)
    ((geometricallyIrreducible_closure_iff _).mpr (hi.polynomialMap_image P)) hne

end HessianTheorem11.UnconditionalChevalley
