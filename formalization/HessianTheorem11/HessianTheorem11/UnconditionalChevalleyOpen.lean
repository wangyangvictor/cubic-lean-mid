import HessianTheorem11.UnconditionalChevalley

/-! Chevalley on actual nonempty open source neighborhoods. A Jacobson
closed-point lift preserves the source nonvanishing condition. -/
noncomputable section
namespace HessianTheorem11.UnconditionalChevalleyOpen
open MvPolynomial Ideal UnconditionalFiberClosed UnconditionalChevalleySpectrum
  UnconditionalChevalley

theorem maximal_coordinateIdeal_point {σ : Type} [Fintype σ]
    (Z : Set (σ → GeometricField)) (hZ : AlgebraicallyClosedSet Z)
    (M : Ideal (CoordinateRing Z)) [M.IsMaximal] :
    ∃ x ∈ Z, ∀ q : MvPolynomial σ GeometricField,
      Ideal.Quotient.mk (vanishingIdeal GeometricField Z) q ∈ M ↔ eval x q = 0 := by
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
  intro q
  change q ∈ N ↔ _
  rw [hx]
  exact mem_vanishingIdeal_singleton_iff x q

theorem open_image_point_of_spectrum {σ τ : Type} [Fintype σ] [Fintype τ]
    (P : τ → MvPolynomial σ GeometricField) (Z : Set (σ → GeometricField))
    (hZ : AlgebraicallyClosedSet Z) (b : MvPolynomial σ GeometricField)
    (y : τ → GeometricField) (hy : y ∈ geometricClosure (polynomialMap P '' Z))
    (h : let m := RingHom.ker (closureEvaluation (polynomialMap P '' Z) y hy)
      (⟨m, RingHom.ker_isPrime _⟩ : PrimeSpectrum (CoordinateRing (polynomialMap P '' Z))) ∈
        (coordinateMap P Z).toRingHom.specComap ''
          (PrimeSpectrum.basicOpen (Ideal.Quotient.mk (vanishingIdeal GeometricField Z) b) :
            Set (PrimeSpectrum (CoordinateRing Z)))) :
    y ∈ polynomialMap P '' {x | x ∈ Z ∧ eval x b ≠ 0} := by
  let m := RingHom.ker (closureEvaluation (polynomialMap P '' Z) y hy)
  letI : m.IsMaximal := RingHom.ker_isMaximal_of_surjective _
    (closureEvaluation_surjective (polynomialMap P '' Z) y hy)
  obtain ⟨M, hM, hMm, hbM⟩ := exists_maximal_over_avoiding (coordinateMap P Z).toRingHom
    m (Ideal.Quotient.mk (vanishingIdeal GeometricField Z) b) h
  letI : M.IsMaximal := hM
  obtain ⟨x, hx, hpoint⟩ := maximal_coordinateIdeal_point Z hZ M
  refine ⟨x, ⟨hx, fun hb => hbM ((hpoint b).mpr hb)⟩, ?_⟩
  ext i
  have hk : Ideal.Quotient.mk (vanishingIdeal GeometricField (polynomialMap P '' Z))
      (X i - C (y i)) ∈ m := by
    change closureEvaluation _ y hy (Ideal.Quotient.mk _ _) = 0
    simp
  have hkM : Ideal.Quotient.mk (vanishingIdeal GeometricField Z) (P i - C (y i)) ∈ M := by
    rw [← hMm] at hk
    simpa using hk
  have hz := (hpoint _).mp hkM
  apply sub_eq_zero.mp
  simpa [polynomialMap] using hz

/-- For any nonempty principal open in the source, its polynomial image
contains a principal open in the closure of the whole source image. -/
theorem exists_principal_open_in_open_image {σ τ : Type} [Fintype σ] [Fintype τ]
    (P : τ → MvPolynomial σ GeometricField) (Z : Set (σ → GeometricField))
    (hZ : AlgebraicallyClosedSet Z) (hi : GeometricallyIrreducible Z)
    (b : MvPolynomial σ GeometricField) (hb : ∃ x ∈ Z, eval x b ≠ 0) :
    ∃ g : MvPolynomial τ GeometricField,
      (∃ y ∈ polynomialMap P '' Z, eval y g ≠ 0) ∧
      ∀ y ∈ geometricClosure (polynomialMap P '' Z), eval y g ≠ 0 →
        y ∈ polynomialMap P '' {x | x ∈ Z ∧ eval x b ≠ 0} := by
  let B := CoordinateRing (polynomialMap P '' Z)
  let A := CoordinateRing Z
  letI : (vanishingIdeal GeometricField Z).IsPrime := hi
  letI : (vanishingIdeal GeometricField (polynomialMap P '' Z)).IsPrime := hi.polynomialMap_image P
  let f := coordinateMap P Z
  letI : Algebra B A := f.toAlgebra
  letI : IsScalarTower GeometricField B A := IsScalarTower.of_algHom f
  letI : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType GeometricField B A
  have hfp : f.toRingHom.FinitePresentation :=
    RingHom.FinitePresentation.of_finiteType.mp
      (RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType B A))
  have hb0 : Ideal.Quotient.mk (vanishingIdeal GeometricField Z) b ≠ 0 := by
    intro he
    obtain ⟨x, hx, hbx⟩ := hb
    exact hbx ((Ideal.Quotient.eq_zero_iff_mem.mp he) x hx)
  obtain ⟨a, ha, hopen⟩ := exists_basicOpen_subset_image_basicOpen f.toRingHom hfp
    (coordinateMap_injective P Z) _ hb0
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨g, ?_, ?_⟩
  · by_contra hn
    push_neg at hn
    exact ha (Ideal.Quotient.eq_zero_iff_mem.mpr hn)
  · intro y hy hgy
    apply open_image_point_of_spectrum P Z hZ b y hy
    apply hopen
    change ¬ closureEvaluation (polynomialMap P '' Z) y hy (Ideal.Quotient.mk _ g) = 0
    exact hgy

/-- The image of any nonempty actual relatively open source subset
contains an actual dense open of the whole image closure. -/
theorem exists_dense_open_subset_image_of_open {σ τ : Type} [Fintype σ] [Fintype τ]
    (P : τ → MvPolynomial σ GeometricField) (Z W : Set (σ → GeometricField))
    (hZ : AlgebraicallyClosedSet Z) (hi : GeometricallyIrreducible Z)
    (hW : RelativelyOpenSet Z W) (hne : W.Nonempty) :
    ∃ O : Set (τ → GeometricField),
      RelativelyOpenSet (geometricClosure (polynomialMap P '' Z)) O ∧ O.Nonempty ∧
      geometricClosure O = geometricClosure (polynomialMap P '' Z) ∧
      O ⊆ polynomialMap P '' W := by
  obtain ⟨C, hC, he⟩ := hW
  obtain ⟨x, hx⟩ := hne
  have hxZ : x ∈ Z := (he ▸ hx).1
  have hxC : x ∉ C := (he ▸ hx).2
  obtain ⟨b, hb, hbx⟩ : ∃ b ∈ vanishingIdeal GeometricField C, eval x b ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hxC (hC ▸ hn)
  obtain ⟨g, ⟨y, hy, hgy⟩, hsub⟩ :=
    exists_principal_open_in_open_image P Z hZ hi b ⟨x, hxZ, hbx⟩
  let O := {y | y ∈ geometricClosure (polynomialMap P '' Z) ∧ eval y g ≠ 0}
  have hopen : RelativelyOpenSet (geometricClosure (polynomialMap P '' Z)) O := by
    refine ⟨zeroLocus GeometricField (Ideal.span {g}), algebraicallyClosedSet_zeroLocus _, ?_⟩
    ext y
    simp [O, zeroLocus_span]
  have hneO : O.Nonempty := ⟨y, subset_geometricClosure _ hy, hgy⟩
  refine ⟨O, hopen, hneO, hopen.dense_of_nonempty (algebraicallyClosedSet_geometricClosure _)
    ((geometricallyIrreducible_closure_iff _).mpr (hi.polynomialMap_image P)) hneO, ?_⟩
  intro y hy
  obtain ⟨z, ⟨hz, hbz⟩, hez⟩ := hsub y hy.1 hy.2
  refine ⟨z, ?_, hez⟩
  rw [he]
  exact ⟨hz, fun hc => hbz (hb z hc)⟩

end HessianTheorem11.UnconditionalChevalleyOpen
