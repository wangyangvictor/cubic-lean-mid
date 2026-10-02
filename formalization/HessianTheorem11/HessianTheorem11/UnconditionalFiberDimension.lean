import HessianTheorem11.UnconditionalFiberClosed
import HessianTheorem11.UnconditionalFiberOpenHeight
import HessianTheorem11.KernelAnnihilatorGeometry

/-! The full affine-fiber dimension interface is proved from commutative
algebra. No generic rank, smoothness, or external geometry input is used. -/
noncomputable section
namespace HessianTheorem11.UnconditionalFiberDimension
open MvPolynomial Ideal UnconditionalCutHeight UnconditionalFiberClosed
  UnconditionalFiberOpenHeight

/-- The fiber inequality at every point of a nonempty open subset of a
closed irreducible affine set. -/
theorem open_fiber_dimension {σ τ : Type} [Fintype σ] [Fintype τ]
    (P : τ → MvPolynomial σ GeometricField) (U R : Set (σ → GeometricField))
    (hU : AlgebraicallyClosedSet U) (hi : GeometricallyIrreducible U)
    (hR : RelativelyOpenSet U R) (x : σ → GeometricField) (hx : x ∈ R) :
    affineDimension U ≤ affineDimension (polynomialMap P '' U) +
      affineDimension {z | z ∈ R ∧ polynomialMap P z = polynomialMap P x} := by
  have hxU : x ∈ U := by obtain ⟨C, hC, he⟩ := hR; exact (he ▸ hx).1
  let B := CoordinateRing (polynomialMap P '' U)
  let A := CoordinateRing U
  letI : (vanishingIdeal GeometricField U).IsPrime := hi
  let f := coordinateMap P U
  let m := RingHom.ker (pointEvaluation U x hxU)
  letI : m.IsMaximal := RingHom.ker_isMaximal_of_surjective _ (pointEvaluation_surjective U x hxU)
  letI : Algebra B A := f.toRingHom.toAlgebra
  let p := m.under B
  let J := p.map (algebraMap B A)
  have hJ : J ≤ m := Ideal.map_comap_le
  let m' := m.map (Ideal.Quotient.mk J)
  letI : m'.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by simpa only [Ideal.mk_ker] using hJ)
  let q : MvPolynomial σ GeometricField →+* A ⧸ J :=
    (Ideal.Quotient.mk J).comp (Ideal.Quotient.mk (vanishingIdeal GeometricField U))
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  have hm : m'.comap q = vanishingIdeal GeometricField {x} := by
    ext k
    change Ideal.Quotient.mk J (Ideal.Quotient.mk _ k) ∈ m.map (Ideal.Quotient.mk J) ↔ _
    rw [Ideal.mem_quotient_iff_mem hJ]
    change eval x k = 0 ↔ k ∈ vanishingIdeal GeometricField {x}
    exact (mem_vanishingIdeal_singleton_iff x k).symm
  have hzero : zeroLocus GeometricField (RingHom.ker q) =
      {z | z ∈ U ∧ polynomialMap P z = polynomialMap P x} := by
    have he : RingHom.ker q = J.comap (Ideal.Quotient.mk (vanishingIdeal GeometricField U)) := by
      ext k
      simp [q, Ideal.Quotient.eq_zero_iff_mem]
    rw [he]
    exact fiber_zeroLocus P U hU x hxU
  have hfopen : RelativelyOpenSet (zeroLocus GeometricField (RingHom.ker q))
      {z | z ∈ R ∧ polynomialMap P z = polynomialMap P x} := by
    obtain ⟨C, hC, he⟩ := hR
    refine ⟨C, hC, ?_⟩
    rw [hzero, he]
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_diff]
    tauto
  have hfheight := point_height_le_open_dimension q hq m' x hm _ hfopen ⟨hx, rfl⟩
  have hh := Ideal.height_le_height_add_of_liesOver p m
  have hb : (p.height : Dimension) ≤ ringKrullDim B :=
    Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
  change ringKrullDim A ≤ ringKrullDim B + _
  rw [← finiteType_maximal_height A m]
  exact (show (m.height : Dimension) ≤ (p.height : Dimension) + (m'.height : Dimension) by
    exact_mod_cast hh).trans (add_le_add hb hfheight)

/-- A dense open in the image closure meets the actual image. -/
theorem image_meets_dense_open {σ τ : Type*}
    (P : τ → MvPolynomial σ GeometricField) (R : Set (σ → GeometricField))
    (hne : R.Nonempty) (O : Set (τ → GeometricField))
    (hO : RelativelyOpenSet (geometricClosure (polynomialMap P '' R)) O)
    (hdense : geometricClosure O = geometricClosure (polynomialMap P '' R)) :
    ∃ x ∈ R, polynomialMap P x ∈ O := by
  obtain ⟨C, hC, he⟩ := hO
  by_contra hn
  have hsub : polynomialMap P '' R ⊆ C := by
    rintro _ ⟨x, hx, rfl⟩
    by_contra hc
    apply hn
    refine ⟨x, hx, ?_⟩
    rw [he]
    exact ⟨subset_geometricClosure _ ⟨x, hx, rfl⟩, hc⟩
  have hclosure := geometricClosure_subset_closed hsub hC
  have hempty : O = ∅ := by rw [he]; exact Set.diff_eq_empty.mpr hclosure
  rw [hempty] at hdense
  obtain ⟨x, hx⟩ := hne
  have hh := subset_geometricClosure _ (Set.mem_image_of_mem (polynomialMap P) hx)
  rw [← hdense] at hh
  simpa only [geometricClosure, vanishingIdeal_empty, zeroLocus_top] using hh

/-- The exact former FD package is now constructed without any premise. -/
def affineFiberDimensionInput : AffineFiberDimensionInput where
  dimension_le := by
    intro σ τ _ _ P R hi hR O hO hdense k hbound
    obtain ⟨x, hx, hxO⟩ := image_meets_dense_open P R hi.nonempty O hO hdense
    have hiU : GeometricallyIrreducible (geometricClosure R) :=
      (geometricallyIrreducible_closure_iff _).mpr hi
    have hh := open_fiber_dimension P (geometricClosure R) R
      (algebraicallyClosedSet_geometricClosure _) hiU hR x hx
    have himage : affineDimension (polynomialMap P '' geometricClosure R) =
        affineDimension (geometricClosure (polynomialMap P '' R)) := by
      rw [← affineDimension_closure (polynomialMap P '' geometricClosure R),
        geometricClosure_polynomialMap_image_closure]
    rw [affineDimension_closure, himage] at hh
    exact hh.trans (add_le_add_right (hbound _ hxO) _)

end HessianTheorem11.UnconditionalFiberDimension
