import HessianTheorem11.UnconditionalCutHeight
import HessianTheorem11.BibleHyperplanes
import HessianTheorem11.ReducedChartScaling
import HessianTheorem11.ReducedMaximalComponent

/-! Principal cuts of actual affine sets, derived from local commutative
algebra and the full-height theorem. No GR or other external input is used. -/
noncomputable section
namespace HessianTheorem11.UnconditionalCutDimension
open MvPolynomial Ideal UnconditionalCutHeight
open scoped Pointwise

theorem quotient_radical_dimension {R : Type*} [CommRing R] (I : Ideal R) :
    ringKrullDim (R ⧸ I.radical) = ringKrullDim (R ⧸ I) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient, PrimeSpectrum.zeroLocus_radical]

theorem localized_quotient_dimension_le {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S] (x : R) :
    ringKrullDim (S ⧸ Ideal.span {algebraMap R S x}) ≤
      ringKrullDim (R ⧸ Ideal.span {x}) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient]
  let f : PrimeSpectrum.zeroLocus (R := S) (Ideal.span {algebraMap R S x}) →
      PrimeSpectrum.zeroLocus (R := R) (Ideal.span {x}) := fun P =>
    ⟨(algebraMap R S).specComap P.val, by
      apply Ideal.span_le.mpr
      rintro _ rfl
      exact P.property (Ideal.subset_span rfl)⟩
  apply Order.krullDim_le_of_strictMono f
  intro P Q hPQ
  exact (IsLocalization.orderEmbedding M S).strictMono hPQ

/-- A cut through a maximal ideal of full height loses at most one
dimension, by localization and the Noetherian local principal-cut theorem. -/
theorem cut_dimension_of_full_height {R : Type*} [CommRing R]
    [IsNoetherianRing R] (m : Ideal R) [m.IsMaximal]
    (hm : (m.height : Dimension) = ringKrullDim R) (x : R) (hx : x ∈ m) :
    ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span {x}) + 1 := by
  let S := Localization.AtPrime m
  have hlocal : algebraMap R S x ∈ IsLocalRing.maximalIdeal S := by
    change x ∈ Ideal.comap (algebraMap R S) (IsLocalRing.maximalIdeal S)
    rwa [Localization.AtPrime.comap_maximalIdeal]
  have h := ringKrullDim_le_ringKrullDim_quotSMulTop_succ hlocal
  have he : Ideal.span {algebraMap R S x} = algebraMap R S x • (⊤ : Ideal S) := by
    simp [← Submodule.ideal_span_singleton_smul]
  rw [← he, IsLocalization.AtPrime.ringKrullDim_eq_height m S, hm] at h
  exact h.trans (by
    apply add_le_add_left
    exact localized_quotient_dimension_le m.primeCompl x)

theorem cut_eq_zeroLocus {n : ℕ} (Z : Set (GeometricPoint n))
    (hZ : AlgebraicallyClosedSet Z) (P : GeometricPolynomial n) :
    {x | x ∈ Z ∧ eval x P = 0} =
      zeroLocus GeometricField (vanishingIdeal GeometricField Z ⊔ Ideal.span {P}) := by
  ext x
  constructor
  · rintro ⟨hx, hp⟩
    have h : vanishingIdeal GeometricField Z ⊔ Ideal.span {P} ≤ RingHom.ker (eval x) := by
      refine sup_le (fun q hq => hq x hx) (Ideal.span_le.mpr ?_)
      rintro _ rfl
      exact hp
    exact fun q hq => h hq
  · intro hx
    refine ⟨?_, hx P (Ideal.mem_sup_right (Ideal.subset_span rfl))⟩
    rw [← hZ]
    exact fun q hq => hx q (Ideal.mem_sup_left hq)

theorem affine_cut_dimension_eq_quotient {n : ℕ} (Z : Set (GeometricPoint n))
    (hZ : AlgebraicallyClosedSet Z) (P : GeometricPolynomial n) :
    affineDimension {x | x ∈ Z ∧ eval x P = 0} =
      ringKrullDim ((GeometricPolynomial n ⧸ vanishingIdeal GeometricField Z) ⧸
        Ideal.span {Ideal.Quotient.mk (vanishingIdeal GeometricField Z) P}) := by
  rw [cut_eq_zeroLocus Z hZ P]
  unfold affineDimension
  rw [vanishingIdeal_zeroLocus_eq_radical, quotient_radical_dimension]
  have he : Ideal.span {Ideal.Quotient.mk (vanishingIdeal GeometricField Z) P} =
      (Ideal.span {P}).map (Ideal.Quotient.mk (vanishingIdeal GeometricField Z)) := by
    rw [Ideal.map_span]
    simp
  rw [he]
  exact (DoubleQuot.quotQuotEquivQuotSup
    (vanishingIdeal GeometricField Z) (Ideal.span {P})).ringKrullDim.symm

/-- Any nonempty principal cut of an irreducible closed affine set has
dimension at least the original dimension minus one. -/
theorem irreducible_cut_dimension {n : ℕ} (Z : Set (GeometricPoint n))
    (hZ : AlgebraicallyClosedSet Z) (hi : GeometricallyIrreducible Z)
    (P : GeometricPolynomial n) (hne : ∃ x ∈ Z, eval x P = 0) :
    affineDimension Z ≤ affineDimension {x | x ∈ Z ∧ eval x P = 0} + 1 := by
  obtain ⟨x, hx, hp⟩ := hne
  let I := vanishingIdeal GeometricField Z
  let A := GeometricPolynomial n ⧸ I
  letI : I.IsPrime := hi
  let ev : A →+* GeometricField := Ideal.Quotient.lift I (eval x) (fun q hq => hq x hx)
  have hev : Function.Surjective ev := by
    intro c
    refine ⟨Ideal.Quotient.mk I (C c), ?_⟩
    change eval x (C c) = c
    simp
  let m := RingHom.ker ev
  letI : m.IsMaximal := RingHom.ker_isMaximal_of_surjective ev hev
  have hq : Ideal.Quotient.mk I P ∈ m := by
    change ev (Ideal.Quotient.mk I P) = 0
    simpa only [ev, Ideal.Quotient.lift_mk] using hp
  rw [affine_cut_dimension_eq_quotient Z hZ P]
  exact cut_dimension_of_full_height m (finiteType_maximal_height A m) _ hq

/-- Every actual irreducible component of a closed affine cone contains
its vertex. The product and polynomial-image argument uses no dimension input. -/
theorem component_contains_origin {n : ℕ} (Z C : Set (GeometricPoint n))
    (hZ : AlgebraicallyClosedSet Z) (hcone : IsAffineCone Z)
    (hC : IsIrreducibleComponent Z C) : (0 : GeometricPoint n) ∈ C := by
  let W := geometricClosure (ReducedChartScaling.scaledImage C)
  have hi : GeometricallyIrreducible W := by
    apply (geometricallyIrreducible_closure_iff _).mpr
    rw [← ReducedChartScaling.scale_image]
    exact (ReducedChartScaling.cylinder_irreducible C hC.irreducible).polynomialMap_image _
  have hCW : C ⊆ W := by
    intro x hx
    exact subset_geometricClosure _ ⟨x, hx, 1, one_smul _ _⟩
  have hWZ : W ⊆ Z := by
    apply geometricClosure_subset_closed _ hZ
    rintro x ⟨c, hc, a, rfl⟩
    exact hcone a c (hC.subset hc)
  have he : W = C := hC.maximal W (algebraicallyClosedSet_geometricClosure _) hi hCW hWZ
  obtain ⟨c, hc⟩ := hC.irreducible.nonempty
  rw [← he]
  exact subset_geometricClosure _ ⟨c, hc, 0, zero_smul _ _⟩

/-- The exact homogeneous-cut interface is a theorem, with no external
geometric input. Positive degree makes the cut meet every cone component. -/
def homogeneousCutDimensionInput : BibleHyperplanes.HomogeneousCutDimensionInput where
  dimension_cut := by
    intro n Z hZ hcone P d hd hP
    by_cases hne : Z.Nonempty
    · obtain ⟨C, hC, hdim⟩ := ReducedMaximalComponent.maximal_dimension_component Z hZ hne
      have hp0 : eval (0 : GeometricPoint n) P = 0 := by
        rw [eval_zero]
        change P.coeff 0 = 0
        exact hP.coeff_eq_zero (by simpa using Nat.ne_of_lt hd)
      calc
        affineDimension Z = affineDimension C := hdim.symm
        _ ≤ affineDimension {x | x ∈ C ∧ eval x P = 0} + 1 :=
          irreducible_cut_dimension C hC.closed hC.irreducible P
            ⟨0, component_contains_origin Z C hZ hcone hC, hp0⟩
        _ ≤ affineDimension {x | x ∈ Z ∧ eval x P = 0} + 1 := by
          apply add_le_add_left
          exact affineDimension_mono (fun x hx => ⟨hC.subset hx.1, hx.2⟩)
    · have he : Z = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      rw [he, affineDimension_empty]
      exact bot_le

end HessianTheorem11.UnconditionalCutDimension
