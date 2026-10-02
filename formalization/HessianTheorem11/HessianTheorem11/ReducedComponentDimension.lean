import HessianTheorem11.Concentration
import HessianTheorem11.AffineHypersurfaceDimension
import Mathlib.RingTheory.KrullDimension.Polynomial

/-! Two component bookkeeping assertions are consequences, not new inputs.
Finite affine dimension is proved from the polynomial-ring dimension bound
already in mathlib. Recognition of a component of maximal dimension is
derived from the retained strict dimension-drop theorem. -/

noncomputable section
namespace HessianTheorem11.ReducedComponentDimension
open MvPolynomial

theorem polynomial_ring_dimension_bounded (n : ℕ) :
    ∃ k : ℕ, ringKrullDim (MvPolynomial (Fin n) GeometricField) ≤ (k : Dimension) := by
  induction n with
  | zero =>
    refine ⟨0, ?_⟩
    rw [ringKrullDim_mvPolynomial_of_isEmpty, ringKrullDim_eq_zero_of_field]
    simp
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨2 * k + 1, ?_⟩
    rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.finSuccEquiv GeometricField n).toRingEquiv]
    apply Polynomial.ringKrullDim_le.trans
    have h : 2 * ringKrullDim (MvPolynomial (Fin n) GeometricField) + 1 ≤
        2 * (k : Dimension) + 1 := by gcongr
    simpa using h

theorem finite_dimension {σ : Type} [Fintype σ]
    (Z : Set (σ → GeometricField)) (hne : Z.Nonempty) :
    ∃ d : ℕ, affineDimension Z = (d : Dimension) := by
  classical
  obtain ⟨k, hk⟩ := polynomial_ring_dimension_bounded (Fintype.card σ)
  have he := ringKrullDim_eq_of_ringEquiv
    (MvPolynomial.renameEquiv GeometricField (Fintype.equivFin σ)).toRingEquiv
  have hbound : affineDimension Z ≤ (k : Dimension) :=
    (ringKrullDim_quotient_le (vanishingIdeal GeometricField Z)).trans (he ▸ hk)
  have hnonneg := affineDimension_nonneg_of_nonempty hne
  cases hd : affineDimension Z with
  | none =>
    rw [hd] at hnonneg
    change (0 : Dimension) ≤ ⊥ at hnonneg
    simp at hnonneg
  | some a =>
    induction a using ENat.recTopCoe with
    | top =>
      rw [hd] at hbound
      change (⊤ : Dimension) ≤ (k : Dimension) at hbound
      simp at hbound
      have hbad : (k : ℕ∞) = ⊤ := WithBot.coe_eq_coe.mp hbound
      simp at hbad
    | coe d => exact ⟨d, rfl⟩

/-- The strict closed-subset dimension theorem also applies after reindexing
any finite affine coordinate set by `Fin`. -/
theorem proper_closed (AD : AffineHypersurfaceDimensionInput)
    {σ : Type} [Fintype σ] (A B : Set (σ → GeometricField))
    (hA : AlgebraicallyClosedSet A) (hB : AlgebraicallyClosedSet B)
    (hi : GeometricallyIrreducible B) (hAB : A ⊂ B) :
    affineDimension A < affineDimension B := by
  classical
  let L := LinearEquiv.piCongrLeft GeometricField (fun _ : Fin (Fintype.card σ) =>
    GeometricField) (Fintype.equivFin σ)
  let E := PolynomialCoordinateEquiv.ofLinearEquiv L
  have hs : E.forwardMap '' A ⊂ E.forwardMap '' B := by
    refine Set.ssubset_iff_subset_ne.mpr ⟨Set.image_mono hAB.subset, ?_⟩
    intro he
    exact hAB.ne (E.pointEquiv.injective.image_injective he)
  have h := AD.proper_closed (E.forwardMap '' A) (E.forwardMap '' B)
    ((E.algebraicallyClosedSet_image_iff A).mpr hA)
    ((E.algebraicallyClosedSet_image_iff B).mpr hB)
    ((E.geometricallyIrreducible_image_iff B).mpr hi) hs
  simpa only [E.affineDimension_image] using h

/-- A closed irreducible subset having the full dimension is already a
maximal irreducible component. No component-recognition input is needed. -/
theorem dimension_maximal (AD : AffineHypersurfaceDimensionInput)
    {σ : Type} [Fintype σ] (X Z : Set (σ → GeometricField))
    (_hX : AlgebraicallyClosedSet X) (hZ : AlgebraicallyClosedSet Z)
    (hi : GeometricallyIrreducible Z) (hZX : Z ⊆ X)
    (hd : affineDimension Z = affineDimension X) : IsIrreducibleComponent X Z := by
  refine ⟨hZ, hi, hZX, ?_⟩
  intro W hW hWi hZW hWX
  by_contra hne
  have hlt := proper_closed AD Z W hZ hW hWi
    (Set.ssubset_iff_subset_ne.mpr ⟨hZW, Ne.symm hne⟩)
  have hle := affineDimension_mono hWX
  rw [← hd] at hle
  exact (not_lt_of_ge hle) hlt

end HessianTheorem11.ReducedComponentDimension
