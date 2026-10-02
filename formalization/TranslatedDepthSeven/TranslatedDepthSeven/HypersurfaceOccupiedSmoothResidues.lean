import TranslatedDepthSeven.HypersurfaceMixedResidueDeterminant

/-! Occupied smooth residue classes embed in the literal smooth zero set of
the reduced equation. The columns may repeat, and no finite-field estimate,
degree factor, or smoothness hypothesis on the remaining columns is assumed. -/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial

local instance occupiedSmoothResiduePropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

private theorem eval_reduction_map (p : ℕ) (F : MvPolynomial (Fin 3) ℤ)
    (x : Fin 3 → ℤ) :
    MvPolynomial.eval (fun i => (x i : ZMod p))
      (MvPolynomial.map (Int.castRingHom (ZMod p)) F) =
        (MvPolynomial.eval x F : ZMod p) := by
  rw [MvPolynomial.eval_map]
  exact (MvPolynomial.eval₂_comp (Int.castRingHom (ZMod p)) x F).symm

/-- Literal affine zeros of the reduced integral surface equation. -/
abbrev SurfaceReductionZeroPoint (p : ℕ) (F : MvPolynomial (Fin 3) ℤ) :=
  {x : Fin 3 → ZMod p //
    MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom (ZMod p)) F) = 0}

/-- Literal affine zeros with a nonzero reduced partial derivative. -/
abbrev SurfaceSmoothReductionPoint (p : ℕ) (F : MvPolynomial (Fin 3) ℤ) :=
  {x : Fin 3 → ZMod p //
    MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom (ZMod p)) F) = 0 ∧
      ∃ v : Fin 3, MvPolynomial.eval x
        (MvPolynomial.pderiv v (MvPolynomial.map (Int.castRingHom (ZMod p)) F)) ≠ 0}

/-- The inclusion is on actual residue coordinates, not on chosen columns;
therefore repetitions in the column family do not affect injectivity. -/
def occupiedSmoothSurfaceResidueEmbedding
    {ι : Type*} (p : ℕ) (F : MvPolynomial (Fin 3) ℤ)
    (y : ι → Fin 3 → ℤ) (hzero : ∀ j, MvPolynomial.eval (y j) F = 0) :
    SurfaceOccupiedSmoothResidueClass p F y ↪ SurfaceSmoothReductionPoint p F where
  toFun c := ⟨c.val, by
    obtain ⟨j, hj⟩ := c.property
    rw [← hj]
    change MvPolynomial.eval (fun i => (y j.val i : ZMod p))
      (MvPolynomial.map (Int.castRingHom (ZMod p)) F) = 0 ∧ _
    constructor
    · rw [eval_reduction_map, hzero j.val, Int.cast_zero]
    · obtain ⟨v, hv⟩ := j.property
      refine ⟨v, ?_⟩
      change MvPolynomial.eval (fun i => (y j.val i : ZMod p))
        (MvPolynomial.pderiv v (MvPolynomial.map (Int.castRingHom (ZMod p)) F)) ≠ 0
      rwa [MvPolynomial.pderiv_map, eval_reduction_map]⟩
  inj' a b hab := Subtype.ext
    (congrArg (fun z : SurfaceSmoothReductionPoint p F => z.val) hab)

/-- A sharp inclusion bound for the occupied smooth classes used in the
mixed determinant. No injectivity of the original columns is required. -/
theorem card_occupiedSmoothSurfaceResidues_le_smoothZeroPoints
    {ι : Type*} [Fintype ι] (p : ℕ) (hp : p ≠ 0)
    (F : MvPolynomial (Fin 3) ℤ) (y : ι → Fin 3 → ℤ)
    (hzero : ∀ j, MvPolynomial.eval (y j) F = 0) :
    Fintype.card (SurfaceOccupiedSmoothResidueClass p F y) ≤
      Nat.card (SurfaceSmoothReductionPoint p F) := by
  letI : NeZero p := ⟨hp⟩
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_le_card_of_injective
    (occupiedSmoothSurfaceResidueEmbedding p F y hzero)
    (occupiedSmoothSurfaceResidueEmbedding p F y hzero).injective

/-- Smooth reduced points form a subset of all reduced points, with no
geometric integrality or degree hypothesis. -/
theorem card_smoothSurfaceReductionPoints_le_zeroPoints
    (p : ℕ) (hp : p ≠ 0) (F : MvPolynomial (Fin 3) ℤ) :
    Nat.card (SurfaceSmoothReductionPoint p F) ≤
      Nat.card (SurfaceReductionZeroPoint p F) := by
  letI : NeZero p := ⟨hp⟩
  let f : SurfaceSmoothReductionPoint p F → SurfaceReductionZeroPoint p F :=
    fun x => ⟨x.val, x.property.1⟩
  exact Nat.card_le_card_of_injective f
    (fun a b hab => Subtype.ext
      (congrArg (fun z : SurfaceReductionZeroPoint p F => z.val) hab))

/-- Direct interface for any actual affine finite-field point-count bound.
The leading coefficient of that bound is preserved exactly. -/
theorem card_occupiedSmoothSurfaceResidues_le_zeroPoints
    {ι : Type*} [Fintype ι] (p : ℕ) (hp : p ≠ 0)
    (F : MvPolynomial (Fin 3) ℤ) (y : ι → Fin 3 → ℤ)
    (hzero : ∀ j, MvPolynomial.eval (y j) F = 0) :
    Fintype.card (SurfaceOccupiedSmoothResidueClass p F y) ≤
      Nat.card (SurfaceReductionZeroPoint p F) :=
  (card_occupiedSmoothSurfaceResidues_le_smoothZeroPoints p hp F y hzero).trans
    (card_smoothSurfaceReductionPoints_le_zeroPoints p hp F)

end
end TranslatedDepthSeven
