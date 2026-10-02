import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Counting finite residue sets by a coordinate projection

This file records the elementary finite counting step behind the local
Noether-normalisation estimate.  The geometric input is deliberately absent:
one fixes a literal coordinate projection and assumes a literal upper bound
for every fibre.  Summing the fibre cardinalities then bounds the cardinality
of the original finite set.
-/

namespace TranslatedDepthSeven

noncomputable section

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- The literal fibre of a map inside a finite set. -/
def finiteMapFiber {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (projection : X → Y) (S : Finset X) (y : Y) : Finset X :=
  S.filter fun x ↦ projection x = y

@[simp]
theorem mem_finiteMapFiber_iff
    {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    {projection : X → Y} {S : Finset X} {y : Y} {x : X} :
    x ∈ finiteMapFiber projection S y ↔
      x ∈ S ∧ projection x = y := by
  simp [finiteMapFiber]

/-- Exact partition of a finite set by the fibres of any explicitly specified
map to a finite type. -/
theorem card_eq_sum_finiteMapFiber
    {X Y : Type*} [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (projection : X → Y) (S : Finset X) :
    S.card = ∑ y : Y, (finiteMapFiber projection S y).card := by
  simpa [finiteMapFiber] using
    (Finset.card_eq_sum_card_fiberwise
      (s := S) (t := Finset.univ) (f := projection)
      (fun _ _ ↦ Finset.mem_univ _))

/-- A uniform fibre bound for an arbitrary explicit map gives the expected
cardinality bound.  This is the finite statement needed for a general linear
Noether-normalisation map; no coordinate choice is built into it. -/
theorem card_finiteSet_le_of_map_fibers_le
    {X Y : Type*} [DecidableEq X] [Fintype Y] [DecidableEq Y]
    {D : ℕ} (projection : X → Y) (S : Finset X)
    (hfibre : ∀ y : Y, (finiteMapFiber projection S y).card ≤ D) :
    S.card ≤ D * Fintype.card Y := by
  rw [card_eq_sum_finiteMapFiber projection S]
  calc
    (∑ y : Y, (finiteMapFiber projection S y).card) ≤
        ∑ _y : Y, D :=
      Finset.sum_le_sum fun y _ ↦ hfibre y
    _ = D * Fintype.card Y := by simp [Nat.mul_comm]

/-- Projection from `N` coordinates to the explicitly selected `d`
coordinates.  Injectivity of `coordinates` is not needed for the counting
inequality. -/
def finiteCoordinateProjection {N d : ℕ} (coordinates : Fin d → Fin N)
    (x : Fin N → K) : Fin d → K :=
  fun i ↦ x (coordinates i)

/-- The literal fibre inside `X` over the projected residue vector `y`. -/
def finiteCoordinateProjectionFiber {N d : ℕ}
    (coordinates : Fin d → Fin N) (X : Finset (Fin N → K))
    (y : Fin d → K) : Finset (Fin N → K) :=
  finiteMapFiber (finiteCoordinateProjection coordinates) X y

omit [Fintype K] in
@[simp]
theorem mem_finiteCoordinateProjectionFiber_iff
    {N d : ℕ} {coordinates : Fin d → Fin N}
    {X : Finset (Fin N → K)} {y : Fin d → K} {x : Fin N → K} :
    x ∈ finiteCoordinateProjectionFiber coordinates X y ↔
      x ∈ X ∧ finiteCoordinateProjection coordinates x = y := by
  simp [finiteCoordinateProjectionFiber]

/-- Exact partition of a finite set by the fibres of a fixed coordinate
projection. -/
theorem card_eq_sum_finiteCoordinateProjectionFiber
    {N d : ℕ} (coordinates : Fin d → Fin N)
    (X : Finset (Fin N → K)) :
    X.card = ∑ y : Fin d → K,
      (finiteCoordinateProjectionFiber coordinates X y).card := by
  exact card_eq_sum_finiteMapFiber
    (finiteCoordinateProjection coordinates) X

/-- If every fibre of an explicit `d`-coordinate projection has cardinality
at most `D`, then the finite set has cardinality at most
`D * (#K)^d`. -/
theorem card_finiteSet_le_of_coordinateProjection_fibers_le
    {N d D : ℕ} (coordinates : Fin d → Fin N)
    (X : Finset (Fin N → K))
    (hfibre : ∀ y : Fin d → K,
      (finiteCoordinateProjectionFiber coordinates X y).card ≤ D) :
    X.card ≤ D * (Fintype.card K) ^ d := by
  simpa only [Fintype.card_fun, Fintype.card_fin] using
    card_finiteSet_le_of_map_fibers_le
      (finiteCoordinateProjection coordinates) X hfibre

/-- For a prime modulus, any explicit map from residue vectors to
d residue coordinates with fibres bounded by D gives the estimate
#X ≤ D * p^d.  The map may be a coordinate, linear, or affine-linear
projection. -/
theorem card_zmod_finiteSet_le_of_map_fibers_le
    {p N d D : ℕ} (hp : p.Prime)
    (projection : (Fin N → ZMod p) → (Fin d → ZMod p))
    (X : Finset (Fin N → ZMod p))
    (hfibre : ∀ y : Fin d → ZMod p,
      (finiteMapFiber projection X y).card ≤ D) :
    X.card ≤ D * p ^ d := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  simpa only [Fintype.card_fun, Fintype.card_fin, ZMod.card] using
    card_finiteSet_le_of_map_fibers_le projection X hfibre

/-- The residue-field specialization: for prime `p`, a fibre bound `D` for
an explicit projection `(ZMod p)^N → (ZMod p)^d` gives the exact estimate
`#X ≤ D * p^d`. -/
theorem card_zmod_finiteSet_le_of_coordinateProjection_fibers_le
    {p N d D : ℕ} (hp : p.Prime) (coordinates : Fin d → Fin N)
    (X : Finset (Fin N → ZMod p))
    (hfibre : ∀ y : Fin d → ZMod p,
      (finiteCoordinateProjectionFiber coordinates X y).card ≤ D) :
    X.card ≤ D * p ^ d := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  simpa only [ZMod.card] using
    (card_finiteSet_le_of_coordinateProjection_fibers_le
      coordinates X hfibre)

end

end TranslatedDepthSeven
