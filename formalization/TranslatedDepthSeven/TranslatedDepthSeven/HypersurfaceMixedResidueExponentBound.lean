import TranslatedDepthSeven.HypersurfaceMixedResidueDeterminant
import TranslatedDepthSeven.SmoothSurfaceResidueExponent

/-!
# The sharp exponent for the actual mixed hypersurface residue classes

This file connects the literal smooth residue classes used by
`hypersurfaceMixedResidue_det_dvd` to the sharp numerical lower bound from
`SmoothSurfaceResidueExponent`.  The complement consists of the actual
columns whose reduction has zero affine gradient; no fictitious local
exponent is assigned to those columns.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial

set_option maxHeartbeats 1000000

local instance hypersurfaceMixedResidueExponentBound_decidableProp
    (P : Prop) : Decidable P := Classical.propDecidable P

/-- The fibers of the actual smooth-residue label partition all columns
whose reduction is smooth. -/
theorem sum_card_smoothSurfacePointResidueClass_fibers
    {ι : Type*} [Fintype ι]
    (p : ℕ) (F : MvPolynomial (Fin 3) ℤ) (y : ι → Fin 3 → ℤ) :
    (∑ c : SurfaceOccupiedSmoothResidueClass p F y,
      Fintype.card {j : SmoothSurfaceColumn p F y //
        smoothSurfacePointResidueClass p F y j = c}) =
      Fintype.card (SmoothSurfaceColumn p F y) := by
  classical
  simpa using
    (Fintype.sum_fiberwise
      (smoothSurfacePointResidueClass p F y)
      (fun _ : SmoothSurfaceColumn p F y => (1 : ℕ)))

/-- Exact good/bad column accounting for the literal affine-gradient
predicate used in the mixed determinant. -/
theorem card_smoothSurfaceColumn_eq_card_sub_bad
    {ι : Type*} [Fintype ι]
    (p : ℕ) (F : MvPolynomial (Fin 3) ℤ) (y : ι → Fin 3 → ℤ) :
    Fintype.card (SmoothSurfaceColumn p F y) =
      Fintype.card ι -
        Fintype.card {j : ι // ¬ surfaceGradientNonzeroMod p F (y j)} := by
  have h := Fintype.card_subtype_compl
    (fun j : ι => ¬ surfaceGradientNonzeroMod p F (y j))
  simpa only [not_not] using h

/-- Sharp lower bound for the exponent in the actual mixed-residue
determinant.  `M` may be any positive upper bound for the number of occupied
smooth residue classes.  The loss is expressed by the literal number of
singular-reduction columns, counted with multiplicity in the column type. -/
theorem hypersurfaceSmoothResidueExponent_lower_bound
    {ι : Type*} [Fintype ι]
    (p : ℕ) (F : MvPolynomial (Fin 3) ℤ) (y : ι → Fin 3 → ℤ)
    (M : ℕ) (hM : 0 < M)
    (hclasses : Fintype.card (SurfaceOccupiedSmoothResidueClass p F y) ≤ M) :
    (2 * Real.sqrt 2 / 3) * (Fintype.card ι : ℝ) ^ (3 / 2 : ℝ) /
          Real.sqrt (M : ℝ) -
        Real.sqrt 2 *
          (Fintype.card {j : ι //
            ¬ surfaceGradientNonzeroMod p F (y j)} : ℝ) *
          Real.sqrt (Fintype.card ι : ℝ) / Real.sqrt (M : ℝ) -
        2 * Fintype.card ι ≤
      (hypersurfaceSmoothResidueExponent p F y : ℝ) := by
  classical
  let a : Finset (SurfaceOccupiedSmoothResidueClass p F y) := Finset.univ
  let n : SurfaceOccupiedSmoothResidueClass p F y → ℕ := fun c =>
    Fintype.card {j : SmoothSurfaceColumn p F y //
      smoothSurfacePointResidueClass p F y j = c}
  let s : ℕ := Fintype.card ι
  let b : ℕ := Fintype.card {j : ι //
    ¬ surfaceGradientNonzeroMod p F (y j)}
  have hb : b ≤ s := by
    dsimp [b, s]
    exact Fintype.card_subtype_le _
  have hrows : (∑ c ∈ a, n c) = s - b := by
    simp only [a, n, s, b]
    rw [sum_card_smoothSurfacePointResidueClass_fibers p F y,
      card_smoothSurfaceColumn_eq_card_sub_bad p F y]
  have hcard : a.card ≤ M := by
    simpa only [a, Finset.card_univ] using hclasses
  have hbound := sum_smoothSurfaceJetExponent_lower_bound_discard
    a n M s b hM hcard hb hrows
  simpa only [a, n, s, b, Finset.sum_const_zero, Finset.sum_filter,
    Finset.mem_univ, if_true, hypersurfaceSmoothResidueExponent] using hbound

end
end TranslatedDepthSeven
