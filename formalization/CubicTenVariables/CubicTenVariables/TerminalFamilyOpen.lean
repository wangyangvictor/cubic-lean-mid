import CubicTenVariables.TerminalFamilyBound
import CubicTenVariables.FiniteDenseOpen
import HessianTheorem11.ReducedDominantOpen

/-! The dense source-open required by the nonsingular-family contact proof
is constructed from actual nonvanishing, rather than supplied as an input. -/

noncomputable section
namespace CubicTenVariables.TerminalFamilyOpen
open MvPolynomial HessianTheorem11
open TerminalSectionIncidence TerminalFiberCoordinates

/-- A dominating family over a positive-dimensional base has a point with
nonzero normal. This conclusion concerns the literal normal projection. -/
theorem exists_nonzero_normal {n z : ℕ} (Y : Set (GeometricPoint (n+n)))
    (Z : Set (GeometricPoint n))
    (hdom : geometricClosure (polynomialMap (normalProjection n) '' Y) = Z)
    (hdim : affineDimension Z = (z : Dimension)) (hz : 0 < z) :
    ∃ y ∈ Y, polynomialMap (normalProjection n) y ≠ 0 := by
  by_contra hn
  push_neg at hn
  have him : polynomialMap (normalProjection n) '' Y ⊆ ({0} : Set (GeometricPoint n)) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hn y hy
  have hc : Z ⊆ ({0} : Set (GeometricPoint n)) := by
    rw [← hdom]
    exact geometricClosure_subset_closed him (by
      exact RationalConeClosure.origin_closed)
  have hd := affineDimension_mono hc
  rw [hdim, affineDimension_origin] at hd
  have he : z ≤ 0 := by exact_mod_cast hd
  omega

/-- Nonzero normal and nonzero ambient gradient meet on an actual dense
relative source-open, because the source is irreducible. -/
theorem exists_nonsingular_normal_open {n : ℕ} (F : GeometricPolynomial n)
    (Y : Set (GeometricPoint (n+n))) (hY : AlgebraicallyClosedSet Y)
    (hiY : GeometricallyIrreducible Y)
    (hnormal : ∃ y ∈ Y, polynomialMap (normalProjection n) y ≠ 0)
    (hgradient : ∃ y ∈ Y, gradient F (polynomialMap (pointProjection n) y) ≠ 0) :
    ∃ W, RelativelyOpenSet Y W ∧ geometricClosure W = Y ∧ W.Nonempty ∧
      (∀ y ∈ W, polynomialMap (normalProjection n) y ≠ 0) ∧
      (∀ y ∈ W, gradient F (polynomialMap (pointProjection n) y) ≠ 0) := by
  let N := polynomialMap (normalProjection n) ⁻¹' ({0} : Set (GeometricPoint n))
  let S := polynomialMap (pointProjection n) ⁻¹' BibleHyperplanes.singularCone F
  have hN : AlgebraicallyClosedSet N :=
    ReducedDominantOpen.closed_preimage _ (RationalConeClosure.origin_closed)
  have hS : AlgebraicallyClosedSet S :=
    ReducedDominantOpen.closed_preimage _ (BibleHyperplanes.singularCone_closed F)
  have hON : RelativelyOpenSet Y (Y \ N) := ⟨N, hN, rfl⟩
  have hOS : RelativelyOpenSet Y (Y \ S) := ⟨S, hS, rfl⟩
  have hnN : (Y \ N).Nonempty := by
    obtain ⟨y, hy, hny⟩ := hnormal
    exact ⟨y, hy, hny⟩
  have hnS : (Y \ S).Nonempty := by
    obtain ⟨y, hy, hsy⟩ := hgradient
    exact ⟨y, hy, hsy⟩
  have hopen := hON.inter hOS
  have hn := ReducedGenericImageTangent.dense_inter_open_nonempty
    (hON.dense_of_nonempty hY hiY hnN) hOS hnS
  exact ⟨(Y \ N) ∩ (Y \ S), hopen, hopen.dense_of_nonempty hY hiY hn, hn,
    fun _ hy => hy.1.2, fun _ hy => hy.2.2⟩

end CubicTenVariables.TerminalFamilyOpen
