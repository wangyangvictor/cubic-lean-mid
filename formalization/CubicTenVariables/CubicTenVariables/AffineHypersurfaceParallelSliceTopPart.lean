import TranslatedDepthSeven.AffineChartProjectionBoundaryTopPart
import TranslatedDepthSeven.AffineTransformTopHomogeneousPart

/-!
# The common leading equation of parallel affine slices

Specializing the first coordinate of an integral polynomial at any integer
leaves the leading equation on the remaining variables equal to the
restriction of its original leading form at coordinate zero.  If that
restriction is nonzero, every parallel slice retains the exact degree.
In particular, an absolutely irreducible restricted leading form supplies
the same Salberger polynomial hypothesis for every parallel slice.

This file does not assert that a suitable slicing coordinate exists, nor
does it assume or prove a point-count estimate.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace TranslatedDepthSeven

open MvPolynomial

/-- Substitute an integer for coordinate zero and retain consecutive tail
coordinates. -/
def integralSpecializeFirstCoordinate {n : ℕ} (t : ℤ) :
    MvPolynomial (Fin (n + 1)) ℤ →ₐ[ℤ] MvPolynomial (Fin n) ℤ :=
  MvPolynomial.aeval (Fin.cases (MvPolynomial.C t) MvPolynomial.X)

/-- Evaluation on the slice is evaluation at the reconstructed source
point, with first coordinate equal to the slice parameter. -/
theorem eval_integralSpecializeFirstCoordinate
    {n : ℕ} (t : ℤ) (y : Fin n → ℤ)
    (f : MvPolynomial (Fin (n + 1)) ℤ) :
    MvPolynomial.eval y (integralSpecializeFirstCoordinate t f) =
      MvPolynomial.eval (Fin.cases t y) f := by
  let lhs : MvPolynomial (Fin (n + 1)) ℤ →+* ℤ :=
    (MvPolynomial.eval y).comp
      (integralSpecializeFirstCoordinate t).toRingHom
  let rhs : MvPolynomial (Fin (n + 1)) ℤ →+* ℤ :=
    MvPolynomial.eval (Fin.cases t y)
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [lhs, rhs, integralSpecializeFirstCoordinate]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp [lhs, rhs, integralSpecializeFirstCoordinate]
  exact RingHom.congr_fun hhom f

/-- Coefficient extension commutes with the literal integral slice. -/
theorem map_integralSpecializeFirstCoordinate
    {n : ℕ} (t : ℤ) (f : MvPolynomial (Fin (n + 1)) ℤ) :
    MvPolynomial.map (Int.castRingHom ℚ)
        (integralSpecializeFirstCoordinate t f) =
      rationalSpecializeFirstCoordinate (t : ℚ)
        (MvPolynomial.map (Int.castRingHom ℚ) f) := by
  let lhs : MvPolynomial (Fin (n + 1)) ℤ →+*
      MvPolynomial (Fin n) ℚ :=
    (MvPolynomial.map (Int.castRingHom ℚ)).comp
      (integralSpecializeFirstCoordinate t).toRingHom
  let rhs : MvPolynomial (Fin (n + 1)) ℤ →+*
      MvPolynomial (Fin n) ℚ :=
    (rationalSpecializeFirstCoordinate (t : ℚ)).toRingHom.comp
      (MvPolynomial.map (Int.castRingHom ℚ))
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [lhs, rhs, integralSpecializeFirstCoordinate,
        rationalSpecializeFirstCoordinate]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp [lhs, rhs, integralSpecializeFirstCoordinate,
          rationalSpecializeFirstCoordinate]
  exact RingHom.congr_fun hhom f

/-- Specializing one coordinate cannot increase total degree. -/
theorem rationalSpecializeFirstCoordinate_totalDegree_le_self
    {n : ℕ} (c : ℚ) (f : MvPolynomial (Fin (n + 1)) ℚ) :
    (rationalSpecializeFirstCoordinate c f).totalDegree ≤ f.totalDegree := by
  classical
  rw [← MvPolynomial.mem_restrictTotalDegree]
  have hsum : rationalSpecializeFirstCoordinate c f =
      ∑ k ∈ Finset.range (f.totalDegree + 1),
        rationalSpecializeFirstCoordinate c (homogeneousComponent k f) := by
    rw [← map_sum, f.sum_homogeneousComponent]
  rw [hsum]
  apply Submodule.sum_mem
  intro k hk
  rw [MvPolynomial.mem_restrictTotalDegree]
  exact (rationalSpecializeFirstCoordinate_totalDegree_le c
    (MvPolynomial.homogeneousComponent_isHomogeneous k f)).trans
      (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

/-- At the highest possible degree, specialization discards precisely the
monomials containing the specialized coordinate. -/
theorem homogeneousComponent_rationalSpecializeFirstCoordinate_of_totalDegree_le
    {n d : ℕ} (c : ℚ) (f : MvPolynomial (Fin (n + 1)) ℚ)
    (hdegree : f.totalDegree ≤ d) :
    homogeneousComponent d (rationalSpecializeFirstCoordinate c f) =
      rationalSpecializeFirstCoordinate 0 (homogeneousComponent d f) := by
  classical
  conv_lhs => rw [← f.sum_homogeneousComponent, map_sum, map_sum]
  rw [Finset.sum_eq_single d]
  · exact homogeneousComponent_rationalSpecializeFirstCoordinate_of_isHomogeneous
      c (MvPolynomial.homogeneousComponent_isHomogeneous d f)
  · intro k hk hkd
    apply MvPolynomial.homogeneousComponent_eq_zero
    have hklt : k < d := by
      have hkle := (Nat.le_of_lt_succ (Finset.mem_range.mp hk)).trans hdegree
      omega
    exact (rationalSpecializeFirstCoordinate_totalDegree_le c
      (MvPolynomial.homogeneousComponent_isHomogeneous k f)).trans_lt hklt
  · intro hdnot
    have hlt : f.totalDegree < d := by
      simp only [Finset.mem_range] at hdnot
      omega
    rw [MvPolynomial.homogeneousComponent_eq_zero d f hlt]
    simp

/-- Every parallel affine slice has the same exact leading form, provided
the leading restriction is nonzero. -/
theorem isTopHomogeneousPart_integralSpecializeFirstCoordinate
    {n d : ℕ} (t : ℤ)
    {f : MvPolynomial (Fin (n + 1)) ℤ}
    {h : MvPolynomial (Fin (n + 1)) ℚ}
    (htop : Published.IsTopHomogeneousPart f h d)
    (hrestricted : rationalSpecializeFirstCoordinate 0 h ≠ 0) :
    Published.IsTopHomogeneousPart
      (integralSpecializeFirstCoordinate t f)
      (rationalSpecializeFirstCoordinate 0 h) d := by
  have hdegree : f.totalDegree = d := totalDegree_eq_of_isTopHomogeneousPart htop
  have hmapdegree : (MvPolynomial.map (Int.castRingHom ℚ) f).totalDegree ≤ d := by
    exact (Finset.sup_mono (MvPolynomial.support_map_subset
      (Int.castRingHom ℚ) f)).trans hdegree.le
  have hsliceDegree :
      (rationalSpecializeFirstCoordinate (t : ℚ)
        (MvPolynomial.map (Int.castRingHom ℚ) f)).totalDegree ≤ d :=
    (rationalSpecializeFirstCoordinate_totalDegree_le_self _ _).trans hmapdegree
  refine ⟨?_, hrestricted, ?_⟩
  · rw [map_homogeneousComponent_boundary, map_integralSpecializeFirstCoordinate,
      homogeneousComponent_rationalSpecializeFirstCoordinate_of_totalDegree_le
        _ _ hmapdegree]
    rw [htop.1, map_homogeneousComponent_boundary]
  · intro k hdk
    apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
    rw [map_zero, map_homogeneousComponent_boundary,
      map_integralSpecializeFirstCoordinate]
    exact MvPolynomial.homogeneousComponent_eq_zero _ _
      (hsliceDegree.trans_lt hdk)

/-- Absolute irreducibility is a property of the one common restricted
leading form and therefore supplies the hypothesis on every slice. -/
theorem isTopHomogeneousPart_and_isAbsolutelyIrreducible_integralSpecializeFirstCoordinate
    {n d : ℕ} (t : ℤ)
    {f : MvPolynomial (Fin (n + 1)) ℤ}
    {h : MvPolynomial (Fin (n + 1)) ℚ}
    (htop : Published.IsTopHomogeneousPart f h d)
    (hirr : Published.IsAbsolutelyIrreducible
      (rationalSpecializeFirstCoordinate 0 h)) :
    Published.IsTopHomogeneousPart
        (integralSpecializeFirstCoordinate t f)
        (rationalSpecializeFirstCoordinate 0 h) d ∧
      Published.IsAbsolutelyIrreducible
        (rationalSpecializeFirstCoordinate 0 h) :=
  ⟨isTopHomogeneousPart_integralSpecializeFirstCoordinate t htop hirr.ne_zero,
    hirr⟩

end TranslatedDepthSeven
