import HessianTheorem11.CubicWeights

/-! A nonzero positive-degree homogeneous form has positive ambient
dimension. This discharges the zero-variable edge case in the universal
rational boundary interface. -/
namespace HessianTheorem11.UnconditionalBoundary
open MvPolynomial

theorem positive_dimension {K : Type*} [CommRing K] {n d : ℕ}
    (F : MvPolynomial (Fin n) K) (hd : 0 < d) (hF : F.IsHomogeneous d)
    (hne : F ≠ 0) : 0 < n := by
  cases n with
  | zero =>
    obtain ⟨e,he⟩ := support_nonempty.mpr hne
    have hc := hF (mem_support_iff.mp he)
    have he0 : e = 0 := Subsingleton.elim _ _
    simp only [he0,map_zero] at hc
    omega
  | succ n => omega

end HessianTheorem11.UnconditionalBoundary
