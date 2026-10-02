import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! Lift polynomial equations through a surjective coefficient map while
preserving their exact monomial support. This is used for residue equations
of the invariant target over a valuation ring. -/
noncomputable section
namespace HessianTheorem11.UnconditionalPolynomialLift
open MvPolynomial

/-- Coefficients can be lifted without adding or deleting any monomial. -/
theorem exists_lift_same_support {R E σ : Type*} [CommRing R] [CommRing E]
    (f : R →+* E) (hf : Function.Surjective f) (q : MvPolynomial σ E) :
    ∃ p : MvPolynomial σ R, map f p = q ∧ p.support = q.support := by
  classical
  let s : E → R := fun c => if c = 0 then 0 else Classical.choose (hf c)
  have hs0 : s 0 = 0 := by simp [s]
  have hs (c : E) : f (s c) = c := by
    by_cases hc : c = 0
    · simp [s,hc]
    · simpa [s,hc] using Classical.choose_spec (hf c)
  let p : MvPolynomial σ R := Finsupp.mapRange s hs0 q
  have hp : map f p = q := by
    ext e
    simp only [coeff_map,p,coeff_mapRange,hs]
  refine ⟨p,hp,?_⟩
  ext e
  simp only [mem_support_iff,p,coeff_mapRange]
  constructor
  · intro h hc
    exact h (hc ▸ hs0)
  · intro h hs'
    apply h
    rw [← hs (coeff e q),hs',map_zero]

end HessianTheorem11.UnconditionalPolynomialLift
