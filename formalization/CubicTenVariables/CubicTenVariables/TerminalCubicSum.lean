import CubicTenVariables.CubicTaylorExpansion
import CubicTenVariables.QuadraticGaussBound
import Mathlib.Data.Finset.Max

/-!
# The literal terminal cubic sum and its base-point translation invariance

The phase is `ell·z + alpha*Q_y(z) + alpha*A*F(z)`, where the integral
quadratic term is the actual `Q_y(z)=y·∇F(z)`. Its finite maximum is over
all residue units `alpha` and all linear terms `ell`. Division-free Taylor
expansion proves the phase identity, and finite translation proves the
norm and maximum identities. No invertibility of `A`, analytic estimate,
characteristic restriction, or ring embedding between moduli is used.
-/

noncomputable section
namespace CubicTenVariables.TerminalCubicSum

open MvPolynomial HessianTheorem11 CubicTaylorExpansion
open scoped BigOperators

section Algebra

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The literal integral terminal phase. -/
def terminalPhase (F : MvPolynomial (Fin n) R) (A : R)
    (ell : Fin n → R) (alpha : R) (y z : Fin n → R) : R :=
  dotProduct ell z + alpha * quadraticAt F y z + alpha * A * eval z F

/-- The exact sign of the linear-term shift in the manuscript. -/
def shiftedLinear (F : MvPolynomial (Fin n) R) (A alpha : R)
    (y h ell : Fin n → R) : Fin n → R :=
  ell - alpha • (hessian F y).mulVec h - (alpha * A) • gradient F h

/-- The quadratic term is linear in its base point, including characteristic two. -/
theorem quadraticAt_add_smul_left (F : MvPolynomial (Fin n) R)
    (y h z : Fin n → R) (A : R) :
    quadraticAt F (y + A • h) z = quadraticAt F y z + A * quadraticAt F h z := by
  simp [quadraticAt, directional, add_dotProduct, smul_dotProduct, smul_eq_mul]

/-- Division-free translation of the actual phase, with its constant term retained.
The coefficient shift has the two minus signs in the source formula. -/
theorem terminalPhase_translate (F : MvPolynomial (Fin n) R)
    (hF : F.IsHomogeneous 3) (A alpha : R) (y h ell z : Fin n → R) :
    terminalPhase F A ell alpha (y + A • h) z +
        terminalPhase F A (shiftedLinear F A alpha y h ell) alpha y h =
      terminalPhase F A (shiftedLinear F A alpha y h ell) alpha y (z + h) := by
  have he : eval (z + h) F = eval z F + directional F z h +
      quadraticAt F z h + eval h F := by
    simpa using eval_cubic_add_smul F hF z h 1
  simp only [terminalPhase, quadraticAt_add_smul_left,
    quadraticAt_add F hF, he, shiftedLinear, dotProduct_add, sub_dotProduct,
    smul_dotProduct, smul_eq_mul]
  rw [dotProduct_comm ((hessian F y).mulVec h) z,
    dotProduct_comm (gradient F h) z]
  unfold quadraticAt directional
  ring

end Algebra

variable (T : ℕ) [NeZero T] {n : ℕ}

/-- The actual finite terminal cubic sum over every vector modulo `T`. -/
def terminalSum (F : MvPolynomial (Fin n) (ZMod T)) (A : ZMod T)
    (ell : Fin n → ZMod T) (alpha : ZMod T) (y : Fin n → ZMod T) : ℂ :=
  ∑ z : Fin n → ZMod T, ZMod.stdAddChar (terminalPhase F A ell alpha y z)

/-- The actual finite maximum over all units and all linear phases.
The indexing type contains `(1,0)`, including when `T=1`. -/
def terminalMax (F : MvPolynomial (Fin n) (ZMod T)) (A : ZMod T)
    (y : Fin n → ZMod T) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun p : (ZMod T)ˣ × (Fin n → ZMod T) => ‖terminalSum T F A p.2 p.1 y‖)

theorem norm_terminalSum_le_terminalMax (F : MvPolynomial (Fin n) (ZMod T))
    (A : ZMod T) (ell : Fin n → ZMod T) (alpha : (ZMod T)ˣ)
    (y : Fin n → ZMod T) :
    ‖terminalSum T F A ell alpha y‖ ≤ terminalMax T F A y := by
  exact Finset.le_sup' (fun p : (ZMod T)ˣ × (Fin n → ZMod T) =>
    ‖terminalSum T F A p.2 p.1 y‖) (Finset.mem_univ (alpha, ell))

/-- The finite maximum is attained by an actual unit and linear term. -/
theorem terminalMax_attained (F : MvPolynomial (Fin n) (ZMod T))
    (A : ZMod T) (y : Fin n → ZMod T) :
    ∃ alpha : (ZMod T)ˣ, ∃ ell : Fin n → ZMod T,
      terminalMax T F A y = ‖terminalSum T F A ell alpha y‖ := by
  obtain ⟨⟨alpha, ell⟩, _, he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun p : (ZMod T)ˣ × (Fin n → ZMod T) => ‖terminalSum T F A p.2 p.1 y‖)
  exact ⟨alpha, ell, he⟩

theorem terminalMax_nonneg (F : MvPolynomial (Fin n) (ZMod T))
    (A : ZMod T) (y : Fin n → ZMod T) : 0 ≤ terminalMax T F A y :=
  (norm_nonneg _).trans (norm_terminalSum_le_terminalMax T F A 0 1 y)

/-- Exact sum identity with the constant character factor. This is stronger
than norm invariance and displays why translation only changes a phase. -/
theorem terminalSum_translate_mul (F : MvPolynomial (Fin n) (ZMod T))
    (hF : F.IsHomogeneous 3) (A alpha : ZMod T)
    (y h ell : Fin n → ZMod T) :
    terminalSum T F A ell alpha (y + A • h) *
        ZMod.stdAddChar (terminalPhase F A (shiftedLinear F A alpha y h ell) alpha y h) =
      terminalSum T F A (shiftedLinear F A alpha y h ell) alpha y := by
  classical
  rw [terminalSum, Finset.sum_mul]
  calc
    _ = ∑ z : Fin n → ZMod T,
        ZMod.stdAddChar
          (terminalPhase F A (shiftedLinear F A alpha y h ell) alpha y (z + h)) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [← AddChar.map_add_eq_mul, terminalPhase_translate F hF A alpha y h ell z]
    _ = terminalSum T F A (shiftedLinear F A alpha y h ell) alpha y :=
      Equiv.sum_comp (Equiv.addRight h)
        (fun z => ZMod.stdAddChar
          (terminalPhase F A (shiftedLinear F A alpha y h ell) alpha y z))

/-- Source norm identity, valid for every scalar `alpha` and not only units. -/
theorem norm_terminalSum_translate (F : MvPolynomial (Fin n) (ZMod T))
    (hF : F.IsHomogeneous 3) (A alpha : ZMod T)
    (y h ell : Fin n → ZMod T) :
    ‖terminalSum T F A ell alpha (y + A • h)‖ =
      ‖terminalSum T F A (shiftedLinear F A alpha y h ell) alpha y‖ := by
  have he := congrArg norm (terminalSum_translate_mul T F hF A alpha y h ell)
  simpa only [norm_mul, QuadraticGaussBound.norm_stdAddChar, mul_one] using he

private theorem terminalMax_translate_le (F : MvPolynomial (Fin n) (ZMod T))
    (hF : F.IsHomogeneous 3) (A : ZMod T) (y h : Fin n → ZMod T) :
    terminalMax T F A (y + A • h) ≤ terminalMax T F A y := by
  apply Finset.sup'_le
  rintro ⟨alpha, ell⟩ _
  rw [norm_terminalSum_translate T F hF]
  exact norm_terminalSum_le_terminalMax T F A _ alpha y

/-- The manuscript's `max-G-A-invariant` for the actual finite maximum. -/
theorem terminalMax_add_smul (F : MvPolynomial (Fin n) (ZMod T))
    (hF : F.IsHomogeneous 3) (A : ZMod T) (y h : Fin n → ZMod T) :
    terminalMax T F A (y + A • h) = terminalMax T F A y := by
  apply le_antisymm (terminalMax_translate_le T F hF A y h)
  have he := terminalMax_translate_le T F hF A (y + A • h) (-h)
  simpa only [smul_neg, add_neg_cancel_right] using he

end CubicTenVariables.TerminalCubicSum
