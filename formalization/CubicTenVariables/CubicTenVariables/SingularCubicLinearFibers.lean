import CubicTenVariables.CubicSingularQuotient
import Mathlib.Data.Fin.Tuple.Basic

/-! Exact linear fibers obtained from a rational singular point of a cubic.
The coordinate equivalence is constructed from one nonzero coordinate of the
point. No existence of a singular point, geometric classification, or bound
for the intersection of the quadratic and cubic is asserted here. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.SingularCubicLinearFibers
open MvPolynomial HessianTheorem11 CubicTaylorExpansion CubicSingularQuotient
open scoped BigOperators

/-- Set the selected coordinate to zero, retaining an actual polynomial. -/
def zeroSection {R : Type*} [CommRing R] {n : ℕ} (i : Fin (n+1))
    (F : MvPolynomial (Fin (n+1)) R) : MvPolynomial (Fin n) R :=
  aeval (i.insertNth 0 (X : Fin n → MvPolynomial (Fin n) R)) F

theorem eval_section {R : Type*} [CommRing R] {n : ℕ} (i : Fin (n+1))
    (F : MvPolynomial (Fin (n+1)) R) (y : Fin n → R) :
    eval y (zeroSection i F)=eval (i.insertNth 0 y) F := by
  change aeval y (aeval _ F)=aeval (i.insertNth 0 y) F
  rw [MvPolynomial.comp_aeval_apply]
  have he : (fun j => aeval y (@Fin.insertNth n (fun _ => MvPolynomial (Fin n) R) i 0 X j))=
      i.insertNth 0 y := by
    funext j
    induction j using i.succAboveCases <;> simp
  rw [he]

theorem homogeneous_section {R : Type*} [CommRing R] {n d : ℕ} (i : Fin (n+1))
    (F : MvPolynomial (Fin (n+1)) R) (hF : F.IsHomogeneous d) :
    (zeroSection i F).IsHomogeneous d := by
  unfold zeroSection
  have h : ∀ j : Fin (n+1),
      (@Fin.insertNth n (fun _ => MvPolynomial (Fin n) R) i 0 X j).IsHomogeneous 1 := by
    intro j
    induction j using i.succAboveCases
    · simp only [Fin.insertNth_apply_same]
      exact isHomogeneous_zero _ _ _
    · simp only [Fin.insertNth_apply_succAbove]
      exact isHomogeneous_X (R := R) _
  simpa only [one_mul] using hF.aeval _ h

/-- The scalar along a singular direction occurs only linearly. This
identity is division-free and holds in every residue characteristic. -/
theorem eval_singular_line {R : Type*} [CommRing R] {n : ℕ}
    (F : MvPolynomial (Fin n) R) (hF : F.IsHomogeneous 3)
    (z : Fin n → R) (hzero : eval z F=0) (hsing : gradient F z=0)
    (x : Fin n → R) (a : R) :
    eval (x+a • z) F=a*eval x (quadraticPolynomial F z)+eval x F := by
  rw [eval_cubic_add_smul F hF,eval_quadraticPolynomial]
  simp only [quadraticAt,directional,hsing,dotProduct_zero,hzero,mul_zero,add_zero]
  ring

/-- An explicit coordinate decomposition into the hyperplane x_i=0 and
the chosen nonzero direction; it works over finite fields as well. -/
def chartEquiv {K : Type*} [Field K] {n : ℕ}
    (z : Fin (n+1) → K) (i : Fin (n+1)) (hi : z i ≠ 0) :
    (Fin (n+1) → K) ≃ ((Fin n → K) × K) where
  toFun x := (i.removeNth (x-(x i/z i) • z),x i/z i)
  invFun u := i.insertNth 0 u.1+u.2 • z
  left_inv x := by
    funext j
    induction j using i.succAboveCases
    · simp [div_mul_cancel₀ _ hi]
    · simp only [Fin.insertNth_apply_succAbove,Pi.add_apply,Pi.smul_apply,
        smul_eq_mul,Fin.removeNth_apply,Pi.sub_apply]
      ring
  right_inv u := by
    rcases u with ⟨y,a⟩
    apply Prod.ext
    · funext j
      simp only [Fin.removeNth_apply,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,
        smul_eq_mul,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove,zero_add]
      rw [mul_div_cancel_right₀ _ hi]
      ring
    · simp [hi]

@[simp] theorem chartEquiv_symm_apply {K : Type*} [Field K] {n : ℕ}
    (z : Fin (n+1) → K) (i : Fin (n+1)) (hi : z i ≠ 0)
    (u : (Fin n → K) × K) :
    (chartEquiv z i hi).symm u=i.insertNth 0 u.1+u.2 • z := rfl

theorem eval_chart {K : Type*} [Field K] {n : ℕ}
    (F : MvPolynomial (Fin (n+1)) K) (hF : F.IsHomogeneous 3)
    (z : Fin (n+1) → K) (hzero : eval z F=0) (hsing : gradient F z=0)
    (i : Fin (n+1)) (hi : z i ≠ 0) (u : (Fin n → K) × K) :
    eval ((chartEquiv z i hi).symm u) F=
      u.2*eval u.1 (zeroSection i (quadraticPolynomial F z))+eval u.1 (zeroSection i F) := by
  rw [chartEquiv_symm_apply,eval_singular_line F hF z hzero hsing,
    eval_section,eval_section]

/-- A literal equivalence of the actual zero sets, not an assumed count. -/
def zeroEquiv {K : Type*} [Field K] {n : ℕ}
    (F : MvPolynomial (Fin (n+1)) K) (hF : F.IsHomogeneous 3)
    (z : Fin (n+1) → K) (hzero : eval z F=0) (hsing : gradient F z=0)
    (i : Fin (n+1)) (hi : z i ≠ 0) :
    {x : Fin (n+1) → K // eval x F=0} ≃
      {u : (Fin n → K) × K //
        u.2*eval u.1 (zeroSection i (quadraticPolynomial F z))+eval u.1 (zeroSection i F)=0} :=
  (chartEquiv z i hi).subtypeEquiv (fun x => by
    have h := eval_chart F hF z hzero hsing i hi (chartEquiv z i hi x)
    rw [Equiv.symm_apply_apply] at h
    exact h ▸ Iff.rfl)

/-- A supplied nonzero singular point yields actual homogeneous quadratic
and cubic equations and an exact affine root-count identity. No field-size,
characteristic, point-count, or coordinate-choice premise is added. -/
theorem exists_equations {K : Type*} [Field K] {n : ℕ}
    (F : MvPolynomial (Fin (n+1)) K) (hF : F.IsHomogeneous 3)
    (z : Fin (n+1) → K) (hz : z ≠ 0)
    (hzero : eval z F=0) (hsing : gradient F z=0) :
    ∃ Q C : MvPolynomial (Fin n) K, Q.IsHomogeneous 2 ∧ C.IsHomogeneous 3 ∧
      Nat.card {x : Fin (n+1) → K // eval x F=0}=
        Nat.card {u : (Fin n → K) × K // u.2*eval u.1 Q+eval u.1 C=0} := by
  obtain ⟨i,hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra! h
    exact hz (funext h)
  refine ⟨zeroSection i (quadraticPolynomial F z),zeroSection i F,
    homogeneous_section i _ (homogeneous_quadraticPolynomial F hF z),
    homogeneous_section i F hF,?_⟩
  exact Nat.card_congr (zeroEquiv F hF z hzero hsing i hi)

end CubicTenVariables.SingularCubicLinearFibers
