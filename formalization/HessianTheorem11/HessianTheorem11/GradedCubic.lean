import HessianTheorem11.QuadraticCombinationGeometry
import HessianTheorem11.SingularNormalEquations

/-! Differentiation of the literal graded singular cubic, connecting its
polynomial Hessian to the proved Schur matrix calculation. -/
noncomputable section
namespace HessianTheorem11.GradedCubic
open MvPolynomial Matrix SingularNormalEquations
variable {K : Type*} [Field K] {s r : ℕ}

abbrev Index (r s : ℕ) := Fin r ⊕ (Fin s ⊕ Unit)
def radial : Index r s := Sum.inr (Sum.inr ())
def tangent (i : Fin s) : Index r s := Sum.inr (Sum.inl i)
def embed (p : MvPolynomial (Fin s) K) : MvPolynomial (Index r s) K := rename tangent p

def cubic (q : MvPolynomial (Fin r) K) (p : Fin r → MvPolynomial (Fin s) K) :
    MvPolynomial (Index r s) K :=
  X radial * rename Sum.inl q + ∑ i, X (Sum.inl i) * embed (p i)

def point (Xc : K) (a : Fin s → K) (d : Fin r → K) : Index r s → K :=
  Sum.elim d (Sum.elim a (fun _ => Xc))

@[simp] theorem eval_embed (p : MvPolynomial (Fin s) K)
    (Xc : K) (a : Fin s → K) (d : Fin r → K) :
    eval (point Xc a d) (embed p : MvPolynomial (Index r s) K) = eval a p := by
  simp [embed, eval_rename, point, tangent, Function.comp_def]

@[simp] theorem eval_cubic (q : MvPolynomial (Fin r) K) (p : Fin r → MvPolynomial (Fin s) K)
    (Xc : K) (a : Fin s → K) (d : Fin r → K) :
    eval (point Xc a d) (cubic q p) = Xc * eval d q + dotProduct d (fun i => eval a (p i)) := by
  simp [cubic, eval_rename, point, radial, embed, tangent, Function.comp_def, dotProduct]

@[simp] theorem pderiv_normal_embed (p : MvPolynomial (Fin s) K) (i : Fin r) :
    pderiv (Sum.inl i) (embed p : MvPolynomial (Index r s) K) = 0 :=
  LocalCubicNormalForm.pderiv_rename_outside _ _ p (by intro j; simp [tangent])

@[simp] theorem pderiv_tangent_embed (p : MvPolynomial (Fin s) K) (i : Fin s) :
    pderiv (Sum.inr (Sum.inl i)) (embed p : MvPolynomial (Index r s) K) = embed (pderiv i p) :=
  pderiv_rename (Sum.inr_injective.comp Sum.inl_injective) i p

@[simp] theorem pderiv_radial_embed (p : MvPolynomial (Fin s) K) :
    pderiv (Sum.inr (Sum.inr ())) (embed p : MvPolynomial (Index r s) K) = 0 :=
  LocalCubicNormalForm.pderiv_rename_outside _ _ p (by intro j; simp [tangent, radial])

@[simp] theorem pderiv_normal_rename (q : MvPolynomial (Fin r) K) (i : Fin r) :
    pderiv (Sum.inl i) (rename Sum.inl q : MvPolynomial (Index r s) K) =
      rename Sum.inl (pderiv i q) := pderiv_rename Sum.inl_injective i q

@[simp] theorem pderiv_tangent_rename (q : MvPolynomial (Fin r) K) (i : Fin s) :
    pderiv (Sum.inr (Sum.inl i)) (rename Sum.inl q : MvPolynomial (Index r s) K) = 0 :=
  LocalCubicNormalForm.pderiv_rename_outside _ _ q (by intro j; simp [tangent])

@[simp] theorem pderiv_radial_rename (q : MvPolynomial (Fin r) K) :
    pderiv (Sum.inr (Sum.inr ())) (rename Sum.inl q : MvPolynomial (Index r s) K) = 0 :=
  LocalCubicNormalForm.pderiv_rename_outside _ _ q (by intro j; simp [radial])

theorem normal_partial (q : MvPolynomial (Fin r) K) (p : Fin r → MvPolynomial (Fin s) K)
    (i : Fin r) : pderiv (Sum.inl i) (cubic q p) =
      X radial * rename Sum.inl (pderiv i q) + embed (p i) := by
  classical
  simp [cubic, pderiv_mul, pderiv_X, Pi.single_apply, radial, mul_ite,
    ite_mul, Finset.sum_ite_eq', eq_comm]

theorem tangent_partial (q : MvPolynomial (Fin r) K) (p : Fin r → MvPolynomial (Fin s) K)
    (i : Fin s) : pderiv (tangent i) (cubic q p) =
      ∑ j, X (Sum.inl j) * embed (pderiv i (p j)) := by
  classical
  simp [cubic, pderiv_mul, pderiv_X, Pi.single_apply, radial, tangent]

theorem radial_partial (q : MvPolynomial (Fin r) K) (p : Fin r → MvPolynomial (Fin s) K) :
    pderiv radial (cubic q p) = rename Sum.inl q := by
  classical
  simp [cubic, pderiv_mul, pderiv_X, Pi.single_apply, radial]

theorem hessian_eq_full
    (q : MvPolynomial (Fin r) K) (hq : q.IsHomogeneous 2)
    (p : Fin r → MvPolynomial (Fin s) K)
    (Xc : K) (a : Fin s → K) (d : Fin r → K) :
    (SplitPolynomial.fullHessian (cubic q p)).map (eval (point Xc a d)) =
      GradedSchurMatrix.full (Xc • quadraticHessian q) (normalCombination p a d)
        (TangentHessianRank.polynomialJacobian p a) ((quadraticHessian q).mulVec d) := by
  classical
  have he (i j : Fin r) : pderiv j (pderiv i q) = C (quadraticHessian q i j) :=
    homogeneous_zero_eq_constant hq.pderiv.pderiv
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp [SplitPolynomial.fullHessian, normal_partial, pderiv_mul,
        pderiv_X, Pi.single_apply, radial, he, point, GradedSchurMatrix.full]
    | inr j =>
      cases j with
      | inl j =>
        change eval (point Xc a d) (pderiv (tangent j) (pderiv (Sum.inl i) (cubic q p))) = _
        simp [normal_partial, pderiv_mul, pderiv_X, Pi.single_apply,
          radial, tangent, GradedSchurMatrix.full, GradedSchurMatrix.cross,
          TangentHessianRank.polynomialJacobian]
      | inr j =>
        cases j
        change eval (point Xc a d) (pderiv radial (pderiv (Sum.inl i) (cubic q p))) = _
        simp [normal_partial, pderiv_mul, pderiv_X, Pi.single_apply,
          eval_rename, point, radial, Function.comp_def, GradedSchurMatrix.full,
          GradedSchurMatrix.cross, eval_quadratic_partial q hq]
  | inr i =>
    cases i with
    | inl i =>
      change eval (point Xc a d) (pderiv j (pderiv (tangent i) (cubic q p))) = _
      rw [tangent_partial]
      cases j with
      | inl j =>
        simp [pderiv_mul, pderiv_X, Pi.single_apply, GradedSchurMatrix.full,
          GradedSchurMatrix.cross, TangentHessianRank.polynomialJacobian]
      | inr j =>
        cases j with
        | inl j =>
          change eval (point Xc a d) (pderiv (Sum.inr (Sum.inl j)) _) = _
          simp only [map_sum, pderiv_mul, pderiv_tangent_embed]
          simp [pderiv_mul, pderiv_X, Pi.single_apply, GradedSchurMatrix.full,
            GradedSchurMatrix.rest, normalCombination, tangent, point, embed, eval_rename, Function.comp_def]
        | inr j =>
          cases j
          change eval (point Xc a d) (pderiv radial _) = _
          simp [pderiv_mul, pderiv_X, Pi.single_apply, radial,
            GradedSchurMatrix.full, GradedSchurMatrix.rest]
    | inr i =>
      cases i
      change eval (point Xc a d) (pderiv j (pderiv radial (cubic q p))) = _
      rw [radial_partial]
      cases j with
      | inl j =>
        simp [eval_rename, point, radial, Function.comp_def, GradedSchurMatrix.full,
          GradedSchurMatrix.cross, eval_quadratic_partial q hq]
      | inr j =>
        cases j with
        | inl j =>
          change eval (point Xc a d) (pderiv (tangent j) _) = _
          simp [tangent, radial, GradedSchurMatrix.full, GradedSchurMatrix.rest]
        | inr j =>
          cases j
          change eval (point Xc a d) (pderiv radial _) = _
          simp [tangent, radial, GradedSchurMatrix.full, GradedSchurMatrix.rest]

theorem quadraticHessian_symm (q : MvPolynomial (Fin r) K) : (quadraticHessian q).IsSymm := by
  ext i j
  exact congrArg (coeff 0) (partials_commute q i j)

end HessianTheorem11.GradedCubic
