import HessianTheorem11.SingularRadialNormalForm

/-! Exact singular equations of the constructed radial equality form.
The inverse-pairing quadratic relation is derived from the actual partials,
not assumed as part of a normal-form certificate. -/
noncomputable section
namespace HessianTheorem11.SingularNormalEquations
open MvPolynomial Module SingularRadialNormalForm
open scoped BigOperators

variable {K : Type*} [Field K]

/-- Actual constant Hessian of a homogeneous quadratic, in arbitrary
finitely many normal coordinates. -/
def quadraticHessian {δ : Type*} (q : MvPolynomial δ K) : Matrix δ δ K :=
  fun i j => coeff 0 (pderiv j (pderiv i q))

section Quadratic
variable {δ : Type*} [Fintype δ]

theorem quadratic_first_partial (q : MvPolynomial δ K) (hq : q.IsHomogeneous 2) (i : δ) :
    pderiv i q = ∑ j, X j * C (quadraticHessian q i j) := by
  have h := (show (pderiv i q).IsHomogeneous 1 from hq.pderiv).sum_X_mul_pderiv
  have he (j : δ) : pderiv j (pderiv i q) = C (quadraticHessian q i j) :=
    LocalCubicNormalForm.homogeneous_zero_eq_constant _ hq.pderiv.pderiv
  simpa only [one_nsmul, he] using h.symm

theorem quadratic_eval_identity (q : MvPolynomial δ K) (hq : q.IsHomogeneous 2) (d : δ → K) :
    dotProduct d ((quadraticHessian q).mulVec d) = 2 * eval d q := by
  have h := congrArg (eval d) hq.sum_X_mul_pderiv
  simp only [map_sum, map_mul, eval_X, quadratic_first_partial q hq, eval_C] at h
  simpa [Matrix.mulVec, dotProduct, nsmul_eq_mul, mul_comm] using h

theorem eval_quadratic_partial (q : MvPolynomial δ K) (hq : q.IsHomogeneous 2)
    (d : δ → K) (i : δ) : eval d (pderiv i q) = (quadraticHessian q).mulVec d i := by
  rw [quadratic_first_partial q hq]
  simp [Matrix.mulVec, dotProduct, mul_comm]

variable [CharZero K]

theorem eval_quadratic_smul (q : MvPolynomial δ K) (hq : q.IsHomogeneous 2)
    (c : K) (d : δ → K) : eval (c • d) q = c^2 * eval d q := by
  have h := quadratic_eval_identity q hq (c • d)
  have hd := quadratic_eval_identity q hq d
  have he : dotProduct (c • d) ((quadraticHessian q).mulVec (c • d)) =
      c^2 * dotProduct d ((quadraticHessian q).mulVec d) := by
    rw [Matrix.mulVec_smul]
    simp [dotProduct, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_assoc, mul_left_comm, pow_two]
  rw [he, hd] at h
  linear_combination (1/2 : K) * h.symm

/-- Solving the exact normal derivative equations yields the quadratic
normal relation. No division by the radial coordinate is needed. -/
theorem inverse_pairing_relation [DecidableEq δ]
    (q : MvPolynomial δ K) (hq : q.IsHomogeneous 2)
    (hdet : (quadraticHessian q).det ≠ 0) (Xc : K) (d p : δ → K)
    (hqzero : eval d q = 0)
    (hequation : Xc • (quadraticHessian q).mulVec d + p = 0) :
    eval ((quadraticHessian q)⁻¹.mulVec p) q = 0 := by
  have hp : p = -Xc • (quadraticHessian q).mulVec d := by
    have h := eq_neg_of_add_eq_zero_right hequation
    simpa using h
  have hinv : (quadraticHessian q)⁻¹.mulVec p = -Xc • d := by
    rw [hp, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
  rw [hinv, eval_quadratic_smul q hq, hqzero, mul_zero]

end Quadratic

variable {n : ℕ}

/-- Differentiating in a normal coordinate gives the exact linear normal
system, since each normal-map component uses only tangent variables. -/
theorem normal_partial (P : MvPolynomial (Fin n) K) (hP : P.IsHomogeneous 3)
    (radial : Fin n) (IT IL : Finset (Fin n)) (hr : radial ∈ IT) (hnest : IT ⊆ IL)
    (hw : ∀ d ∈ P.support, monomialWeight (singularRadialWeight radial IT IL) d = 0)
    (i : Fin n) (hi : i ∈ ILᶜ) :
    pderiv i P = X radial * pderiv i (normalQuadratic P radial) + normalMapComponent P radial IL i := by
  classical
  have hir : radial ≠ i := by
    intro h
    subst i
    exact Finset.mem_compl.mp hi (hnest hr)
  have hp (j : Fin n) (hj : j ∈ ILᶜ) : pderiv i (normalMapComponent P radial IL j) = 0 :=
    pderiv_eq_zero_of_notMem_vars (by
      intro h
      have ht := Finset.mem_of_mem_erase (normalMapComponent_vars P hP radial IT IL hr hnest hw j hj h)
      exact Finset.mem_compl.mp hi (hnest ht))
  have hK : pderiv i (complementaryPart P radial IL) = 0 :=
    pderiv_eq_zero_of_notMem_vars (by
      intro h
      exact Finset.mem_compl.mp (complementaryPart_vars P hP radial IT IL hr hnest hw h)
        (Finset.mem_union_right _ hi))
  conv_lhs => rw [exact_normal_form P hP radial IT IL hr hnest hw]
  simp only [map_add, map_sum, pderiv_mul, pderiv_X_of_ne hir, zero_mul, zero_add, hK, add_zero]
  congr 1
  calc
    _ = ∑ j ∈ ILᶜ, (pderiv i (X j)) * normalMapComponent P radial IL j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hp j hj, mul_zero, add_zero]
    _ = normalMapComponent P radial IL i := by
      simp [pderiv_X, Pi.single_apply, hi]

theorem singular_radial_equation (P : MvPolynomial (Fin n) K) (hP : P.IsHomogeneous 3)
    (radial : Fin n) (IT IL : Finset (Fin n)) (hr : radial ∈ IT) (hnest : IT ⊆ IL)
    (hw : ∀ d ∈ P.support, monomialWeight (singularRadialWeight radial IT IL) d = 0)
    (x : Fin n → K) (hx : gradient P x = 0) : eval x (normalQuadratic P radial) = 0 := by
  have h := congrFun hx radial
  change eval x (pderiv radial P) = 0 at h
  rwa [radial_partial_eq_normalQuadratic P hP radial IT IL hr hnest hw] at h

theorem singular_normal_equation (P : MvPolynomial (Fin n) K) (hP : P.IsHomogeneous 3)
    (radial : Fin n) (IT IL : Finset (Fin n)) (hr : radial ∈ IT) (hnest : IT ⊆ IL)
    (hw : ∀ d ∈ P.support, monomialWeight (singularRadialWeight radial IT IL) d = 0)
    (x : Fin n → K) (hx : gradient P x = 0) (i : Fin n) (hi : i ∈ ILᶜ) :
    x radial * eval x (pderiv i (normalQuadratic P radial)) +
      eval x (normalMapComponent P radial IL i) = 0 := by
  have h := congrFun hx i
  change eval x (pderiv i P) = 0 at h
  rw [normal_partial P hP radial IT IL hr hnest hw i hi] at h
  simpa using h

/-- At every actual singular point of the equality model, the normal-map
values satisfy the inverse-pairing quadric relation in the actual normal
coordinate ring. In particular this holds on the radial affine chart. -/
theorem singular_inverse_pairing_relation [CharZero K]
    (P : MvPolynomial (Fin n) K) (hP : P.IsHomogeneous 3)
    (radial : Fin n) (IT IL : Finset (Fin n)) (hr : radial ∈ IT) (hnest : IT ⊆ IL)
    (hw : ∀ d ∈ P.support, monomialWeight (singularRadialWeight radial IT IL) d = 0)
    (q : MvPolynomial (↑ILᶜ : Type) K) (hq : q.IsHomogeneous 2)
    (hqe : rename (fun i : (↑ILᶜ : Type) => (i : Fin n)) q = normalQuadratic P radial)
    (hdet : (quadraticHessian q).det ≠ 0)
    (x : Fin n → K) (hx : gradient P x = 0) :
    eval ((quadraticHessian q)⁻¹.mulVec
      (fun i : (↑ILᶜ : Type) => eval x (normalMapComponent P radial IL i))) q = 0 := by
  classical
  apply inverse_pairing_relation q hq hdet (x radial) (fun i => x i)
  · have h := singular_radial_equation P hP radial IT IL hr hnest hw x hx
    rw [← hqe, eval_rename] at h
    exact h
  · ext i
    have h := singular_normal_equation P hP radial IT IL hr hnest hw x hx i i.property
    have he : eval x (pderiv (i : Fin n) (normalQuadratic P radial)) =
        (quadraticHessian q).mulVec (fun j : (↑ILᶜ : Type) => x j) i := by
      rw [← hqe, pderiv_rename Subtype.val_injective i q, eval_rename]
      exact eval_quadratic_partial q hq _ i
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, he] using h

end HessianTheorem11.SingularNormalEquations
