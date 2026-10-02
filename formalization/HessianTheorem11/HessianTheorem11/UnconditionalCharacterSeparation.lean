import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Tactic

/-! One integral special-linear weight separates any finite family of
distinct sum-zero integral characters. The argument uses a product of actual
nonzero linear polynomials over the infinite integral domain ℤ. -/
noncomputable section
namespace HessianTheorem11.UnconditionalCharacters
open MvPolynomial Finset

def linearPolynomial {n : ℕ} (v : Fin n → ℤ) : MvPolynomial (Fin n) ℤ :=
  ∑ i, C (v i) * X i

theorem eval_linearPolynomial {n : ℕ} (v x : Fin n → ℤ) :
    eval x (linearPolynomial v) = ∑ i, v i * x i := by
  simp [linearPolynomial]

theorem linearPolynomial_ne_zero {n : ℕ} (v : Fin n → ℤ) (hv : v ≠ 0) :
    linearPolynomial v ≠ 0 := by
  classical
  intro h
  apply hv
  funext i
  have hi := congrArg (eval (Pi.single i (1 : ℤ))) h
  simpa [eval_linearPolynomial, Pi.single_apply] using hi

/-- Simultaneously avoid finitely many nonzero integral linear forms. -/
theorem exists_avoiding {n : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → Fin n → ℤ) (hv : ∀ a, v a ≠ 0) :
    ∃ x : Fin n → ℤ, ∀ a, (∑ i, v a i * x i) ≠ 0 := by
  classical
  let p : MvPolynomial (Fin n) ℤ := ∏ a, linearPolynomial (v a)
  have hp : p ≠ 0 := Finset.prod_ne_zero_iff.mpr fun a _ =>
    linearPolynomial_ne_zero (v a) (hv a)
  have hex : ∃ x : Fin n → ℤ, eval x p ≠ 0 := by
    by_contra h
    push_neg at h
    apply hp
    apply MvPolynomial.funext
    intro x
    simpa using h x
  obtain ⟨x,hx⟩ := hex
  refine ⟨x,?_⟩
  have he : (∏ a, ∑ i, v a i * x i) ≠ 0 := by
    simpa [p,eval_linearPolynomial] using hx
  exact fun a => Finset.prod_ne_zero_iff.mp he a (mem_univ a)

/-- Separate a finite set of sum-zero characters by a sum-zero integral
weight. No primitivity or sign convention is required. -/
theorem exists_separating_sum_zero {n : ℕ} (hn : 0 < n)
    (S : Finset (Fin n → ℤ)) (hS : ∀ v ∈ S, ∑ i, v i = 0) :
    ∃ w : Fin n → ℤ, (∑ i, w i = 0) ∧
      ∀ v ∈ S, ∀ u ∈ S, v ≠ u → (∑ i, v i * w i) ≠ ∑ i, u i * w i := by
  classical
  let I := {p : S × S // p.1 ≠ p.2}
  let v : I → Fin n → ℤ := fun a i => a.val.1.val i - a.val.2.val i
  have hv : ∀ a, v a ≠ 0 := by
    intro a h
    apply a.property
    apply Subtype.ext
    funext i
    have hi := congrFun h i
    exact sub_eq_zero.mp hi
  obtain ⟨x,hx⟩ := exists_avoiding v hv
  let w : Fin n → ℤ := fun i => (n : ℤ) * x i - ∑ j, x j
  have hw : ∑ i, w i = 0 := by
    simp [w,Finset.sum_sub_distrib,← Finset.mul_sum]
  refine ⟨w,hw,?_⟩
  intro a ha b hb hab he
  let k : I := ⟨(⟨a,ha⟩,⟨b,hb⟩),by simpa using hab⟩
  have ha0 := hS a ha
  have hb0 := hS b hb
  have hdot (c : Fin n → ℤ) (hc : ∑ i, c i = 0) :
      (∑ i, c i * w i) = (n : ℤ) * ∑ i, c i * x i := by
    simp only [w,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hc,zero_mul,
      sub_zero]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hdot a ha0,hdot b hb0] at he
  have hnz : (n : ℤ) ≠ 0 := by omega
  have he' := mul_left_cancel₀ hnz he
  apply hx k
  change (∑ i, (a i - b i) * x i) = 0
  simp only [sub_mul,Finset.sum_sub_distrib,he',sub_self]

end HessianTheorem11.UnconditionalCharacters
