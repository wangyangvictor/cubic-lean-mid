import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Derivative

/-! A literal smooth residue zero lifts by one-coordinate Hensel lifting.
All residue coordinates are preserved, so nonzero residue vectors remain
nonzero and have an actual unit coordinate. No degree or characteristic
restriction is imposed. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PadicSmoothResidueZero
open MvPolynomial

private def coordinatePolynomial {R : Type*} [CommRing R] {n : ℕ}
    (F : MvPolynomial (Fin n) R) (a : Fin n → R) (i : Fin n) : Polynomial R :=
  eval₂Hom Polynomial.C (Function.update (fun j => Polynomial.C (a j)) i Polynomial.X) F

private theorem eval_coordinatePolynomial {R : Type*} [CommRing R] {n : ℕ}
    (F : MvPolynomial (Fin n) R) (a : Fin n → R) (i : Fin n) (t : R) :
    (coordinatePolynomial F a i).eval t = eval (Function.update a i t) F := by
  classical
  induction F using MvPolynomial.induction_on with
  | C c => simp [coordinatePolynomial]
  | add F G hF hG => simp [coordinatePolynomial] at hF hG ⊢; rw [hF,hG]
  | mul_X F j hF =>
      by_cases h : j=i <;> simp [coordinatePolynomial,h] at hF ⊢ <;> rw [hF]

private theorem derivative_coordinatePolynomial {R : Type*} [CommRing R] {n : ℕ}
    (F : MvPolynomial (Fin n) R) (a : Fin n → R) (i : Fin n) :
    (coordinatePolynomial F a i).derivative=coordinatePolynomial (pderiv i F) a i := by
  classical
  induction F using MvPolynomial.induction_on with
  | C c => simp [coordinatePolynomial]
  | add F G hF hG => simp [coordinatePolynomial] at hF hG ⊢; rw [hF,hG]
  | mul_X F j hF =>
      by_cases h : j=i <;>
        simp [coordinatePolynomial,Polynomial.derivative_mul,h] at hF ⊢ <;>
        rw [hF] <;> ring

theorem toZMod_eq_zero_iff_norm_lt_one {p : ℕ} [Fact p.Prime] (a : ℤ_[p]) :
    PadicInt.toZMod a=0 ↔ ‖a‖<1 := by
  rw [← RingHom.mem_ker,PadicInt.ker_toZMod,PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton,PadicInt.norm_lt_one_iff_dvd]

theorem toZMod_ne_zero_iff_isUnit {p : ℕ} [Fact p.Prime] (a : ℤ_[p]) :
    PadicInt.toZMod a≠0 ↔ IsUnit a := by
  rw [ne_eq,toZMod_eq_zero_iff_norm_lt_one,← PadicInt.not_isUnit_iff,not_not]

/-- Hensel lifting changes only the selected coordinate; every coordinate
keeps its residue and the selected first partial becomes a unit. -/
theorem exists_integral_lift {p n : ℕ} [Fact p.Prime]
    (F : MvPolynomial (Fin n) ℤ_[p]) (a : Fin n → ℤ_[p]) (i : Fin n)
    (hzero : PadicInt.toZMod (eval a F)=0)
    (hpartial : PadicInt.toZMod (eval a (pderiv i F))≠0) :
    ∃ x : Fin n → ℤ_[p], eval x F=0 ∧
      (∀ j,PadicInt.toZMod (x j)=PadicInt.toZMod (a j)) ∧
      IsUnit (eval x (pderiv i F)) := by
  classical
  let P := coordinatePolynomial F a i
  have heval (t : ℤ_[p]) : P.aeval t=eval (Function.update a i t) F := by
    simpa only [Polynomial.aeval_def,Polynomial.eval₂_id] using eval_coordinatePolynomial F a i t
  have hderiv (t : ℤ_[p]) : P.derivative.aeval t=eval (Function.update a i t) (pderiv i F) := by
    rw [show P.derivative=coordinatePolynomial (pderiv i F) a i from derivative_coordinatePolynomial F a i]
    simpa only [Polynomial.aeval_def,Polynomial.eval₂_id] using
      eval_coordinatePolynomial (pderiv i F) a i t
  have hd : ‖P.derivative.aeval (a i)‖=1 := by
    rw [hderiv,Function.update_eq_self]
    exact PadicInt.isUnit_iff.mp ((toZMod_ne_zero_iff_isUnit _).mp hpartial)
  have hsmall : ‖P.aeval (a i)‖<‖P.derivative.aeval (a i)‖^2 := by
    rw [hd,one_pow,heval,Function.update_eq_self]
    exact (toZMod_eq_zero_iff_norm_lt_one _).mp hzero
  obtain ⟨b,hb,hclose,hdb,_⟩ := hensels_lemma hsmall
  refine ⟨Function.update a i b,by simpa only [heval] using hb,?_,?_⟩
  · intro j
    by_cases hj : j=i
    · subst j
      simp only [Function.update_self]
      apply sub_eq_zero.mp
      rw [← map_sub]
      exact (toZMod_eq_zero_iff_norm_lt_one _).mpr (by simpa only [hd] using hclose)
    · simp [Function.update_of_ne hj]
  · apply PadicInt.isUnit_iff.mpr
    rw [← hderiv,hdb,hd]

/-- Every actual smooth residue zero has an integral lift with all residues
unchanged. For a nonzero residue vector, a lifted coordinate is a unit. -/
theorem exists_integral_zero_of_smooth_reduction {p n : ℕ} [Fact p.Prime]
    (F : MvPolynomial (Fin n) ℤ_[p]) (z : Fin n → ZMod p) (hz : z≠0)
    (hzero : eval z (map PadicInt.toZMod F)=0)
    (hsmooth : ∃ i,eval z (pderiv i (map PadicInt.toZMod F))≠0) :
    ∃ x : Fin n → ℤ_[p], (∀ j,PadicInt.toZMod (x j)=z j) ∧ eval x F=0 ∧
      (∃ j,IsUnit (x j)) ∧ ∃ i,IsUnit (eval x (pderiv i F)) := by
  classical
  let a : Fin n → ℤ_[p] := fun j => (z j).val
  have ha : ∀ j,PadicInt.toZMod (a j)=z j := by
    intro j
    simp [a]
  have heval (G : MvPolynomial (Fin n) ℤ_[p]) :
      PadicInt.toZMod (eval a G)=eval z (map PadicInt.toZMod G) := by
    rw [MvPolynomial.map_eval]
    have he : (PadicInt.toZMod ∘ a)=z := funext ha
    rw [he]
  obtain ⟨i,hi⟩ := hsmooth
  have hz' : PadicInt.toZMod (eval a F)=0 := (heval F).trans hzero
  have hi' : PadicInt.toZMod (eval a (pderiv i F))≠0 := by
    rw [heval,← pderiv_map]
    exact hi
  obtain ⟨x,hx,hres,hunit⟩ := exists_integral_lift F a i hz' hi'
  have hres' : ∀ j,PadicInt.toZMod (x j)=z j := fun j => (hres j).trans (ha j)
  obtain ⟨j,hj⟩ : ∃ j,z j≠0 := by
    by_contra! h
    exact hz (funext h)
  exact ⟨x,hres',hx,⟨j,(toZMod_ne_zero_iff_isUnit _).mp (by rwa [hres'])⟩,i,hunit⟩

/-- A literal smooth nonzero residue zero gives a nonzero zero of the
coefficient-extended polynomial over Qp, with a nonzero first partial. -/
theorem exists_field_zero_of_smooth_reduction {p n : ℕ} [Fact p.Prime]
    (F : MvPolynomial (Fin n) ℤ_[p]) (z : Fin n → ZMod p) (hz : z≠0)
    (hzero : eval z (map PadicInt.toZMod F)=0)
    (hsmooth : ∃ i,eval z (pderiv i (map PadicInt.toZMod F))≠0) :
    ∃ x : Fin n → ℚ_[p], x≠0 ∧ eval x (map (algebraMap ℤ_[p] ℚ_[p]) F)=0 ∧
      ∃ i,eval x (pderiv i (map (algebraMap ℤ_[p] ℚ_[p]) F))≠0 := by
  obtain ⟨x,_,hx,⟨j,hj⟩,⟨i,hi⟩⟩ :=
    exists_integral_zero_of_smooth_reduction F z hz hzero hsmooth
  refine ⟨fun k => (x k : ℚ_[p]),?_,?_,i,?_⟩
  · intro h
    exact hj.ne_zero (by simpa using congrFun h j)
  · have he := MvPolynomial.map_eval (algebraMap ℤ_[p] ℚ_[p]) x F
    simpa only [hx,map_zero,Function.comp_def,PadicInt.algebraMap_apply] using he.symm
  · rw [pderiv_map]
    have he := MvPolynomial.map_eval (algebraMap ℤ_[p] ℚ_[p]) x (pderiv i F)
    simp only [Function.comp_def,PadicInt.algebraMap_apply] at he
    rw [← he]
    exact PadicInt.coe_ne_zero.mpr hi.ne_zero

/-- The contrapositive used by descent: absence of nonzero Qp zeros
excludes every literal smooth nonzero zero of the reduction. -/
theorem reduction_no_smooth_zero {p n : ℕ} [Fact p.Prime]
    (F : MvPolynomial (Fin n) ℤ_[p])
    (hno : ¬ ∃ x : Fin n → ℚ_[p], x≠0 ∧
      eval x (map (algebraMap ℤ_[p] ℚ_[p]) F)=0) :
    ¬ ∃ z : Fin n → ZMod p, z≠0 ∧ eval z (map PadicInt.toZMod F)=0 ∧
      ∃ i,eval z (pderiv i (map PadicInt.toZMod F))≠0 := by
  rintro ⟨z,hz,hzero,hsmooth⟩
  obtain ⟨x,hx,hFx,_⟩ := exists_field_zero_of_smooth_reduction F z hz hzero hsmooth
  exact hno ⟨x,hx,hFx⟩

end CubicTenVariables.PadicSmoothResidueZero
