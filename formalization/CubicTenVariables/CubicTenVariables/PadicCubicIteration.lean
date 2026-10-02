import CubicTenVariables.PadicPrimitive
import CubicTenVariables.PadicCubicDescentColumns
import HessianTheorem11.PolynomialWeightTransport
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Iteration of a literal integral cubic descent step. The one-step
certificate remains an explicit argument in this module. Its iteration
preserves the original polynomial identity and determinant norm, as well
as the absence of nonzero field zeros. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PadicCubicIteration
open MvPolynomial HessianTheorem11 PolynomialRestriction PolynomialWeightTransport
open scoped BigOperators

variable {p n : ℕ} [Fact p.Prime]

/-- Actual field-zero condition on an integral polynomial. -/
def onlyTrivialFieldZero (F : MvPolynomial (Fin n) ℤ_[p]) : Prop :=
  ∀ x : Fin n → ℚ_[p], eval₂ PadicInt.Coe.ringHom x F=0 → x=0

/-- A nonsingular integral substitution transfers the zero obstruction
to the polynomial obtained after division by a scalar. -/
theorem onlyTrivialFieldZero_of_restrict
    (F G : MvPolynomial (Fin n) ℤ_[p])
    (T : Matrix (Fin n) (Fin n) ℤ_[p]) (c : ℤ_[p])
    (hT : T.det ≠ 0) (he : restrict T F=C c*G)
    (hno : onlyTrivialFieldZero F) : onlyTrivialFieldZero G := by
  classical
  intro x hx
  let ι : ℤ_[p] →+* ℚ_[p] := PadicInt.Coe.ringHom
  have hdet : (T.map ι).det ≠ 0 := by
    change (ι.mapMatrix T).det ≠ 0
    rw [← RingHom.map_det]
    exact fun hz => hT (PadicInt.coe_eq_zero.mp hz)
  have hinj : Function.Injective (T.map ι).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  have hmap := congrArg (map ι) he
  rw [map_restrict,map_mul,map_C] at hmap
  have hz : eval₂ ι ((T.map ι).mulVec x) F=0 := by
    rw [← eval_map,← eval_restrict,hmap,eval_mul,eval_C,eval_map]
    rw [hx,mul_zero]
  apply hinj
  rw [Matrix.mulVec_zero]
  exact hno _ hz

/-- Iterated exact change of variables and scalar division. Neither
polynomial congruences nor determinant valuations are approximate here. -/
theorem exists_iterates
    (F : MvPolynomial (Fin n) ℤ_[p]) (hF : F.IsHomogeneous 3)
    (hno : onlyTrivialFieldZero F)
    (hstep : ∀ G : MvPolynomial (Fin n) ℤ_[p], G.IsHomogeneous 3 →
      onlyTrivialFieldZero G →
      ∃ (T : Matrix (Fin n) (Fin n) ℤ_[p]) (H : MvPolynomial (Fin n) ℤ_[p]),
        H.IsHomogeneous 3 ∧ restrict T G=C (p : ℤ_[p])*H ∧
        ‖T.det‖=‖(p : ℤ_[p])‖^3) (r : ℕ) :
    ∃ (T : Matrix (Fin n) (Fin n) ℤ_[p]) (G : MvPolynomial (Fin n) ℤ_[p]),
      G.IsHomogeneous 3 ∧ restrict T F=C ((p : ℤ_[p])^r)*G ∧
      ‖T.det‖=‖(p : ℤ_[p])‖^(3*r) ∧ onlyTrivialFieldZero G := by
  classical
  induction r with
  | zero => exact ⟨1,F,hF,by simp,by simp,hno⟩
  | succ r ih =>
    obtain ⟨T,G,hG,he,hdet,hnoG⟩ := ih
    obtain ⟨S,H,hH,heS,hdetS⟩ := hstep G hG hnoG
    have hp : (p : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    have hS : S.det ≠ 0 := by
      intro hs
      rw [hs,norm_zero] at hdetS
      exact (pow_ne_zero 3 (norm_ne_zero_iff.mpr hp)) hdetS.symm
    refine ⟨T*S,H,hH,?_,?_,onlyTrivialFieldZero_of_restrict G H S p hS heS hnoG⟩
    · rw [← restrict_restrict,he]
      change aeval (linearForms S) (C ((p : ℤ_[p])^r)*G)=_
      rw [map_mul,aeval_C]
      change C ((p : ℤ_[p])^r)*restrict S G=_
      rw [heS,← mul_assoc,← map_mul,← pow_succ]
    · rw [Matrix.det_mul,norm_mul,hdet,hdetS,← pow_add]
      congr 1

/-- Evaluate the literal iterated identity on coordinate basis vectors.
All coefficients of the residual polynomial are integral, hence so are
these evaluations. -/
theorem column_bound_of_restrict
    (F G : MvPolynomial (Fin n) ℤ_[p])
    (T : Matrix (Fin n) (Fin n) ℤ_[p]) (r : ℕ)
    (he : restrict T F=C ((p : ℤ_[p])^r)*G) (j : Fin n) :
    ‖eval (fun i => ((T i j : ℤ_[p]) : ℚ_[p]))
      (map PadicInt.Coe.ringHom F)‖ ≤ ‖(p : ℚ_[p])‖^r := by
  classical
  let e : Fin n → ℤ_[p] := Pi.single j 1
  have h := congrArg (eval e) he
  rw [eval_restrict,eval_mul,eval_C] at h
  have hc : T.mulVec e=fun i => T i j := by
    simpa only [e] using Matrix.mulVec_single_one T j
  rw [hc] at h
  have hbound : ‖eval (fun i => T i j) F‖ ≤ ‖(p : ℤ_[p])‖^r := by
    rw [h,norm_mul,norm_pow]
    exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one _)
  have heval : eval (fun i => ((T i j : ℤ_[p]) : ℚ_[p]))
      (map PadicInt.Coe.ringHom F)=
        ((eval (fun i => T i j) F : ℤ_[p]) : ℚ_[p]) := by
    rw [eval_map]
    exact (eval₂_comp_left PadicInt.Coe.ringHom (RingHom.id _) (fun i => T i j) F).symm
  rw [heval]
  exact hbound

/-- The exact one-step certificate suffices for a nonzero p-adic zero in
more than nine variables. Iteration, normalization, and compactness are
all discharged here; only construction of the one-step certificate remains. -/
theorem exists_zero_of_step
    (F : MvPolynomial (Fin n) ℤ_[p]) (hF : F.IsHomogeneous 3) (hn : 9 < n)
    (hstep : ∀ G : MvPolynomial (Fin n) ℤ_[p], G.IsHomogeneous 3 →
      onlyTrivialFieldZero G →
      ∃ (T : Matrix (Fin n) (Fin n) ℤ_[p]) (H : MvPolynomial (Fin n) ℤ_[p]),
        H.IsHomogeneous 3 ∧ restrict T G=C (p : ℤ_[p])*H ∧
        ‖T.det‖=‖(p : ℤ_[p])‖^3) :
    ∃ x : Fin n → ℚ_[p], x≠0 ∧ eval x (map PadicInt.Coe.ringHom F)=0 := by
  classical
  by_contra hno
  have hnoF : onlyTrivialFieldZero F := by
    intro x hx
    by_contra hne
    exact hno ⟨x,hne,by simpa only [eval_map] using hx⟩
  have hcert (k : ℕ) : ∃ T : Matrix (Fin n) (Fin n) ℚ_[p],
      ‖(p : ℚ_[p])‖^(3*n*k) ≤ ‖T.det‖ ∧
      ∀ j, ‖eval (fun i => T i j) (map PadicInt.Coe.ringHom F)‖ ≤
        ‖(p : ℚ_[p])‖^(n*k) := by
    obtain ⟨T,G,hG,he,hdet,_⟩ := exists_iterates F hF hnoF hstep (n*k)
    refine ⟨T.map PadicInt.Coe.ringHom,?_,?_⟩
    · have heq : ‖(T.map PadicInt.Coe.ringHom).det‖=‖T.det‖ := by
        change ‖(PadicInt.Coe.ringHom.mapMatrix T).det‖=‖T.det‖
        rw [← RingHom.map_det]
        rfl
      rw [heq,hdet]
      simp only [Nat.mul_assoc]
      exact le_rfl
    · intro j
      exact column_bound_of_restrict F G T (n*k) he j
  obtain ⟨x,_,_,hx,hzero⟩ := PadicCubicDescentColumns.exists_zero_of_certificates
    (map PadicInt.Coe.ringHom F) (hF.map _) hn hcert
  exact hno ⟨x,hx,hzero⟩

end CubicTenVariables.PadicCubicIteration
