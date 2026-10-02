import TranslatedDepthSeven.StarEquationBounds
import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Concrete affine and projective zero sets of homogeneous integral equations

This file starts with a literal finite family of integral multivariable
polynomials.  It defines its common zero set after extension to a field,
proves the expected scaling law from an explicit homogeneity hypothesis, and
identifies the punctured affine cone modulo nonzero scalar multiplication with
a concrete subset of Mathlib's projectivization.

The last results connect this construction directly to the top coefficient of
the explicit line-restriction polynomial from `StarEquationBounds`.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped LinearAlgebra.Projectivization

open MvPolynomial

variable {σ : Type*}

/-- Evaluation of a homogeneous polynomial on a scalar multiple. -/
theorem eval_smul_of_isHomogeneous
    {R : Type*} [CommSemiring R]
    (f : MvPolynomial σ R) (x : σ → R) (a : R) (d : ℕ)
    (hf : f.IsHomogeneous d) :
    MvPolynomial.eval (fun i ↦ a * x i) f =
      a ^ d * MvPolynomial.eval x f := by
  induction hf using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simp [ihp, ihq, mul_add]
  | monomial m r hm =>
      rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
      simp only [mul_pow, Finsupp.prod, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum]
      have hsum : ∑ i ∈ m.support, m i = d := by
        simpa only [Finsupp.weight_apply, Pi.one_apply, nsmul_eq_mul,
          mul_one, Finsupp.sum] using hm
      rw [hsum]
      ac_rfl

/-- The literal common zero set, over a commutative ring `R`, of a finite
family of integral equations after coefficient extension `ℤ → R`. -/
def integralAffineConeZeroSetOver
    (R : Type*) [CommRing R]
    (equations : Finset (MvPolynomial σ ℤ)) : Set (σ → R) :=
  {x | ∀ f ∈ equations,
    MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom R) f) = 0}

@[simp]
theorem mem_integralAffineConeZeroSetOver_iff
    {R : Type*} [CommRing R]
    (equations : Finset (MvPolynomial σ ℤ)) (x : σ → R) :
    x ∈ integralAffineConeZeroSetOver R equations ↔
      ∀ f ∈ equations,
        MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom R) f) = 0 :=
  Iff.rfl

/-- The literal common integral zero set of a finite family of integral
equations. -/
def integralAffineConeZeroSet
    (equations : Finset (MvPolynomial σ ℤ)) : Set (σ → ℤ) :=
  {x | ∀ f ∈ equations, MvPolynomial.eval x f = 0}

@[simp]
theorem mem_integralAffineConeZeroSet_iff
    (equations : Finset (MvPolynomial σ ℤ)) (x : σ → ℤ) :
    x ∈ integralAffineConeZeroSet equations ↔
      ∀ f ∈ equations, MvPolynomial.eval x f = 0 :=
  Iff.rfl

/-- Evaluation after extending integral coefficients is exactly the image of
the integral evaluation. -/
theorem eval_map_intCast
    {R : Type*} [CommRing R]
    (f : MvPolynomial σ ℤ) (x : σ → ℤ) :
    MvPolynomial.eval (fun i ↦ (x i : R))
        (MvPolynomial.map (Int.castRingHom R) f) =
      (MvPolynomial.eval x f : R) := by
  simpa only [Function.comp_apply] using
    (MvPolynomial.map_eval (Int.castRingHom R) x f).symm

/-- Every integral common zero remains a common zero after coefficient and
coordinate extension to a commutative ring. -/
theorem intCast_mem_integralAffineConeZeroSetOver
    {R : Type*} [CommRing R]
    (equations : Finset (MvPolynomial σ ℤ)) {x : σ → ℤ}
    (hx : x ∈ integralAffineConeZeroSet equations) :
    (fun i ↦ (x i : R)) ∈ integralAffineConeZeroSetOver R equations := by
  intro f hf
  rw [eval_map_intCast, hx f hf, Int.cast_zero]

/-- Over a characteristic-zero field, coefficient extension reflects as
well as preserves integral common zeros. -/
theorem intCast_mem_integralAffineConeZeroSetOver_iff
    {K : Type*} [Field K] [CharZero K]
    (equations : Finset (MvPolynomial σ ℤ)) (x : σ → ℤ) :
    (fun i ↦ (x i : K)) ∈ integralAffineConeZeroSetOver K equations ↔
      x ∈ integralAffineConeZeroSet equations := by
  simp only [mem_integralAffineConeZeroSetOver_iff,
    mem_integralAffineConeZeroSet_iff, eval_map_intCast, Int.cast_eq_zero]

/-- A nonzero integral vector stays nonzero after coordinatewise extension
to a characteristic-zero field. -/
theorem intCast_ne_zero
    {K : Type*} [Field K] [CharZero K]
    {x : σ → ℤ} (hx : x ≠ 0) :
    (fun i ↦ (x i : K)) ≠ 0 := by
  intro hcast
  apply hx
  funext i
  have hi := congrFun hcast i
  simpa only [Pi.zero_apply, Int.cast_eq_zero] using hi

/-- A common zero of homogeneous integral equations remains a common zero
after scalar multiplication over any commutative ring. -/
theorem smul_mem_integralAffineConeZeroSetOver
    {R : Type*} [CommRing R]
    (equations : Finset (MvPolynomial σ ℤ))
    (degree : MvPolynomial σ ℤ → ℕ)
    (hhom : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    {x : σ → R}
    (hx : x ∈ integralAffineConeZeroSetOver R equations) (a : R) :
    (fun i ↦ a * x i) ∈ integralAffineConeZeroSetOver R equations := by
  intro f hf
  have hhomR :
      (MvPolynomial.map (Int.castRingHom R) f).IsHomogeneous (degree f) :=
    (hhom f hf).map _
  rw [eval_smul_of_isHomogeneous _ _ _ _ hhomR, hx f hf, mul_zero]

/-- Over a field, multiplication by a nonzero scalar preserves and reflects
membership in the affine cone. -/
theorem smul_mem_integralAffineConeZeroSetOver_iff
    {K : Type*} [Field K]
    (equations : Finset (MvPolynomial σ ℤ))
    (degree : MvPolynomial σ ℤ → ℕ)
    (hhom : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    (x : σ → K) {a : K} (ha : a ≠ 0) :
    (fun i ↦ a * x i) ∈ integralAffineConeZeroSetOver K equations ↔
      x ∈ integralAffineConeZeroSetOver K equations := by
  constructor
  · intro hax
    have hscaled :=
      smul_mem_integralAffineConeZeroSetOver equations degree hhom hax a⁻¹
    simpa [ha] using hscaled
  · intro hx
    exact smul_mem_integralAffineConeZeroSetOver equations degree hhom hx a

/-- Integral scalar multiplication preserves the common integral zero set. -/
theorem smul_mem_integralAffineConeZeroSet
    (equations : Finset (MvPolynomial σ ℤ))
    (degree : MvPolynomial σ ℤ → ℕ)
    (hhom : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    {x : σ → ℤ} (hx : x ∈ integralAffineConeZeroSet equations) (a : ℤ) :
    (fun i ↦ a * x i) ∈ integralAffineConeZeroSet equations := by
  intro f hf
  rw [eval_smul_of_isHomogeneous _ _ _ _ (hhom f hf), hx f hf, mul_zero]

/-- The projectivization of the punctured common zero set.  Membership means
literally that the projective point has a nonzero representative satisfying
all of the displayed, coefficient-extended integral equations. -/
def integralProjectiveConeZeroSetOver
    (K : Type*) [Field K]
    (equations : Finset (MvPolynomial σ ℤ)) :
    Set (ℙ K (σ → K)) :=
  {P | ∃ (x : σ → K) (hx : x ≠ 0),
    P = Projectivization.mk K x hx ∧
      x ∈ integralAffineConeZeroSetOver K equations}

/-- For homogeneous equations, a nonzero vector satisfies the affine
equations exactly when its projective class belongs to the projective zero
set. -/
theorem mk_mem_integralProjectiveConeZeroSetOver_iff
    {K : Type*} [Field K]
    (equations : Finset (MvPolynomial σ ℤ))
    (degree : MvPolynomial σ ℤ → ℕ)
    (hhom : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    (x : σ → K) (hx : x ≠ 0) :
    Projectivization.mk K x hx ∈
        integralProjectiveConeZeroSetOver K equations ↔
      x ∈ integralAffineConeZeroSetOver K equations := by
  constructor
  · rintro ⟨y, hy, hxy, hycone⟩
    obtain ⟨a, ha⟩ :=
      (Projectivization.mk_eq_mk_iff' K x y hx hy).mp hxy
    have hscaled :=
      smul_mem_integralAffineConeZeroSetOver equations degree hhom hycone a
    have haxy : (fun i ↦ a * y i) = x := by
      funext i
      simpa using congrFun ha i
    simpa only [haxy] using hscaled
  · intro hxcone
    exact ⟨x, hx, rfl, hxcone⟩

/-- Equivalently, projective membership can be checked on Mathlib's chosen
nonzero representative. -/
theorem mem_integralProjectiveConeZeroSetOver_iff_rep
    {K : Type*} [Field K]
    (equations : Finset (MvPolynomial σ ℤ))
    (degree : MvPolynomial σ ℤ → ℕ)
    (hhom : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    (P : ℙ K (σ → K)) :
    P ∈ integralProjectiveConeZeroSetOver K equations ↔
      P.rep ∈ integralAffineConeZeroSetOver K equations := by
  simpa only [Projectivization.mk_rep] using
    (mk_mem_integralProjectiveConeZeroSetOver_iff
      equations degree hhom P.rep P.rep_nonzero)

/-- The top star equation attached to each homogeneous equation is literally
the original equation. -/
theorem starCoefficient_top_eq_on_equations
    (equations : Finset (MvPolynomial σ ℤ))
    (degree : MvPolynomial σ ℤ → ℕ)
    (hhom : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    (h : σ → ℤ) {f : MvPolynomial σ ℤ} (hf : f ∈ equations) :
    starCoefficient f h (degree f) = f :=
  starCoefficient_eq_of_isHomogeneous f h (degree f) (hhom f hf)

/-- Consequently, simultaneous vanishing of the top star equations is
exactly membership in the original integral affine cone. -/
theorem all_top_starCoefficients_eq_zero_iff_mem_integralAffineConeZeroSet
    (equations : Finset (MvPolynomial σ ℤ))
    (degree : MvPolynomial σ ℤ → ℕ)
    (hhom : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    (h z : σ → ℤ) :
    (∀ f ∈ equations,
        MvPolynomial.eval z (starCoefficient f h (degree f)) = 0) ↔
      z ∈ integralAffineConeZeroSet equations := by
  simp only [mem_integralAffineConeZeroSet_iff]
  apply forall_congr'
  intro f
  apply imp_congr_right
  intro hf
  rw [starCoefficient_top_eq_on_equations equations degree hhom h hf]

/-- For a nonzero integral direction, simultaneous vanishing of the top star
equations is exactly membership of its rational projective class in the
projectivized cone. -/
theorem all_top_starCoefficients_eq_zero_iff_mk_rat_mem_projectiveCone
    (equations : Finset (MvPolynomial σ ℤ))
    (degree : MvPolynomial σ ℤ → ℕ)
    (hhom : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    (h z : σ → ℤ) (hz : z ≠ 0) :
    (∀ f ∈ equations,
        MvPolynomial.eval z (starCoefficient f h (degree f)) = 0) ↔
      Projectivization.mk ℚ (fun i ↦ (z i : ℚ))
          (intCast_ne_zero (K := ℚ) hz) ∈
        integralProjectiveConeZeroSetOver ℚ equations := by
  rw [all_top_starCoefficients_eq_zero_iff_mem_integralAffineConeZeroSet
    equations degree hhom h z]
  rw [mk_mem_integralProjectiveConeZeroSetOver_iff
    equations degree hhom (fun i ↦ (z i : ℚ))
      (intCast_ne_zero (K := ℚ) hz)]
  exact (intCast_mem_integralAffineConeZeroSetOver_iff equations z).symm

/-- If every displayed homogeneous equation vanishes identically on an
integral affine line, then its direction lies in the literal integral affine
cone. -/
theorem mem_integralAffineConeZeroSet_of_eval_line_zero
    (equations : Finset (MvPolynomial σ ℤ))
    (degree : MvPolynomial σ ℤ → ℕ)
    (hhom : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    (h z : σ → ℤ)
    (hline : ∀ f ∈ equations, ∀ t : ℤ,
      MvPolynomial.eval (fun i ↦ h i + t * z i) f = 0) :
    z ∈ integralAffineConeZeroSet equations := by
  intro f hf
  exact eval_direction_eq_zero_of_isHomogeneous_of_eval_line_zero
    f h z (degree f) (hhom f hf) (hline f hf)

/-- Hence the nonzero direction of an integral affine line contained in all
the displayed homogeneous equations determines a point of the corresponding
rational projective zero set. -/
theorem mk_rat_mem_projectiveCone_of_eval_line_zero
    (equations : Finset (MvPolynomial σ ℤ))
    (degree : MvPolynomial σ ℤ → ℕ)
    (hhom : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    (h z : σ → ℤ) (hz : z ≠ 0)
    (hline : ∀ f ∈ equations, ∀ t : ℤ,
      MvPolynomial.eval (fun i ↦ h i + t * z i) f = 0) :
    Projectivization.mk ℚ (fun i ↦ (z i : ℚ))
        (intCast_ne_zero (K := ℚ) hz) ∈
      integralProjectiveConeZeroSetOver ℚ equations := by
  apply (mk_mem_integralProjectiveConeZeroSetOver_iff
    equations degree hhom (fun i ↦ (z i : ℚ))
      (intCast_ne_zero (K := ℚ) hz)).2
  exact intCast_mem_integralAffineConeZeroSetOver equations
    (mem_integralAffineConeZeroSet_of_eval_line_zero
      equations degree hhom h z hline)

end

end TranslatedDepthSeven
