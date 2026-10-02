import CubicTenVariables.GeneralSmoothResidueIteration
import CubicTenVariables.UniformPrimePolynomialZeros

/-!
# Integral binary cubics with prime-divisible cubic part

These are actual degree-at-most-three polynomials, not a root-count interface.
The nondegenerate quadratic reduction has at most one critical point. At a
singular integral residue center, division of the translated polynomial by
p^2 is performed coefficientwise and preserves the same class. This is the
algebraic step needed by the singular quadratic-lifting recurrence.
-/

noncomputable section
namespace CubicTenVariables.BinaryCubicPerturbation
open MvPolynomial

structure Coefficients where
  c : ℤ
  lx : ℤ
  ly : ℤ
  qx : ℤ
  qxy : ℤ
  qy : ℤ
  cx : ℤ
  cxxy : ℤ
  cxyy : ℤ
  cy : ℤ

/-- Literal evaluation over any residue ring or over the integers. -/
def value (G : Coefficients) {R : Type*} [CommRing R] (p x y : R) : R :=
  G.c + G.lx * x + G.ly * y + G.qx * x^2 + G.qxy * x*y + G.qy*y^2 +
    p * (G.cx*x^3 + G.cxxy*x^2*y + G.cxyy*x*y^2 + G.cy*y^3)

def dx (G : Coefficients) {R : Type*} [CommRing R] (p x y : R) : R :=
  G.lx + 2*G.qx*x + G.qxy*y +
    p*(3*G.cx*x^2 + 2*G.cxxy*x*y + G.cxyy*y^2)

def dy (G : Coefficients) {R : Type*} [CommRing R] (p x y : R) : R :=
  G.ly + G.qxy*x + 2*G.qy*y +
    p*(G.cxxy*x^2 + 2*G.cxyy*x*y + 3*G.cy*y^2)

def polynomial (G : Coefficients) (p : ℤ) : MvPolynomial (Fin 2) ℤ :=
  C G.c + C G.lx*X 0 + C G.ly*X 1 + C G.qx*X 0^2 +
    C G.qxy*X 0*X 1 + C G.qy*X 1^2 +
    C p*(C G.cx*X 0^3 + C G.cxxy*X 0^2*X 1 +
      C G.cxyy*X 0*X 1^2 + C G.cy*X 1^3)

@[simp] theorem eval₂_polynomial (G : Coefficients) (p : ℤ)
    {R : Type*} [CommRing R] (z : Fin 2 → R) :
    eval₂ (Int.castRingHom R) z (polynomial G p) = value G (p : R) (z 0) (z 1) := by
  simp only [polynomial, value, eval₂_add, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X, Int.coe_castRingHom]

@[simp] theorem eval₂_pderiv_zero (G : Coefficients) (p : ℤ)
    {R : Type*} [CommRing R] (z : Fin 2 → R) :
    eval₂ (Int.castRingHom R) z (pderiv 0 (polynomial G p)) =
      dx G (p : R) (z 0) (z 1) := by
  simp only [polynomial, dx, map_add, pderiv_C, pderiv_mul, pderiv_pow, pderiv_X, eval₂_add, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X, Int.coe_castRingHom]
  norm_num
  ring

@[simp] theorem eval₂_pderiv_one (G : Coefficients) (p : ℤ)
    {R : Type*} [CommRing R] (z : Fin 2 → R) :
    eval₂ (Int.castRingHom R) z (pderiv 1 (polynomial G p)) =
      dy G (p : R) (z 0) (z 1) := by
  simp only [polynomial, dy, map_add, pderiv_C, pderiv_mul, pderiv_pow, pderiv_X, eval₂_add, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X, Int.coe_castRingHom]
  norm_num
  ring

def discriminant (G : Coefficients) : ℤ := 4*G.qx*G.qy-G.qxy^2

/-- Only the literal two first derivatives are used for a critical point. -/
theorem critical_point_unique (G : Coefficients) {K : Type*} [Field K]
    (hD : (discriminant G : K) ≠ 0) {x y x' y' : K}
    (hx : dx G 0 x y = 0) (hy : dy G 0 x y = 0)
    (hx' : dx G 0 x' y' = 0) (hy' : dy G 0 x' y' = 0) :
    x = x' ∧ y = y' := by
  simp only [dx, dy, zero_mul, add_zero] at hx hy hx' hy'
  have hxx : (discriminant G : K)*(x-x') = 0 := by
    simp only [discriminant, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_pow]
    linear_combination (2*(G.qy : K))*(hx-hx') - (G.qxy : K)*(hy-hy')
  have hyy : (discriminant G : K)*(y-y') = 0 := by
    simp only [discriminant, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_pow]
    linear_combination (2*(G.qx : K))*(hy-hy') - (G.qxy : K)*(hx-hx')
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp hxx).resolve_left hD),
    sub_eq_zero.mp ((mul_eq_zero.mp hyy).resolve_left hD)⟩

/-- The coefficients after translation and division by p^2. -/
def rescale (G : Coefficients) (p a b : ℤ) : Coefficients where
  c := value G p a b / p^2
  lx := dx G p a b / p
  ly := dy G p a b / p
  qx := G.qx + p*(3*G.cx*a + G.cxxy*b)
  qxy := G.qxy + p*(2*G.cxxy*a + 2*G.cxyy*b)
  qy := G.qy + p*(G.cxyy*a + 3*G.cy*b)
  cx := p*G.cx
  cxxy := p*G.cxxy
  cxyy := p*G.cxyy
  cy := p*G.cy

/-- Exact integer Taylor rescaling at a singular residue center. -/
theorem value_translate_rescale (G : Coefficients) (p a b : ℤ)
    (h0 : p^2 ∣ value G p a b) (hx : p ∣ dx G p a b)
    (hy : p ∣ dy G p a b) (x y : ℤ) :
    value G p (a+p*x) (b+p*y) = p^2 * value (rescale G p a b) p x y := by
  have hc := Int.ediv_mul_cancel h0
  have hdx := Int.ediv_mul_cancel hx
  have hdy := Int.ediv_mul_cancel hy
  simp only [value, rescale, dx, dy, Int.cast_id]
  simp only [value, dx, dy, Int.cast_id] at hc hdx hdy
  linear_combination -hc - p*x*hdx - p*y*hdy

/-- The reduced quadratic Hessian determinant is unchanged by the rescaling. -/
theorem discriminant_rescale_mod (G : Coefficients) (p : ℕ) (a b : ℤ) :
    (discriminant (rescale G (p : ℤ) a b) : ZMod p) = (discriminant G : ZMod p) := by
  simp [discriminant, rescale]

/-- Thus the rescaled polynomial stays in the same nondegenerate class. -/
theorem rescale_nondegenerate (G : Coefficients) (p : ℕ) (a b : ℤ)
    (hD : (discriminant G : ZMod p) ≠ 0) :
    (discriminant (rescale G (p : ℤ) a b) : ZMod p) ≠ 0 := by
  rwa [discriminant_rescale_mod]

/-- At a critical residue class the value modulo p^2 is constant. -/
theorem sq_dvd_translate_sub (G : Coefficients) (p a b : ℤ)
    (hx : p ∣ dx G p a b) (hy : p ∣ dy G p a b) (x y : ℤ) :
    p^2 ∣ value G p (a+p*x) (b+p*y) - value G p a b := by
  obtain ⟨u, hu⟩ := hx
  obtain ⟨v, hv⟩ := hy
  refine ⟨u*x+v*y +
    (G.qx+p*(3*G.cx*a+G.cxxy*b))*x^2 +
    (G.qxy+p*(2*G.cxxy*a+2*G.cxyy*b))*x*y +
    (G.qy+p*(G.cxyy*a+3*G.cy*b))*y^2 +
    p^2*(G.cx*x^3+G.cxxy*x^2*y+G.cxyy*x*y^2+G.cy*y^3), ?_⟩
  simp only [value, dx, dy, Int.cast_id] at hu hv ⊢
  linear_combination p*x*hu + p*y*hv

/-- Thus a critical residue class has no roots at levels at least two
unless the actual chosen integral center is a root modulo p^2. -/
theorem sq_dvd_value_translate_iff (G : Coefficients) (p a b : ℤ)
    (hx : p ∣ dx G p a b) (hy : p ∣ dy G p a b) (x y : ℤ) :
    p^2 ∣ value G p (a+p*x) (b+p*y) ↔ p^2 ∣ value G p a b := by
  have h := sq_dvd_translate_sub G p a b hx hy x y
  constructor
  · intro hz
    simpa only [sub_sub_cancel] using dvd_sub hz h
  · intro hz
    simpa only [sub_add_cancel] using dvd_add h hz

/-- A literal all-level smooth-class count for the binary polynomial.
The singular class is handled separately by rescale, not by this theorem. -/
theorem card_smooth_binary_lifts (G : Coefficients) (p : ℕ) [Fact p.Prime]
    (a : ℕ) (ha : 1 ≤ a) (v : Fin 2 → ZMod p)
    (hv : value G 0 (v 0) (v 1) = 0)
    (hg : dx G 0 (v 0) (v 1) ≠ 0 ∨ dy G 0 (v 0) (v 1) ≠ 0) :
    (Finset.univ.filter fun z : Fin 2 → ZMod (p^a) =>
      (∀ i, SmoothResidueIteration.toPrime p a ha (z i) = v i) ∧
        value G (p : ZMod (p^a)) (z 0) (z 1) = 0).card = p^(a-1) := by
  have hv' : eval₂ (Int.castRingHom (ZMod p)) v (polynomial G (p : ℤ)) = 0 := by
    simpa only [eval₂_polynomial, Int.cast_natCast, ZMod.natCast_self] using hv
  have hg' : ∃ i, eval₂ (Int.castRingHom (ZMod p)) v
      (pderiv i (polynomial G (p : ℤ))) ≠ 0 := by
    rcases hg with h | h
    · exact ⟨0, by simpa only [eval₂_pderiv_zero, Int.cast_natCast, ZMod.natCast_self] using h⟩
    · exact ⟨1, by simpa only [eval₂_pderiv_one, Int.cast_natCast, ZMod.natCast_self] using h⟩
  simpa only [eval₂_polynomial, Int.cast_natCast, Nat.reduceSub, mul_one] using
    GeneralSmoothResidueIteration.card_smooth_zero_filter p (polynomial G (p : ℤ))
      v hv' hg' a ha

/-- The singular zero classes modulo p form a set of size at most one. -/
theorem card_singular_prime_zeros_le_one (G : Coefficients) (p : ℕ) [Fact p.Prime]
    (hD : (discriminant G : ZMod p) ≠ 0) :
    (Finset.univ.filter fun z : Fin 2 → ZMod p =>
      value G 0 (z 0) (z 1) = 0 ∧ dx G 0 (z 0) (z 1) = 0 ∧
        dy G 0 (z 0) (z 1) = 0).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro x hx y hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  obtain ⟨h0,h1⟩ := critical_point_unique G hD hx.2.1 hx.2.2 hy.2.1 hy.2.2
  funext i
  fin_cases i
  · exact h0
  · exact h1

end CubicTenVariables.BinaryCubicPerturbation
