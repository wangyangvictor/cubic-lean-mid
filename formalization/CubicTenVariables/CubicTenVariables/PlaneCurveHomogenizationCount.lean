import CubicTenVariables.PlaneCurveHomogenization
import CubicTenVariables.CubicGradientScaling
import CubicTenVariables.FiniteFieldPolynomialZeros

/-! Exact affine-chart decomposition of a homogenized zero cone and the
elementary bound for its hyperplane-at-infinity contribution. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.PlaneCurveHomogenization
open MvPolynomial TranslatedDepthSeven

variable {K : Type*} [Field K] {n : ℕ}

def infinityVector (x : Fin n → K) : Option (Fin n) → K
  | none => 0
  | some i => x i

theorem eval_at_infinity (f : MvPolynomial (Fin n) K) (d : ℕ) (x : Fin n → K) :
    eval (infinityVector x) (multivariateHomogenization f d) =
      eval x (homogeneousComponent d f) := by
  classical
  rw [multivariateHomogenization, map_sum, Finset.sum_eq_single d]
  · simp [infinityVector, eval_rename, Function.comp_def]
  · intro k hk hkd
    have hlt : k < d := by simp only [Finset.mem_range] at hk; omega
    simp [infinityVector, Nat.ne_of_gt (Nat.sub_pos_of_lt hlt)]
  · simp

/-- Separate a homogeneous cone into its nonzero first-coordinate chart
and its first-coordinate-zero part. The first chart is a product with Kˣ. -/
theorem homogenization_zero_card [Fintype K]
    (f : MvPolynomial (Fin n) K) (d : ℕ) (hd : f.totalDegree ≤ d) :
    Nat.card {x : Option (Fin n) → K //
      eval x (multivariateHomogenization f d) = 0} =
      (Fintype.card K - 1) * Nat.card {x : Fin n → K // eval x f = 0} +
        Nat.card {x : Fin n → K // eval x (homogeneousComponent d f) = 0} := by
  classical
  let A := {x : Fin n → K // eval x f = 0}
  let B := {x : Fin n → K // eval x (homogeneousComponent d f) = 0}
  let Z := {x : Option (Fin n) → K // eval x (multivariateHomogenization f d) = 0}
  have hs (a : K) (x : Fin n → K) :
      eval (a • affineChartVector x) (multivariateHomogenization f d) =
        a^d * eval x f := by
    have h := CubicGradientScaling.homogeneous_eval₂_smul
      (multivariateHomogenization f d) (multivariateHomogenization_isHomogeneous f d)
      (RingHom.id K) (affineChartVector x) a
    simpa only [eval₂_id, eval_affineChartVector_multivariateHomogenization f d hd x] using h
  let g : (Kˣ × A) ⊕ B → Z := fun t => match t with
    | Sum.inl z => ⟨(z.1 : K) • affineChartVector z.2.1, by rw [hs, z.2.2, mul_zero]⟩
    | Sum.inr z => ⟨infinityVector z.1, by rw [eval_at_infinity, z.2]⟩
  have hinj : Function.Injective g := by
    intro x y h
    have hv := congrArg Subtype.val h
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        have ha : x.1 = y.1 := Units.ext (by
          simpa [g, affineChartVector] using congrFun hv none)
        have hb : x.2 = y.2 := by
          apply Subtype.ext
          funext i
          have hi := congrFun hv (some i)
          simp only [g, Pi.smul_apply, smul_eq_mul, affineChartVector] at hi
          rw [ha] at hi
          exact mul_left_cancel₀ y.1.ne_zero hi
        exact congrArg Sum.inl (Prod.ext ha hb)
      | inr y =>
        have hz : (x.1 : K) = 0 := by
          simpa [g, affineChartVector, infinityVector] using congrFun hv none
        exact False.elim (x.1.ne_zero hz)
    | inr x =>
      cases y with
      | inl y =>
        have hz : (y.1 : K) = 0 := by
          simpa [g, affineChartVector, infinityVector] using (congrFun hv none).symm
        exact False.elim (y.1.ne_zero hz)
      | inr y =>
        congr 1
        apply Subtype.ext
        funext i
        exact congrFun hv (some i)
  have hsurj : Function.Surjective g := by
    intro z
    by_cases hz : z.1 none = 0
    · let x : Fin n → K := fun i => z.1 (some i)
      have hx : infinityVector x = z.1 := by
        funext i
        cases i <;> simp [infinityVector, x, hz]
      have hp : eval x (homogeneousComponent d f) = 0 := by
        rw [← eval_at_infinity, hx]
        exact z.2
      exact ⟨Sum.inr ⟨x,hp⟩, Subtype.ext hx⟩
    · let a : Kˣ := Units.mk0 (z.1 none) hz
      let x : Fin n → K := fun i => (z.1 none)⁻¹ * z.1 (some i)
      have hx : (a : K) • affineChartVector x = z.1 := by
        funext i
        cases i <;> simp [a, affineChartVector, x, mul_inv_cancel_left₀ hz]
      have hp : eval x f = 0 := by
        have hh := z.2
        rw [← hx, hs, mul_eq_zero] at hh
        exact hh.resolve_left (pow_ne_zero _ hz)
      exact ⟨Sum.inl (a,⟨x,hp⟩), Subtype.ext hx⟩
  have hcard := Nat.card_congr (Equiv.ofBijective g ⟨hinj,hsurj⟩)
  simpa only [Nat.card_sum, Nat.card_prod, Nat.card_eq_fintype_card,
    Fintype.card_sum, Fintype.card_prod, Fintype.card_units] using hcard.symm

/-- Renaming coordinates changes no literal number of zeros. -/
theorem zero_card_rename {σ τ : Type*} (e : σ ≃ τ) (F : MvPolynomial σ K) :
    Nat.card {x : τ → K // eval x (rename e F) = 0} =
      Nat.card {x : σ → K // eval x F = 0} := by
  let E : (τ → K) ≃ (σ → K) := e.symm.arrowCongr (Equiv.refl K)
  apply Nat.card_congr
  exact E.subtypeEquiv fun x => by
    have hE : E x = x ∘ e := by funext i; rfl
    rw [hE, eval_rename]

/-- The literal `Fin (n+1)` homogeneous closure has the expected chart count. -/
theorem closure_zero_card [Fintype K] (f : MvPolynomial (Fin n) K) :
    Literature.affineZeroCount (closure f) =
      (Fintype.card K - 1) * Nat.card {x : Fin n → K // eval x f = 0} +
      Nat.card {x : Fin n → K // eval x (homogeneousComponent f.totalDegree f) = 0} := by
  rw [Literature.affineZeroCount, closure, zero_card_rename]
  exact homogenization_zero_card f f.totalDegree le_rfl

/-- The top component of a nonzero polynomial is nonzero. -/
theorem topComponent_ne_zero (f : MvPolynomial (Fin n) K) (hf : f ≠ 0) :
    homogeneousComponent f.totalDegree f ≠ 0 := by
  classical
  obtain ⟨m, hm, he⟩ := Finset.exists_mem_eq_sup f.support
    (Finsupp.support_nonempty_iff.mpr hf) (fun m => m.sum fun _ e => e)
  have he' : m.degree = f.totalDegree := by
    simpa only [totalDegree, Finsupp.degree, Finsupp.weight] using he.symm
  intro hz
  have hh := congrArg (coeff m) hz
  rw [coeff_homogeneousComponent, if_pos he', coeff_zero] at hh
  exact (mem_support_iff.mp hm) hh

/-- An affine plane cubic contributes at most `3*q` cone points at infinity.
This coarse elementary bound suffices for the square-root affine estimate. -/
theorem infinity_zero_card_le [Fintype K]
    (f : MvPolynomial (Fin 2) K) (hd : f.totalDegree = 3) :
    Nat.card {x : Fin 2 → K // eval x (homogeneousComponent f.totalDegree f) = 0} ≤
      3 * Fintype.card K := by
  have hf : f ≠ 0 := by intro hz; simp [hz] at hd
  rw [FiniteFieldPolynomialZeros.natCard_zeros]
  have h := FiniteFieldPolynomialZeros.card_zeros_le_degree_mul
    (homogeneousComponent f.totalDegree f) (topComponent_ne_zero f hf) 3
    ((homogeneousComponent_isHomogeneous _ _).totalDegree_le.trans hd.le)
  simpa using h

/-- Numerical transfer from a squared homogeneous-cone estimate. The only
correction is the literal top-form zero count bounded above by `3*q`. -/
theorem affine_square_bound_of_closure [Fintype K]
    (f : MvPolynomial (Fin 2) K) (hd : f.totalDegree = 3) (C : ℝ)
    (hbound : ((Literature.affineZeroCount (closure f) : ℝ) -
        (Fintype.card K : ℝ)^2)^2 ≤
      C * ((Fintype.card K : ℝ)-1)^2 * (Fintype.card K : ℝ)) :
    ((Nat.card {x : Fin 2 → K // eval x f = 0} : ℝ) -
      (Fintype.card K : ℝ))^2 ≤ (2*C+32)*(Fintype.card K : ℝ) := by
  let q : ℝ := Fintype.card K
  let a : ℝ := Nat.card {x : Fin 2 → K // eval x f = 0}
  let t : ℝ := Nat.card {x : Fin 2 → K //
    eval x (homogeneousComponent f.totalDegree f) = 0}
  let D : ℝ := (Literature.affineZeroCount (closure f) : ℝ) - q^2
  have hq : 2 ≤ q := by
    dsimp [q]
    exact_mod_cast Nat.succ_le_of_lt (Fintype.one_lt_card : 1 < Fintype.card K)
  have ht0 : 0 ≤ t := Nat.cast_nonneg _
  have ht : t ≤ 3*q := by
    dsimp [t, q]
    exact_mod_cast infinity_zero_card_le f hd
  have hc := congrArg (fun m : ℕ => (m : ℝ)) (closure_zero_card f)
  simp only [Nat.cast_add, Nat.cast_mul,
    Nat.cast_sub (Nat.le_of_lt (Fintype.one_lt_card : 1 < Fintype.card K)),
    Nat.cast_one] at hc
  have heq : (q-1)*(a-q) = D+(q-t) := by dsimp [q,a,t,D]; nlinarith [hc]
  have hE : (q-t)^2 ≤ 4*q^2 := by
    nlinarith [mul_nonneg (show 0 ≤ (q-t)+2*q by linarith)
      (show 0 ≤ 2*q-(q-t) by linarith)]
  have hqq : 4*q^2 ≤ 16*(q-1)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ q-2 by linarith)
      (show 0 ≤ 3*q-2 by linarith)]
  have hE' : (q-t)^2 ≤ 16*(q-1)^2*q := by
    have hh := mul_le_mul_of_nonneg_left (show 1 ≤ q by linarith)
      (show 0 ≤ 16*(q-1)^2 by positivity)
    nlinarith
  have hb : D^2 ≤ C*(q-1)^2*q := hbound
  have hh : (q-1)^2*(a-q)^2 ≤ (q-1)^2*((2*C+32)*q) := by
    have heq2 := congrArg (fun x : ℝ => x^2) heq
    nlinarith [sq_nonneg (D-(q-t))]
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos (show 0 < q-1 by linarith))).mp hh

end CubicTenVariables.PlaneCurveHomogenization
