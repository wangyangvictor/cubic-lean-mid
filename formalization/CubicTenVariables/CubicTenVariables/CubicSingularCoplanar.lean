import CubicTenVariables.CubicSingularCollinear
import Mathlib.Algebra.MvPolynomial.Division

/-! Concrete coplanarity obstruction: three coordinate singular zeros in a
plane leave only the product of its coordinates. A fourth zero off all three
coordinate lines forces the restriction to vanish identically. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.CubicSingularCoplanar
open MvPolynomial HessianTheorem11 Module
open PolynomialRestriction PlaneCubicSingularGeometry
open scoped BigOperators
variable {K : Type*} [Field K] [IsAlgClosed K]

private theorem coordinate_dvd_of_vanishes {n : ℕ}
    (F : MvPolynomial (Fin n) K) (i : Fin n)
    (hz : ∀ x : Fin n → K, x i = 0 → eval x F = 0) : X i ∣ F := by
  let I : Ideal (MvPolynomial (Fin n) K) := Ideal.span {X i}
  have hp : I.IsPrime := (Ideal.span_singleton_prime (X_ne_zero i)).mpr X_prime
  letI := hp
  have hm : F ∈ vanishingIdeal K (zeroLocus K I) := by
    intro x hx
    apply hz x
    have h := hx (X i) (Ideal.subset_span (Set.mem_singleton _))
    simpa only [aeval_X] using h
  rw [IsPrime.vanishingIdeal_zeroLocus] at hm
  exact Ideal.mem_span_singleton.mp hm

/-- Three actual coordinate singular zeros of a ternary cubic force the
literal form cXYZ. The coefficient may be zero. -/
theorem eq_coordinate_product_of_three_singular
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3)
    (hz : ∀ i : Fin 3, eval (Pi.single i 1) F = 0)
    (hg : ∀ i : Fin 3, HessianTheorem11.gradient F (Pi.single i 1) = 0) :
    ∃ c : K, F = C c * X 0 * X 1 * X 2 := by
  have hdiv (i : Fin 3) : X i ∣ F := by
    apply coordinate_dvd_of_vanishes F i
    intro x hx
    fin_cases i
    · have he : x = x 1 • (Pi.single 1 (1 : K) : Fin 3 → K) + x 2 • (Pi.single 2 (1 : K) : Fin 3 → K) := by
        ext j; fin_cases j <;> simp_all [Pi.smul_apply,smul_eq_mul]
      rw [he]
      exact eval_singular_span F hF _ _ (hz 1) (hg 1) (hz 2) (hg 2) _ _
    · have he : x = x 0 • (Pi.single 0 (1 : K) : Fin 3 → K) + x 2 • (Pi.single 2 (1 : K) : Fin 3 → K) := by
        ext j; fin_cases j <;> simp_all [Pi.smul_apply,smul_eq_mul]
      rw [he]
      exact eval_singular_span F hF _ _ (hz 0) (hg 0) (hz 2) (hg 2) _ _
    · have he : x = x 0 • (Pi.single 0 (1 : K) : Fin 3 → K) + x 1 • (Pi.single 1 (1 : K) : Fin 3 → K) := by
        ext j; fin_cases j <;> simp_all [Pi.smul_apply,smul_eq_mul]
      rw [he]
      exact eval_singular_span F hF _ _ (hz 0) (hg 0) (hz 1) (hg 1) _ _
  by_cases hF0 : F = 0
  · exact ⟨0,by simp [hF0]⟩
  obtain ⟨A,hA⟩ := hdiv 0
  have h1 : X (1 : Fin 3) ∣ A := by
    have h := hdiv 1
    rw [hA,X_dvd_mul_iff] at h
    exact h.resolve_left (by simp)
  obtain ⟨B,hB⟩ := h1
  have h2 : X (2 : Fin 3) ∣ B := by
    have h := hdiv 2
    rw [hA,hB,X_dvd_mul_iff,X_dvd_mul_iff] at h
    simpa using h
  obtain ⟨G,hG⟩ := h2
  have he : F = X 0 * (X 1 * (X 2 * G)) := by rw [hA,hB,hG]
  have hG0 : G ≠ 0 := by intro h; simp [h] at he; exact hF0 he
  have hdeg : G.totalDegree = 0 := by
    have hd := hF.totalDegree hF0
    have h2 : (X (2 : Fin 3) : MvPolynomial (Fin 3) K) * G ≠ 0 :=
      mul_ne_zero (X_ne_zero _) hG0
    have h12 : (X (1 : Fin 3) : MvPolynomial (Fin 3) K) * (X 2 * G) ≠ 0 :=
      mul_ne_zero (X_ne_zero _) h2
    rw [he,totalDegree_mul_of_isDomain (X_ne_zero _) h12,
      totalDegree_mul_of_isDomain (X_ne_zero _) h2,
      totalDegree_mul_of_isDomain (X_ne_zero _) hG0] at hd
    simp only [totalDegree_X] at hd
    omega
  refine ⟨G.coeff 0,?_⟩
  conv_lhs => rw [he,totalDegree_eq_zero_iff_eq_C.mp hdeg]
  ring

/-- A fourth plane zero with all three coordinates nonzero forces the
entire ternary cubic to be zero. The fourth point need not be singular. -/
theorem eq_zero_of_fourth_zero
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3)
    (hz : ∀ i : Fin 3, eval (Pi.single i 1) F = 0)
    (hg : ∀ i : Fin 3, HessianTheorem11.gradient F (Pi.single i 1) = 0)
    (x : Fin 3 → K) (hx : ∀ i, x i ≠ 0) (hFx : eval x F = 0) : F = 0 := by
  obtain ⟨c,he⟩ := eq_coordinate_product_of_three_singular F hF hz hg
  have hc : c = 0 := by
    rw [he] at hFx
    simpa only [map_mul,eval_C,eval_X,mul_eq_zero,hx,or_false] using hFx
  simp only [he,hc,map_zero,zero_mul]

/-- Literal matrix-coordinate coplanarity bridge for an ambient cubic. -/
theorem restrict_eq_zero_of_four_singular_columns {n : ℕ}
    (B : Matrix (Fin n) (Fin 3) K) (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous 3)
    (hz : ∀ i : Fin 3, eval (B.mulVec (Pi.single i 1)) F = 0)
    (hg : ∀ i : Fin 3, HessianTheorem11.gradient F (B.mulVec (Pi.single i 1)) = 0)
    (x : Fin 3 → K) (hx : ∀ i, x i ≠ 0) (hFx : eval (B.mulVec x) F = 0) :
    restrict B F = 0 := by
  refine eq_zero_of_fourth_zero _ (homogeneous_restrict B F hF) ?_ ?_ x hx ?_
  · intro i
    simpa only [eval_restrict] using hz i
  · intro i
    ext j
    simp only [HessianTheorem11.gradient,pderiv_restrict,map_sum,map_mul,eval_restrict]
    have hh (a : Fin n) : eval (B.mulVec (Pi.single i 1)) (pderiv a F) = 0 :=
      congrFun (hg i) a
    simp only [hh,zero_mul,Finset.sum_const_zero,Pi.zero_apply]
  · simpa only [eval_restrict] using hFx


/-- An integral cubic surface cannot have four coplanar singular points
in plane general position. The independent plane frame is supplied literally
by B, and the fourth point has three nonzero plane coordinates. -/
theorem not_fourth_zero_of_independent_singular_columns
    (B : Matrix (Fin 4) (Fin 3) K) (hB : Function.Injective B.mulVec)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (hz : ∀ i : Fin 3, eval (B.mulVec (Pi.single i 1)) F = 0)
    (hg : ∀ i : Fin 3, HessianTheorem11.gradient F (B.mulVec (Pi.single i 1)) = 0)
    (x : Fin 3 → K) (hx : ∀ i, x i ≠ 0) : eval (B.mulVec x) F ≠ 0 := by
  intro hFx
  have hr := restrict_eq_zero_of_four_singular_columns B F hF hz hg x hx hFx
  let W : Submodule K (Fin 4 → K) := LinearMap.range B.mulVecLin
  have hWd : finrank K W = 3 := by
    dsimp only [W]
    rw [LinearMap.finrank_range_of_inj hB]
    simp only [Module.finrank_pi,Fintype.card_fin]
  have hWlt : W < ⊤ := Submodule.lt_top_of_finrank_lt_finrank (by
    simpa only [hWd,Module.finrank_pi,Fintype.card_fin] using (by decide : 3 < 4))
  obtain ⟨f,hf,hWf⟩ := W.exists_le_ker_of_lt_top hWlt
  have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  have hWeq : W = LinearMap.ker f := Submodule.eq_of_le_of_finrank_eq hWf (by
    simp only [Module.finrank_pi,Fintype.card_fin] at hker
    omega)
  have hd := degree_le_one_of_vanishes_on_hyperplane F hirr f hf (by
    intro y hy
    have hyW : y ∈ W := hWeq ▸ hy
    obtain ⟨v,rfl⟩ := hyW
    have he := congrArg (eval v) hr
    simpa only [eval_restrict,map_zero,Matrix.mulVecLin_apply] using he)
  rw [hF.totalDegree hirr.ne_zero] at hd
  omega

end CubicTenVariables.CubicSingularCoplanar
