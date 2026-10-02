import CubicTenVariables.DeltaMethod
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Tail estimates for the literal scalar delta-method arcs. These estimates
will turn an exact full-line kernel identity into the required truncated
identity. No delta-method literature proposition is used. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.DeltaKernelTruncation
open MeasureTheory Set
open scoped BigOperators

theorem norm_integral_Ioi_le (f : ℝ → ℂ) (D T : ℝ) (hT : 0 < T)
    (N : ℕ) (hN : 1 ≤ N)
    (hb : ∀ x : ℝ, T < x → ‖f x‖ ≤ D*x^(-((N+1 : ℕ) : ℝ))) :
    ‖∫ x in Ioi T, f x‖ ≤ D/(N : ℝ)*T^(-(N : ℝ)) := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hp : -((N+1 : ℕ) : ℝ) < -1 := by push_cast; linarith
  have hi := (integrableOn_Ioi_rpow_of_lt hp hT).const_mul D
  calc
    _ ≤ ∫ x in Ioi T, D*x^(-((N+1 : ℕ) : ℝ)) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hb x hx
    _ = D/(N : ℝ)*T^(-(N : ℝ)) := by
      rw [integral_const_mul,integral_Ioi_rpow_of_lt hp hT]
      have he : -((N+1 : ℕ) : ℝ)+1 = -(N : ℝ) := by push_cast; ring
      rw [he]
      ring

theorem norm_integral_sub_Ioo_le (f : ℝ → ℂ) (hf : Integrable f)
    (D T : ℝ) (hT : 0 < T) (N : ℕ) (hN : 1 ≤ N)
    (hb : ∀ x : ℝ, T ≤ |x| → ‖f x‖ ≤ D*|x|^(-((N+1 : ℕ) : ℝ))) :
    ‖(∫ x, f x)-(∫ x in Ioo (-T) T, f x)‖ ≤
      (2*D/(N : ℝ))*T^(-(N : ℝ)) := by
  have hr : ‖∫ x in Ici T, f x‖ ≤ D/(N : ℝ)*T^(-(N : ℝ)) := by
    rw [integral_Ici_eq_integral_Ioi]
    apply norm_integral_Ioi_le f D T hT N hN
    intro x hx
    simpa only [abs_of_pos (hT.trans hx)] using hb x (by simpa [abs_of_pos (hT.trans hx)] using hx.le)
  have hl : ‖∫ x in Iic (-T), f x‖ ≤ D/(N : ℝ)*T^(-(N : ℝ)) := by
    rw [← integral_comp_neg_Ioi]
    apply norm_integral_Ioi_le (fun x => f (-x)) D T hT N hN
    intro x hx
    simpa only [abs_neg,abs_of_pos (hT.trans hx)] using
      hb (-x) (by simpa [abs_of_pos (hT.trans hx)] using hx.le)
  have hs : (Ioo (-T) T)ᶜ = Iic (-T) ∪ Ici T := by
    ext x
    simp only [mem_compl_iff,mem_Ioo,mem_union,mem_Iic,mem_Ici]
    simp only [not_and_or,not_lt]
  have hd : Disjoint (Iic (-T)) (Ici T) := by
    apply disjoint_left.mpr
    intro x hx hy
    have : T ≤ -T := hy.trans hx
    linarith
  rw [← integral_add_compl measurableSet_Ioo hf,add_sub_cancel_left,hs,
    setIntegral_union hd measurableSet_Ici hf.integrableOn hf.integrableOn]
  calc
    _ ≤ ‖∫ x in Iic (-T), f x‖+‖∫ x in Ici T, f x‖ := norm_add_le _ _
    _ ≤ D/(N : ℝ)*T^(-(N : ℝ))+D/(N : ℝ)*T^(-(N : ℝ)) := add_le_add hl hr
    _ = _ := by ring

theorem norm_integral_sub_scaled_Ioo_le (f : ℝ → ℂ) (hf : Integrable f)
    (C a η : ℝ) (hC : 0 ≤ C) (ha : 0 < a) (N : ℕ) (hN : 1 ≤ N)
    (hb : ∀ x : ℝ, ‖f x‖ ≤ C*(1+a*|x|)^(-((N+1 : ℕ) : ℝ))) :
    ‖(∫ x, f x)-(∫ x in Ioo (-(a^(-1+η))) (a^(-1+η)), f x)‖ ≤
      (2*C/(N : ℝ))/a*a^(-(N : ℝ)*η) := by
  have hT : 0 < a^(-1+η) := Real.rpow_pos_of_pos ha _
  have htail := norm_integral_sub_Ioo_le f hf (C*a^(-((N+1 : ℕ) : ℝ)))
    (a^(-1+η)) hT N hN (by
      intro x hx
      have hpos : 0 < a*|x| := mul_pos ha (hT.trans_le hx)
      have he : (1+a*|x|)^(-((N+1 : ℕ) : ℝ)) ≤
          (a*|x|)^(-((N+1 : ℕ) : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hpos (by linarith)
          (neg_nonpos.mpr (Nat.cast_nonneg (N+1)))
      calc
        _ ≤ C*(a*|x|)^(-((N+1 : ℕ) : ℝ)) :=
          (hb x).trans (mul_le_mul_of_nonneg_left he hC)
        _ = _ := by rw [Real.mul_rpow ha.le (abs_nonneg x)]; ring)
  have hpowers : a^(-((N+1 : ℕ) : ℝ))*(a^(-1+η))^(-(N : ℝ)) =
      a^(-(1 : ℝ))*a^(-(N : ℝ)*η) := by
    rw [← Real.rpow_mul ha.le,← Real.rpow_add ha,← Real.rpow_add ha]
    congr 1
    push_cast
    ring
  calc
    _ ≤ (2*(C*a^(-((N+1 : ℕ) : ℝ)))/(N : ℝ))*(a^(-1+η))^(-(N : ℝ)) := htail
    _ = (2*C/(N : ℝ))*(a^(-((N+1 : ℕ) : ℝ))*(a^(-1+η))^(-(N : ℝ))) := by ring
    _ = _ := by rw [hpowers,Real.rpow_neg_one]; ring

open DeltaMethod

/-- The untruncated arc, with exactly the same sign and numerator convention
as `DeltaMethod.deltaArc`. -/
def fullArc (p : ℕ → ℕ → ℝ → ℂ) (Q q a : ℕ) (m : ℤ) : ℂ :=
  ∫ θ, p Q q θ*realExponential (((a : ℝ)/(q : ℝ)+θ)*(m : ℝ))

def fullApproximation (p : ℕ → ℕ → ℝ → ℂ) (Q : ℕ) (m : ℤ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ Finset.Icc 1 q,
    if Nat.Coprime a q then fullArc p Q q a m else 0

theorem norm_fullArc_sub_deltaArc_le (p : ℕ → ℕ → ℝ → ℂ)
    (Q q a : ℕ) (η : ℝ) (m : ℤ) (hQ : 0 < Q) (hq : 0 < q)
    (C : ℝ) (hC : 0 ≤ C) (N : ℕ) (hN : 1 ≤ N)
    (hi : Integrable (p Q q))
    (hb : ∀ θ : ℝ, ‖p Q q θ‖ ≤ C*(1+(q : ℝ)*(Q : ℝ)*|θ|)^(-((N+1 : ℕ) : ℝ))) :
    ‖fullArc p Q q a m-deltaArc p Q q a η m‖ ≤
      (2*C/(N : ℝ))/((q : ℝ)*(Q : ℝ))*((q : ℝ)*(Q : ℝ))^(-(N : ℝ)*η) := by
  have he : Continuous (fun θ : ℝ =>
      realExponential (((a : ℝ)/(q : ℝ)+θ)*(m : ℝ))) := by
    unfold realExponential
    fun_prop
  have hf := hi.mul_bdd he.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun θ => (norm_realExponential _).le))
  simpa only [fullArc,deltaArc,arc_eq_Ioo] using
    norm_integral_sub_scaled_Ioo_le _ hf C ((q : ℝ)*(Q : ℝ)) η hC
      (by positivity) N hN (by
        intro θ
        simpa only [norm_mul,norm_realExponential,mul_one] using hb θ)

/-- The numerator count cancels the factor `q` in each arc tail, and the
denominator count cancels the remaining `Q`. The bound is uniform in the
integer phase, including zero and negative phases. -/
theorem norm_fullApproximation_sub_deltaApproximation_le
    (p : ℕ → ℕ → ℝ → ℂ) (Q : ℕ) (hQ : 1 ≤ Q) (η : ℝ) (hη : 0 < η)
    (m : ℤ) (C : ℝ) (hC : 0 ≤ C) (N : ℕ) (hN : 1 ≤ N)
    (hi : ∀ q ∈ Finset.Icc 1 Q, Integrable (p Q q))
    (hb : ∀ q ∈ Finset.Icc 1 Q, ∀ θ : ℝ,
      ‖p Q q θ‖ ≤ C*(1+(q : ℝ)*(Q : ℝ)*|θ|)^(-((N+1 : ℕ) : ℝ))) :
    ‖fullApproximation p Q m-deltaApproximation p Q η m‖ ≤
      (2*C/(N : ℝ))*(Q : ℝ)^(-(N : ℝ)*η) := by
  have hQpos : 0 < (Q : ℝ) := by exact_mod_cast (show 0 < Q by omega)
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  let B : ℝ := (2*C/(N : ℝ))/(Q : ℝ)*(Q : ℝ)^(-(N : ℝ)*η)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hterm (q : ℕ) (hq : q ∈ Finset.Icc 1 Q) (a : ℕ) :
      ‖fullArc p Q q a m-deltaArc p Q q a η m‖ ≤ B/(q : ℝ) := by
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hqpos : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
    have hqreal : 1 ≤ (q : ℝ) := by exact_mod_cast hq1
    have hpow : ((q : ℝ)*(Q : ℝ))^(-(N : ℝ)*η) ≤ (Q : ℝ)^(-(N : ℝ)*η) :=
      Real.rpow_le_rpow_of_nonpos hQpos (by nlinarith)
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hNpos.le) hη.le)
    calc
      _ ≤ (2*C/(N : ℝ))/((q : ℝ)*(Q : ℝ))*((q : ℝ)*(Q : ℝ))^(-(N : ℝ)*η) :=
        norm_fullArc_sub_deltaArc_le p Q q a η m (by omega) (by omega)
          C hC N hN (hi q hq) (hb q hq)
      _ ≤ (2*C/(N : ℝ))/((q : ℝ)*(Q : ℝ))*(Q : ℝ)^(-(N : ℝ)*η) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = B/(q : ℝ) := by dsimp [B]; field_simp
  unfold fullApproximation deltaApproximation
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, B := by
      apply norm_sum_le_of_le
      intro q hq
      rw [← Finset.sum_sub_distrib]
      have hqpos : 0 < (q : ℝ) := by
        exact_mod_cast (show 0 < q from lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hq).1)
      calc
        _ ≤ ∑ a ∈ Finset.Icc 1 q, B/(q : ℝ) := by
          apply norm_sum_le_of_le
          intro a _ha
          split_ifs with hcop
          · exact hterm q hq a
          · simp only [sub_zero,norm_zero]
            exact div_nonneg hB hqpos.le
        _ = B := by
          simp only [Finset.sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
          field_simp
    _ = _ := by
      simp only [Finset.sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
      dsimp [B]
      field_simp

/-- Exact full-line reconstruction and uniform rapid decay imply the literal
truncated delta estimate. Neither hypothesis is a theorem of this module:
both must be proved for the constructed kernel before using this adapter. -/
theorem delta_of_full_identity
    (p : ℕ → ℕ → ℝ → ℂ)
    (hi : ∀ Q, 2 ≤ Q → ∀ q, 1 ≤ q → q ≤ Q → Integrable (p Q q))
    (he : ∀ Q, 2 ≤ Q → ∀ m : ℤ, integerDelta m = fullApproximation p Q m)
    (hd : ∀ k : ℕ, 2 ≤ k → ∃ C : ℝ, 1 ≤ C ∧
      ∀ Q, 2 ≤ Q → ∀ q, 1 ≤ q → q ≤ Q → ∀ θ : ℝ,
        ‖p Q q θ‖ ≤ C*(1+(q : ℝ)*(Q : ℝ)*|θ|)^(-(k : ℝ))) :
    ∀ η : ℝ, 0 < η → ∀ N : ℕ, 1 ≤ N → ∃ C : ℝ, 1 ≤ C ∧
      ∀ Q, 2 ≤ Q → ∀ m : ℤ,
        ‖integerDelta m-deltaApproximation p Q η m‖ ≤ C*(Q : ℝ)^(-(N : ℝ)*η) := by
  intro η hη N hN
  obtain ⟨C,hC,hdecay⟩ := hd (N+1) (by omega)
  refine ⟨max 1 (2*C/(N : ℝ)),le_max_left _ _,?_⟩
  intro Q hQ m
  rw [he Q hQ m]
  apply (norm_fullApproximation_sub_deltaApproximation_le p Q (by omega) η hη m C
    (zero_le_one.trans hC) N hN
    (fun q hq => hi Q hQ q (Finset.mem_Icc.mp hq).1 (Finset.mem_Icc.mp hq).2)
    (fun q hq => hdecay Q hQ q (Finset.mem_Icc.mp hq).1 (Finset.mem_Icc.mp hq).2)).trans
  exact mul_le_mul_of_nonneg_right (le_max_right _ _)
    (Real.rpow_nonneg (Nat.cast_nonneg Q) _)

end CubicTenVariables.DeltaKernelTruncation
