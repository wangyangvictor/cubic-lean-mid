import HessianTheorem11.Polarization

/-! Trilinear expansion of the actual cubic tensor and cubic evaluations. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial

variable {K : Type*} [CommRing K] {n : ℕ}

theorem polarization_add_first (F : MvPolynomial (Fin n) K) (a b v w : Fin n → K) :
    polarization F (a+b) v w = polarization F a v w + polarization F b v w := by
  simp [polarization, add_dotProduct]

theorem polarization_smul_first (F : MvPolynomial (Fin n) K) (c : K) (u v w : Fin n → K) :
    polarization F (c • u) v w = c * polarization F u v w := by
  simp [polarization, smul_dotProduct, smul_eq_mul]

theorem polarization_add_second (F : MvPolynomial (Fin n) K) (u a b w : Fin n → K) :
    polarization F u (a+b) w = polarization F u a w + polarization F u b w := by
  simp [polarization, Matrix.mulVec_add, dotProduct_add]

theorem polarization_smul_second (F : MvPolynomial (Fin n) K) (c : K) (u v w : Fin n → K) :
    polarization F u (c • v) w = c * polarization F u v w := by
  simp [polarization, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem polarization_add_third {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous 3)
    (u v a b : Fin n → K) :
    polarization F u v (a+b) = polarization F u v a + polarization F u v b := by
  rw [polarization_swap_last hF, polarization_add_second,
    polarization_swap_last hF u a v, polarization_swap_last hF u b v]

theorem polarization_smul_third {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous 3)
    (c : K) (u v w : Fin n → K) :
    polarization F u v (c • w) = c * polarization F u v w := by
  rw [polarization_swap_last hF, polarization_smul_second, polarization_swap_last hF u w v]

@[simp] theorem polarization_zero_first (F : MvPolynomial (Fin n) K) (v w : Fin n → K) :
    polarization F 0 v w = 0 := by simp [polarization]

@[simp] theorem polarization_zero_second (F : MvPolynomial (Fin n) K) (u w : Fin n → K) :
    polarization F u 0 w = 0 := by simp [polarization]

@[simp] theorem polarization_zero_third {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous 3)
    (u v : Fin n → K) : polarization F u v 0 = 0 := by
  rw [polarization_swap_last hF, polarization_zero_second]

theorem polarization_sum_first {ι : Type*} (s : Finset ι)
    (F : MvPolynomial (Fin n) K) (u : ι → Fin n → K) (v w : Fin n → K) :
    polarization F (∑ i ∈ s, u i) v w = ∑ i ∈ s, polarization F (u i) v w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert hi, polarization_add_first, ih]

theorem polarization_sum_second {ι : Type*} (s : Finset ι)
    (F : MvPolynomial (Fin n) K) (u : Fin n → K) (v : ι → Fin n → K) (w : Fin n → K) :
    polarization F u (∑ i ∈ s, v i) w = ∑ i ∈ s, polarization F u (v i) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert hi, polarization_add_second, ih]

theorem polarization_sum_third {ι : Type*} (s : Finset ι)
    {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous 3)
    (u v : Fin n → K) (w : ι → Fin n → K) :
    polarization F u v (∑ i ∈ s, w i) = ∑ i ∈ s, polarization F u v (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polarization_zero_third hF]
  | @insert i s hi ih => simp [Finset.sum_insert hi, polarization_add_third hF, ih]

section Field
variable {L : Type*} [Field L] [CharZero L]

theorem eval_cubic_eq_polarization {F : MvPolynomial (Fin n) L}
    (hF : F.IsHomogeneous 3) (u : Fin n → L) :
    eval u F = (1/6 : L) * polarization F u u u := by
  unfold polarization
  rw [hessian_cubic_identity hF]
  ring

theorem eval_cubic_add {F : MvPolynomial (Fin n) L}
    (hF : F.IsHomogeneous 3) (u v : Fin n → L) :
    eval (u+v) F = eval u F + eval v F +
      (1/2 : L) * polarization F u u v + (1/2 : L) * polarization F u v v := by
  simp only [eval_cubic_eq_polarization hF, polarization_add_first,
    polarization_add_second, polarization_add_third hF]
  rw [polarization_swap_last hF u v u, polarization_swap_first F v u u,
    polarization_swap_first F v u v, polarization_rotate hF v v u]
  rw [polarization_swap_last hF u v u]
  ring

end Field
end HessianTheorem11
