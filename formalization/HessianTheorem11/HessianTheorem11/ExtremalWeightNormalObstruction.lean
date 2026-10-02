import HessianTheorem11.RadialLimitKernel

/-! A general zero-weight Hessian obstruction: when the minimum-weight
space consists of the kernel and one radial direction, at most one
maximum-weight normal column can survive invertible unipotent transport. -/
noncomputable section
namespace HessianTheorem11
open Matrix MvPolynomial Module NonzeroLimitTransport
variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

theorem normal_card_le_one_of_extremal_weight_transport
    (G : MvPolynomial (Fin n) K) (hG : G.IsHomogeneous 3)
    (w : Fin n → ℤ) (radial : Fin n) (IL IN : Finset (Fin n))
    (hwr : w radial = -2) (hmin : ∀ i, -2 ≤ w i)
    (hwIL : ∀ i ∈ IL, w i = -2)
    (hminimum_only : ∀ i, w i = -2 → i ∈ IL ∨ i=radial)
    (hwIN : ∀ i ∈ IN, w i = 4)
    (hker : ∀ v, (hessian G (Pi.single radial 1)).mulVec v = 0 ↔
      ∀ i, i ∉ IL → v i = 0)
    (U : Matrix (Fin n) (Fin n) K) (hU : Function.Injective U.mulVec)
    (hupper : WeightUpperUnipotent w U)
    (htransport : zeroWeightPart G w = PolynomialRestriction.restrict U G) : IN.card ≤ 1 := by
  classical
  let H := hessian G (Pi.single radial 1)
  let H0 := hessian (zeroWeightPart G w) (Pi.single radial 1)
  have hrad : U.mulVec (Pi.single radial 1) = Pi.single radial 1 :=
    hupper.fixes_minimum_column radial (fun i => by rw [hwr]; exact hmin i)
  have hfix : ∀ v, H.mulVec v=0 → U.mulVec v=v := by
    intro v hv
    apply hupper.fixes_minimum_subspace
    intro j hj i
    have hjL : j ∈ IL := by
      by_contra hn
      exact hj ((hker v).mp hv j hn)
    rw [hwIL j hjL]
    exact hmin i
  have hcong : H0=U.transpose*H*U := by
    dsimp only [H0]
    rw [htransport, PolynomialRestriction.hessian_restrict, hrad]
  have hk0 : ∀ v, H0.mulVec v=0 ↔ ∀i,i∉IL→v i=0 := by
    intro v
    rw [hcong, matrix_congruence_kernel_of_fixed_kernel U H hU hfix]
    exact hker v
  have hIL : IL ⊆ INᶜ := by
    intro i hi
    apply Finset.mem_compl.mpr
    intro hn
    have h1 := hwIL i hi
    have h2 := hwIN i hn
    omega
  have h := normal_columns_card_le_one H0 INᶜ IL radial hIL (fun v => (hk0 v).mp) ?_
  · simpa using h
  intro i j hj hir
  have hjN : j ∈ IN := by simpa using hj
  by_cases hiL : i ∈ IL
  · have hi0 : H0.mulVec (Pi.single i 1)=0 := by
      apply (hk0 _).mpr
      intro k hk
      have hki : k ≠ i := by rintro rfl; exact hk hiL
      simp [hki]
    have he := congrFun hi0 j
    rw [Matrix.mulVec_single_one] at he
    have hs := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i j)
      (hessian_symmetric (zeroWeightPart G w) (Pi.single radial 1))
    exact hs.symm.trans he
  · by_contra hn
    have hw := hessian_coordinate_weight (zeroWeightPart G w)
      (zeroWeightPart_homogeneous hG w) w (zeroWeightPart_weights G w) radial i j hn
    rw [hwr, hwIN j hjN] at hw
    have hiw : w i = -2 := by omega
    exact (hminimum_only i hiw).elim hiL hir

end HessianTheorem11
