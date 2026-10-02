import HessianTheorem11.SingularRadial
import HessianTheorem11.PolarizationExpansion

/-! An additional common radical direction in a singular tangent space
admits weight −8. This strengthens the actual radial inequality and is the
weight obstruction used in the three- and four-coordinate normal-span cases. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Module

def singularExtraWeight {n : ℕ} (radial extra : Fin n) (T : Finset (Fin n))
    (i : Fin n) : ℤ := singularRadialWeight radial T T i - if i = extra then 6 else 0

theorem sum_singularExtraWeight {n : ℕ} (radial extra : Fin n) (T : Finset (Fin n)) :
    ∑ i, singularExtraWeight radial extra T i = 4 * (n : ℤ) - 6 * (T.card : ℤ) - 12 := by
  simp only [singularExtraWeight, Finset.sum_sub_distrib, sum_singularRadialWeight]
  simp
  ring

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

theorem singularExtraWeight_nonnegative_tensor
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (b : Basis (Fin n) K (Fin n → K)) (radial extra : Fin n) (T : Finset (Fin n))
    (hr : radial ∈ T) (he : extra ∈ T) (her : extra ≠ radial)
    (hkernel : ∀ i ∈ T, (hessian F (b radial)).mulVec (b i) = 0)
    (htangent : ∀ i ∈ T, ∀ j ∈ T, ∀ k ∈ T, polarization F (b i) (b j) (b k) = 0)
    (hextra : ∀ j ∈ T, ∀ k, polarization F (b extra) (b j) (b k) = 0)
    (i j k : Fin n) (hne : polarization F (b i) (b j) (b k) ≠ 0) :
    0 ≤ singularExtraWeight radial extra T i + singularExtraWeight radial extra T j +
      singularExtraWeight radial extra T k := by
  have hwextra : singularExtraWeight radial extra T extra = -8 := by
    simp [singularExtraWeight, singularRadialWeight, her, he]
  have hwnormal (j : Fin n) (hj : j ∉ T) : singularExtraWeight radial extra T j = 4 := by
    have hje : j ≠ extra := by rintro rfl; exact hj he
    simp [singularExtraWeight, hje, singularRadialWeight_normal hr (Finset.Subset.refl T) hj]
  have hw (j k : Fin n) (h : polarization F (b extra) (b j) (b k) ≠ 0) :
      singularExtraWeight radial extra T j = 4 ∧ singularExtraWeight radial extra T k = 4 := by
    have hj : j ∉ T := fun hj => h (hextra j hj k)
    have hk : k ∉ T := by
      intro hk
      apply h
      rw [polarization_swap_last hF]
      exact hextra k hk j
    exact ⟨hwnormal j hj, hwnormal k hk⟩
  by_cases hie : i = extra
  · subst i
    obtain ⟨hj,hk⟩ := hw j k hne
    rw [hwextra,hj,hk]
    norm_num
  by_cases hje : j = extra
  · subst j
    have h : polarization F (b extra) (b i) (b k) ≠ 0 := by
      rwa [polarization_swap_first]
    obtain ⟨hi,hk⟩ := hw i k h
    rw [hi,hwextra,hk]
    norm_num
  by_cases hke : k = extra
  · subst k
    have h : polarization F (b extra) (b i) (b j) ≠ 0 := by
      intro hz
      apply hne
      rw [polarization_rotate hF]
      exact hz
    obtain ⟨hi,hj⟩ := hw i j h
    rw [hi,hj,hwextra]
    norm_num
  simpa only [singularExtraWeight, hie, hje, hke, if_false, sub_zero] using
    singularRadialWeight_nonnegative_tensor F hF b radial T T hr (Finset.Subset.refl T)
      hkernel htangent i j k hne

/-- The common radical contains the radial line. If it has any additional
direction, semistability forces this stronger dimension bound. -/
theorem singular_extra_radical_dimension_bound
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3) (hsemi : WeightSemistable F)
    (x : Fin n → K) (hx : x ≠ 0) (S T : Submodule K (Fin n → K))
    (hST : S ≤ T) (hxS : x ∈ S) (hSdim : 2 ≤ finrank K S)
    (hkernel : ∀ t ∈ T, (hessian F x).mulVec t = 0)
    (htangent : ∀ u ∈ T, ∀ v ∈ T, ∀ w ∈ T, polarization F u v w = 0)
    (hcommon : ∀ u ∈ S, ∀ v ∈ T, ∀ w, polarization F u v w = 0) :
    3 * finrank K T + 6 ≤ 2 * n := by
  classical
  let A := adaptedFlagBasis S T hST x hx hxS
  have hsCard : 1 < A.tangentIndices.card := by rw [A.tangent_card]; omega
  obtain ⟨extra,he,her⟩ := Finset.exists_mem_ne hsCard A.radial
  have heT := A.indices_nested he
  have hrT := A.indices_nested A.radial_mem
  let w := singularExtraWeight A.radial extra A.kernelIndices
  have hw : 0 ≤ ∑ i, w i := by
    apply hsemi.nonnegative_weight_sum_of_thirdPartials hF
      (basisMatrix A.basis) (basisMatrix_injective A.basis) w
    intro i j k hne
    change coeff 0 (pderiv k (pderiv j (pderiv i
      (PolynomialRestriction.restrict (basisMatrix A.basis) F)))) ≠ 0 at hne
    rw [polarization_in_coordinates F hF] at hne
    apply singularExtraWeight_nonnegative_tensor F hF A.basis A.radial extra A.kernelIndices
      hrT heT her _ _ _ i j k hne
    · intro a ha
      rw [A.radial_eq]
      exact hkernel _ ((A.mem_kernel_iff a).mpr ha)
    · intro a ha b hb c hc
      exact htangent _ ((A.mem_kernel_iff a).mpr ha) _ ((A.mem_kernel_iff b).mpr hb)
        _ ((A.mem_kernel_iff c).mpr hc)
    · intro a ha c
      exact hcommon _ ((A.mem_tangent_iff extra).mpr he)
        _ ((A.mem_kernel_iff a).mpr ha) _
  change 0 ≤ ∑ i, singularExtraWeight A.radial extra A.kernelIndices i at hw
  rw [sum_singularExtraWeight, A.kernel_card] at hw
  omega

/-- Actual common radical of all polarized normal quadrics on `T`. -/
def singularNormalCommonRadical (F : MvPolynomial (Fin n) K)
    (T : Submodule K (Fin n → K)) : Submodule K (Fin n → K) where
  carrier := {u | u ∈ T ∧ ∀ v ∈ T, ∀ w, polarization F u v w = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    refine ⟨T.add_mem ha.1 hb.1, ?_⟩
    intro v hv w
    rw [polarization_add_first, ha.2 v hv w, hb.2 v hv w, add_zero]
  smul_mem' := by
    intro c a ha
    refine ⟨T.smul_mem c ha.1, ?_⟩
    intro v hv w
    rw [polarization_smul_first, ha.2 v hv w, mul_zero]

theorem singularNormalCommonRadical_finrank_le_one
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3) (hsemi : WeightSemistable F)
    (x : Fin n → K) (hx : x ≠ 0) (T : Submodule K (Fin n → K)) (hxT : x ∈ T)
    (hkernel : ∀ t ∈ T, (hessian F x).mulVec t = 0)
    (htangent : ∀ u ∈ T, ∀ v ∈ T, ∀ w ∈ T, polarization F u v w = 0)
    (hdim : 2 * n < 3 * finrank K T + 6) :
    finrank K (singularNormalCommonRadical F T) ≤ 1 := by
  by_contra hh
  have hxS : x ∈ singularNormalCommonRadical F T := by
    refine ⟨hxT, ?_⟩
    intro v hv w
    rw [polarization_rotate hF, polarization_swap_last hF]
    change dotProduct w ((hessian F x).mulVec v) = 0
    rw [hkernel v hv]
    simp
  have hb := singular_extra_radical_dimension_bound F hF hsemi x hx
    (singularNormalCommonRadical F T) T (fun _ hu => hu.1) hxS (by omega)
    hkernel htangent (fun _ hu => hu.2)
  omega

end HessianTheorem11
