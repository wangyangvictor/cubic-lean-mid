import HessianTheorem11.SmoothRadialDefect
import HessianTheorem11.PolarizationExpansion

/-! The common annihilator of the quadratic forms on a Hessian kernel.
A strengthened radial weighting bounds its actual linear dimension. In the
thirteen-variable incidence equality case the annihilator is exactly the
tangent space, which is the independence of the normal quadrics. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Module

/-- The common annihilator of the polarized quadrics on a subspace. -/
def kernelQuadraticAnnihilator {K : Type*} [Field K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (L : Submodule K (Fin n → K)) :
    Submodule K (Fin n → K) where
  carrier := {v | ∀ u ∈ L, ∀ w ∈ L, polarization F v u w = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb u hu w hw
    rw [polarization_add_first, ha u hu w hw, hb u hu w hw, add_zero]
  smul_mem' := by
    intro a v hv u hu w hw
    rw [polarization_smul_first, hv u hu w hw, mul_zero]

def liftedRadialWeight {n : ℕ} (radial : Fin n) (IS IL : Finset (Fin n))
    (i : Fin n) : ℤ :=
  8 - (if i ∈ IS then 6 else 0) - (if i ∈ IL then 6 else 0) -
    (if i = radial then 3 else 0)

theorem sum_liftedRadialWeight {n : ℕ} (radial : Fin n) (IS IL : Finset (Fin n)) :
    ∑ i, liftedRadialWeight radial IS IL i =
      8 * (n : ℤ) - 6 * (IS.card : ℤ) - 6 * (IL.card : ℤ) - 3 := by
  classical
  unfold liftedRadialWeight
  simp only [Finset.sum_sub_distrib]
  have hs : (∑ i : Fin n, if i ∈ IS then (6 : ℤ) else 0) = 6 * IS.card := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  have hl : (∑ i : Fin n, if i ∈ IL then (6 : ℤ) else 0) = 6 * IL.card := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  rw [hs, hl]
  simp
  ring

private theorem liftedRadialWeight_nonnegative_without_radial
    {n : ℕ} {radial i j k : Fin n} {IS IL : Finset (Fin n)}
    (hir : i ≠ radial) (hjr : j ≠ radial) (hkr : k ≠ radial)
    (hi : i ∈ IS → j ∈ IL → k ∈ IL → False)
    (hj : j ∈ IS → i ∈ IL → k ∈ IL → False)
    (hk : k ∈ IS → i ∈ IL → j ∈ IL → False) :
    0 ≤ liftedRadialWeight radial IS IL i + liftedRadialWeight radial IS IL j +
      liftedRadialWeight radial IS IL k := by
  by_cases hiS : i ∈ IS <;> by_cases hiL : i ∈ IL <;>
    by_cases hjS : j ∈ IS <;> by_cases hjL : j ∈ IL <;>
    by_cases hkS : k ∈ IS <;> by_cases hkL : k ∈ IL <;>
    simp_all [liftedRadialWeight]

private theorem liftedRadialWeight_outside_kernel
    {n : ℕ} {radial i : Fin n} {IS IL : Finset (Fin n)} (hiL : i ∉ IL) :
    -1 ≤ liftedRadialWeight radial IS IL i := by
  unfold liftedRadialWeight
  split_ifs <;> omega

private theorem liftedRadialWeight_outside_kernel_radial
    {n : ℕ} {radial i : Fin n} {IS IL : Finset (Fin n)}
    (hiL : i ∉ IL) (hir : i ≠ radial) :
    2 ≤ liftedRadialWeight radial IS IL i := by
  unfold liftedRadialWeight
  split_ifs <;> omega

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

theorem liftedRadialWeight_nonnegative_tensor
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (b : Basis (Fin n) K (Fin n → K)) (radial : Fin n) (IS IL : Finset (Fin n))
    (hrS : radial ∈ IS) (hrL : radial ∉ IL)
    (hkernel : ∀ i ∈ IL, (hessian F (b radial)).mulVec (b i) = 0)
    (hann : ∀ i ∈ IS, ∀ j ∈ IL, ∀ k ∈ IL,
      polarization F (b i) (b j) (b k) = 0)
    (hzero : polarization F (b radial) (b radial) (b radial) = 0)
    (i j k : Fin n) (hne : polarization F (b i) (b j) (b k) ≠ 0) :
    0 ≤ liftedRadialWeight radial IS IL i + liftedRadialWeight radial IS IL j +
      liftedRadialWeight radial IS IL k := by
  have hrad : liftedRadialWeight radial IS IL radial = -1 := by
    simp [liftedRadialWeight, hrS, hrL]
  have hradzero (a c : Fin n) (ha : a ∈ IL) :
      polarization F (b radial) (b a) (b c) = 0 := by
    rw [polarization_rotate hF, polarization_swap_last hF]
    change dotProduct (b c) ((hessian F (b radial)).mulVec (b a)) = 0
    rw [hkernel a ha]
    simp
  have hradweights (a c : Fin n)
      (h : polarization F (b radial) (b a) (b c) ≠ 0) :
      0 ≤ liftedRadialWeight radial IS IL radial + liftedRadialWeight radial IS IL a +
        liftedRadialWeight radial IS IL c := by
    have haL : a ∉ IL := fun ha => h (hradzero a c ha)
    have hcL : c ∉ IL := by
      intro hc
      apply h
      rw [polarization_swap_last hF]
      exact hradzero c a hc
    rw [hrad]
    by_cases har : a = radial
    · subst a
      have hcr : c ≠ radial := by rintro rfl; exact h hzero
      have hc := liftedRadialWeight_outside_kernel_radial (IS := IS) hcL hcr
      rw [hrad]
      omega
    · have ha := liftedRadialWeight_outside_kernel_radial (IS := IS) haL har
      have hc := liftedRadialWeight_outside_kernel (radial := radial) (IS := IS) hcL
      omega
  by_cases hir : i = radial
  · subst i
    exact hradweights j k hne
  by_cases hjr : j = radial
  · subst j
    have h := hradweights i k (by rwa [polarization_swap_first])
    omega
  by_cases hkr : k = radial
  · subst k
    have h := hradweights i j (by
      intro hz
      apply hne
      rw [polarization_rotate hF]
      exact hz)
    omega
  apply liftedRadialWeight_nonnegative_without_radial hir hjr hkr
  · intro hi hj hk
    exact hne (hann i hi j hj k hk)
  · intro hj hi hk
    apply hne
    rw [polarization_swap_first]
    exact hann j hj i hi k hk
  · intro hk hi hj
    apply hne
    rw [polarization_rotate hF]
    exact hann k hk i hi j hj

/-- A stronger radial bound for every subspace annihilating the kernel
quadrics, derived from a simultaneous basis and actual cubic support. -/
theorem kernel_quadratic_annihilator_dimension_bound
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (hsemi : WeightSemistable F) (x : Fin n → K) (hx : eval x F = 0)
    (S : Submodule K (Fin n → K)) (hxS : x ∈ S)
    (hxL : x ∉ LinearMap.ker (hessian F x).mulVecLin)
    (hann : S ≤ kernelQuadraticAnnihilator F (LinearMap.ker (hessian F x).mulVecLin)) :
    6 * ((finrank K S : ℤ) +
      (finrank K (LinearMap.ker (hessian F x).mulVecLin) : ℤ)) + 3 ≤ 8 * (n : ℤ) := by
  let L := LinearMap.ker (hessian F x).mulVecLin
  let A := simultaneousSubspaceBasis S L x hxS hxL
  have hkernel (i : Fin n) (hi : i ∈ A.kernelIndices) :
      (hessian F (A.basis A.radial)).mulVec (A.basis i) = 0 := by
    rw [A.radial_eq]
    exact (A.mem_kernel_iff i).mpr hi
  have htensor (i : Fin n) (hi : i ∈ A.tangentIndices)
      (j : Fin n) (hj : j ∈ A.kernelIndices) (k : Fin n) (hk : k ∈ A.kernelIndices) :
      polarization F (A.basis i) (A.basis j) (A.basis k) = 0 :=
    hann ((A.mem_tangent_iff i).mpr hi) _ ((A.mem_kernel_iff j).mpr hj)
      _ ((A.mem_kernel_iff k).mpr hk)
  have hz : polarization F (A.basis A.radial) (A.basis A.radial) (A.basis A.radial) = 0 := by
    rw [A.radial_eq]
    change dotProduct x ((hessian F x).mulVec x) = 0
    rw [hessian_cubic_identity hF, hx, mul_zero]
  have hnonneg : 0 ≤ ∑ i, liftedRadialWeight A.radial A.tangentIndices A.kernelIndices i := by
    apply hsemi.nonnegative_weight_sum_of_thirdPartials hF (basisMatrix A.basis)
      (basisMatrix_injective A.basis)
    intro i j k hne
    change coeff 0 (pderiv k (pderiv j (pderiv i
      (PolynomialRestriction.restrict (basisMatrix A.basis) F)))) ≠ 0 at hne
    rw [polarization_in_coordinates F hF] at hne
    exact liftedRadialWeight_nonnegative_tensor F hF A.basis A.radial
      A.tangentIndices A.kernelIndices A.radial_mem_tangent A.radial_notMem_kernel
      hkernel htensor hz i j k hne
  rw [sum_liftedRadialWeight, A.tangent_card, A.kernel_card] at hnonneg
  change 0 ≤ 8 * (n : ℤ) - 6 * (finrank K S : ℤ) -
    6 * (finrank K (LinearMap.ker (hessian F x).mulVecLin) : ℤ) - 3 at hnonneg
  omega

/-- At incidence dimension sixteen in thirteen variables the common
annihilator of the actual kernel quadrics equals the tangent subspace. This
is normal-quadrics independence, without assuming any normal form. -/
theorem kernel_quadratic_annihilator_eq_of_thirteen
    (F : MvPolynomial (Fin 13) K) (hF : F.IsHomogeneous 3)
    (hsemi : WeightSemistable F) (x : Fin 13 → K) (hx : eval x F = 0)
    (T : Submodule K (Fin 13 → K)) (hxT : x ∈ T)
    (hxL : x ∉ LinearMap.ker (hessian F x).mulVecLin)
    (hann : T ≤ kernelQuadraticAnnihilator F (LinearMap.ker (hessian F x).mulVecLin))
    (hdim : finrank K T + finrank K (LinearMap.ker (hessian F x).mulVecLin) = 16) :
    kernelQuadraticAnnihilator F (LinearMap.ker (hessian F x).mulVecLin) = T := by
  let S := kernelQuadraticAnnihilator F (LinearMap.ker (hessian F x).mulVecLin)
  have hb := kernel_quadratic_annihilator_dimension_bound F hF hsemi x hx S
    (hann hxT) hxL le_rfl
  have hle := Submodule.finrank_mono hann
  have heq : finrank K T = finrank K S := by
    change finrank K T ≤ finrank K S at hle
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hann heq).symm

end HessianTheorem11
