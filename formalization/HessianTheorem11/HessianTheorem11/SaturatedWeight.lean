import HessianTheorem11.SaturatedPolynomialExtension
import HessianTheorem11.BasisWeightSum

/-! The explicit lowered radial weight used when the mixed middle block
vanishes. The support check uses the actual cubic tensor and constructed basis. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Module
namespace CoisotropicBasis.Data
variable {n m d q : ℕ} {F : GeometricPolynomial n} {x : GeometricPoint n}
  {T : Submodule GeometricField (GeometricPoint n)}
  (D : Data (hessianBilinear F x) T x m d q)

def loweredRadialWeight : CoisotropicBasis.Index m d q → ℤ :=
  Sum.elim (fun _ => -2)
    (Sum.elim (fun _ => 1) (Sum.elim (fun i => if i=D.radial then -2 else 0) (fun _ => 4)))

theorem sum_loweredRadialWeight : ∑ i, D.loweredRadialWeight i =
    -2*(m : ℤ) + (q : ℤ) - 2 + 4*(d : ℤ) := by
  classical
  simp [loweredRadialWeight, Fintype.sum_sum_type, Finset.sum_ite_eq', mul_comm]
  ring

theorem loweredRadialWeight_radial_tensor (hF : F.IsHomogeneous 3)
    (i j : CoisotropicBasis.Index m d q)
    (hne : polarization F x (D.basis i) (D.basis j) ≠ 0) :
    0 ≤ -2 + D.loweredRadialWeight i + D.loweredRadialWeight j := by
  classical
  rw [polarization_swap_first, polarization_swap_last hF] at hne
  change D.gramAt x i j ≠ 0 at hne
  rw [D.gramAt_base, D.complementGramAt_base] at hne
  rcases i with i | (i | (i | i)) <;> rcases j with j | (j | (j | j)) <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply] at hne
  all_goals try contradiction
  all_goals simp only [loweredRadialWeight, Sum.elim_inl, Sum.elim_inr]
  all_goals (try split_ifs) <;> norm_num

set_option maxHeartbeats 2000000 in
theorem loweredRadialWeight_nonnegative_tensor (hF : F.IsHomogeneous 3)
    (hker : LinearMap.ker (hessian F x).mulVecLin ≤ T)
    (hann : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0)
    (hC : ∀ a ∈ LinearMap.ker (hessian F x).mulVecLin, D.isotropicGramAt a = 0)
    (hE : ∀ a ∈ LinearMap.ker (hessian F x).mulVecLin, D.mixedGramAt a = 0)
    (i j k : CoisotropicBasis.Index m d q)
    (hne : polarization F (D.basis i) (D.basis j) (D.basis k) ≠ 0) :
    0 ≤ D.loweredRadialWeight i + D.loweredRadialWeight j + D.loweredRadialWeight k := by
  classical
  let r : CoisotropicBasis.Index m d q := Sum.inr (Sum.inr (Sum.inl D.radial))
  have hr : D.basis r = x := D.radial_eq
  have hwr : D.loweredRadialWeight r = -2 := by simp [r, loweredRadialWeight]
  by_cases hi : i=r
  · subst i
    rw [hr] at hne
    rw [hwr]
    exact D.loweredRadialWeight_radial_tensor hF j k hne
  by_cases hj : j=r
  · subst j
    rw [hr, polarization_swap_first] at hne
    have h := D.loweredRadialWeight_radial_tensor hF i k hne
    rw [hwr]
    omega
  by_cases hk : k=r
  · subst k
    rw [hr, polarization_swap_last hF, polarization_swap_first] at hne
    have h := D.loweredRadialWeight_radial_tensor hF i j hne
    rw [hwr]
    omega
  have hAAt (a b : Fin m) (v : GeometricPoint n) (hv : v ∈ T) :
      polarization F (D.radicalVector a) (D.radicalVector b) v = 0 := by
    rw [polarization_swap_last hF, polarization_swap_first]
    exact hann v hv _ (D.radical_hessian_kernel a) _ (D.radical_hessian_kernel b)
  have hAAA (a b c : Fin m) : polarization F (D.radicalVector a)
      (D.radicalVector b) (D.radicalVector c) = 0 :=
    hAAt a b _ (hker (D.radical_hessian_kernel c))
  have hAAB (a b : Fin m) (c : Fin q) : polarization F (D.radicalVector a)
      (D.radicalVector b) (D.middleVector c) = 0 := hAAt a b _ (D.tangent_middle c)
  have hAAK (a b : Fin m) (c : Fin d) : polarization F (D.radicalVector a)
      (D.radicalVector b) (D.isotropicVector c) = 0 := hAAt a b _ (D.tangent_isotropic c)
  have hAKK (a : Fin m) (b c : Fin d) : polarization F (D.radicalVector a)
      (D.isotropicVector b) (D.isotropicVector c) = 0 := by
    rw [polarization_swap_first, polarization_swap_last hF]
    exact congrFun (congrFun (hC _ (D.radical_hessian_kernel a)) b) c
  have hAKB (a : Fin m) (b : Fin d) (c : Fin q) : polarization F (D.radicalVector a)
      (D.isotropicVector b) (D.middleVector c) = 0 := by
    rw [polarization_swap_first, polarization_swap_last hF]
    exact congrFun (congrFun (hE _ (D.radical_hessian_kernel a)) b) c
  rcases i with i | (i | (i | i)) <;> rcases j with j | (j | (j | j)) <;>
    rcases k with k | (k | (k | k))
  all_goals simp only [loweredRadialWeight, Sum.elim_inl, Sum.elim_inr]
  all_goals simp only [r, Sum.inr.injEq, Sum.inl.injEq] at hi hj hk
  all_goals try simp only [if_neg hi, if_neg hj, if_neg hk]
  · exfalso
    apply hne
    exact hAAA i j k
  · exfalso
    apply hne
    exact hAAB i j k
  · exfalso
    apply hne
    exact hAAK i j k
  · omega
  · exfalso
    apply hne
    rw [polarization_swap_last hF]
    exact hAAB i k j
  · omega
  · exfalso
    apply hne
    rw [polarization_swap_last hF]
    exact hAKB i k j
  · omega
  · exfalso
    apply hne
    rw [polarization_swap_last hF]
    exact hAAK i k j
  · exfalso
    apply hne
    exact hAKB i j k
  · exfalso
    apply hne
    exact hAKK i j k
  · omega
  · omega
  · omega
  · omega
  · omega
  · exfalso
    apply hne
    rw [polarization_swap_first, polarization_swap_last hF]
    exact hAAB j k i
  · omega
  · exfalso
    apply hne
    rw [polarization_swap_first, polarization_swap_last hF]
    exact hAKB j k i
  · omega
  · omega
  · omega
  · omega
  · omega
  · exfalso
    apply hne
    rw [polarization_swap_first, polarization_swap_last hF, polarization_swap_first]
    exact hAKB k j i
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exfalso
    apply hne
    rw [polarization_swap_first, polarization_swap_last hF]
    exact hAAK j k i
  · exfalso
    apply hne
    rw [polarization_swap_first]
    exact hAKB j i k
  · exfalso
    apply hne
    rw [polarization_swap_first]
    exact hAKK j i k
  · omega
  · exfalso
    apply hne
    rw [polarization_swap_last hF, polarization_swap_first]
    exact hAKB k i j
  · omega
  · omega
  · omega
  · exfalso
    apply hne
    rw [polarization_swap_last hF, polarization_swap_first]
    exact hAKK k i j
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

theorem loweredRadialWeight_sum_nonnegative (hF : F.IsHomogeneous 3) (hsemi : WeightSemistable F)
    (hker : LinearMap.ker (hessian F x).mulVecLin ≤ T)
    (hann : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0)
    (hC : ∀ a ∈ LinearMap.ker (hessian F x).mulVecLin, D.isotropicGramAt a = 0)
    (hE : ∀ a ∈ LinearMap.ker (hessian F x).mulVecLin, D.mixedGramAt a = 0) :
    0 ≤ -2*(m : ℤ)+(q : ℤ)-2+4*(d : ℤ) := by
  rw [← D.sum_loweredRadialWeight]
  exact hsemi.nonnegative_weight_sum_of_basis_tensor hF D.basis D.loweredRadialWeight
    (D.loweredRadialWeight_nonnegative_tensor hF hker hann hC hE)

end CoisotropicBasis.Data
end HessianTheorem11
