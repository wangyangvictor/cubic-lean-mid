import HessianTheorem11.SaturatedHessianPencil
import HessianTheorem11.BasisWeightSum

/-! Lowering the weights on an actual common radical in the scalar
alternative of the final thirteen-variable configuration. -/
noncomputable section
namespace HessianTheorem11
open Module MvPolynomial
namespace CoisotropicBasis.Data
variable {n m d q : ℕ} {F : GeometricPolynomial n} {x : GeometricPoint n}
  {T : Submodule GeometricField (GeometricPoint n)}
  (D : Data (hessianBilinear F x) T x m d q)

def scalarRadicalWeight (S : Finset (Fin m)) : CoisotropicBasis.Index m d q → ℤ :=
  Sum.elim (fun i => if i ∈ S then -5 else -2)
    (Sum.elim (fun _ => 1) (Sum.elim (fun i => if i=D.radial then -2 else 1) (fun _ => 4)))

theorem sum_scalarRadicalWeight (S : Finset (Fin m)) :
    ∑ i, D.scalarRadicalWeight S i = -2*(m : ℤ)-3*(S.card : ℤ)+(q : ℤ)+5*(d : ℤ)-3 := by
  classical
  have ha : (∑ i : Fin m, if i ∈ S then (-5 : ℤ) else -2) = -2*m-3*S.card := by
    have he (i : Fin m) : (if i ∈ S then (-5 : ℤ) else -2) =
        -2 - 3*(if i ∈ S then 1 else 0) := by split_ifs <;> norm_num
    simp only [he, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    simp
    ring
  simp only [scalarRadicalWeight, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, ha]
  have hk : (∑ i : Fin d, if i = D.radial then (-2 : ℤ) else 1) = (d : ℤ)-3 := by
    have he (i : Fin d) : (if i = D.radial then (-2 : ℤ) else 1) =
        1-3*(if i = D.radial then 1 else 0) := by split_ifs <;> norm_num
    simp [he, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq']
  rw [hk]
  simp
  ring

theorem scalarRadicalWeight_radial_tensor (hF : F.IsHomogeneous 3)
    (S : Finset (Fin m)) (i j : CoisotropicBasis.Index m d q)
    (hne : polarization F x (D.basis i) (D.basis j) ≠ 0) :
    0 ≤ -2 + D.scalarRadicalWeight S i + D.scalarRadicalWeight S j := by
  classical
  rw [polarization_swap_first, polarization_swap_last hF] at hne
  change D.gramAt x i j ≠ 0 at hne
  rw [D.gramAt_base, D.complementGramAt_base] at hne
  rcases i with i | (i | (i | i)) <;> rcases j with j | (j | (j | j)) <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply] at hne
  all_goals try contradiction
  all_goals simp only [scalarRadicalWeight, Sum.elim_inl, Sum.elim_inr]
  all_goals (try split_ifs) <;> norm_num

set_option maxHeartbeats 2000000 in
theorem scalarRadicalWeight_nonnegative_tensor (hF : F.IsHomogeneous 3)
    (hker : LinearMap.ker (hessian F x).mulVecLin ≤ T)
    (hann : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0)
    (S : Finset (Fin m))
    (hSA : ∀ a ∈ S, ∀ b : Fin m, ∀ v : GeometricPoint n,
      polarization F (D.radicalVector a) (D.radicalVector b) v = 0)
    (hST : ∀ a ∈ S, ∀ t ∈ T, ∀ u ∈ T,
      polarization F (D.radicalVector a) t u = 0)
    (i j k : CoisotropicBasis.Index m d q)
    (hne : polarization F (D.basis i) (D.basis j) (D.basis k) ≠ 0) :
    0 ≤ D.scalarRadicalWeight S i + D.scalarRadicalWeight S j + D.scalarRadicalWeight S k := by
  classical
  let r : CoisotropicBasis.Index m d q := Sum.inr (Sum.inr (Sum.inl D.radial))
  have hr : D.basis r = x := D.radial_eq
  have hwr : D.scalarRadicalWeight S r = -2 := by simp [r, scalarRadicalWeight]
  by_cases hi : i=r
  · subst i
    rw [hr] at hne
    rw [hwr]
    exact D.scalarRadicalWeight_radial_tensor hF S j k hne
  by_cases hj : j=r
  · subst j
    rw [hr, polarization_swap_first] at hne
    have h := D.scalarRadicalWeight_radial_tensor hF S i k hne
    rw [hwr]
    omega
  by_cases hk : k=r
  · subst k
    rw [hr, polarization_swap_last hF, polarization_swap_first] at hne
    have h := D.scalarRadicalWeight_radial_tensor hF S i j hne
    rw [hwr]
    omega
  have hAAt (a b : Fin m) (v : GeometricPoint n) (hv : v ∈ T) :
      polarization F (D.radicalVector a) (D.radicalVector b) v = 0 := by
    rw [polarization_swap_last hF, polarization_swap_first]
    exact hann v hv _ (D.radical_hessian_kernel a) _ (D.radical_hessian_kernel b)
  have hAAA (a b c : Fin m) := hAAt a b _ (hker (D.radical_hessian_kernel c))
  have hAAB (a b : Fin m) (c : Fin q) := hAAt a b _ (D.tangent_middle c)
  have hAAK (a b : Fin m) (c : Fin d) := hAAt a b _ (D.tangent_isotropic c)
  have hSBB (a : Fin m) (ha : a ∈ S) (b c : Fin q) :=
    hST a ha _ (D.tangent_middle b) _ (D.tangent_middle c)
  have hSKB (a : Fin m) (ha : a ∈ S) (b : Fin d) (c : Fin q) :=
    hST a ha _ (D.tangent_isotropic b) _ (D.tangent_middle c)
  have hSKK (a : Fin m) (ha : a ∈ S) (b c : Fin d) :=
    hST a ha _ (D.tangent_isotropic b) _ (D.tangent_isotropic c)
  simp only [radicalVector, middleVector, isotropicVector] at hAAA hAAB hAAK hSA hSBB hSKB hSKK
  rcases i with i | (i | (i | i)) <;> rcases j with j | (j | (j | j)) <;>
    rcases k with k | (k | (k | k))
  all_goals simp only [scalarRadicalWeight, Sum.elim_inl, Sum.elim_inr]
  all_goals simp only [r, Sum.inr.injEq, Sum.inl.injEq] at hi hj hk
  all_goals try simp only [if_neg hi, if_neg hj, if_neg hk]
  · exfalso
    exact hne (hAAA i j k)
  · 
    exfalso
    apply hne
    exact hAAB i j k
  · 
    exfalso
    apply hne
    exact hAAK i j k
  · by_cases ha : i ∈ S
    ·
      exfalso
      apply hne
      exact hSA i ha j (D.dualVector k)
    · by_cases hb : j ∈ S
      ·
        exfalso
        apply hne
        rw [polarization_swap_first]
        exact hSA j hb i (D.dualVector k)
      · simp only [if_neg ha, if_neg hb]
        norm_num
  · 
    exfalso
    apply hne
    rw [polarization_swap_last hF]
    exact hAAB i k j
  · by_cases ha : i ∈ S
    ·
      exfalso
      apply hne
      exact hSBB i ha j k
    · simp only [if_neg ha]
      norm_num
  · by_cases ha : i ∈ S
    ·
      exfalso
      apply hne
      rw [polarization_swap_last hF]
      exact hSKB i ha k j
    · simp only [if_neg ha]
      norm_num
  · (try split_ifs) <;> norm_num
  · 
    exfalso
    apply hne
    rw [polarization_swap_last hF]
    exact hAAK i k j
  · by_cases ha : i ∈ S
    ·
      exfalso
      apply hne
      exact hSKB i ha j k
    · simp only [if_neg ha]
      norm_num
  · by_cases ha : i ∈ S
    ·
      exfalso
      apply hne
      exact hSKK i ha j k
    · simp only [if_neg ha]
      norm_num
  · (try split_ifs) <;> norm_num
  · by_cases ha : i ∈ S
    ·
      exfalso
      apply hne
      rw [polarization_swap_last hF]
      exact hSA i ha k (D.dualVector j)
    · by_cases hb : k ∈ S
      ·
        exfalso
        apply hne
        rw [polarization_swap_last hF, polarization_swap_first]
        exact hSA k hb i (D.dualVector j)
      · simp only [if_neg ha, if_neg hb]
        norm_num
  · (try split_ifs) <;> norm_num
  · (try split_ifs) <;> norm_num
  · (try split_ifs) <;> norm_num
  · 
    exfalso
    apply hne
    rw [polarization_swap_first, polarization_swap_last hF]
    exact hAAB j k i
  · by_cases ha : j ∈ S
    ·
      exfalso
      apply hne
      rw [polarization_swap_first]
      exact hSBB j ha i k
    · simp only [if_neg ha]
      norm_num
  · by_cases ha : j ∈ S
    ·
      exfalso
      apply hne
      rw [polarization_swap_first, polarization_swap_last hF]
      exact hSKB j ha k i
    · simp only [if_neg ha]
      norm_num
  · (try split_ifs) <;> norm_num
  · by_cases ha : k ∈ S
    ·
      exfalso
      apply hne
      rw [polarization_swap_last hF, polarization_swap_first]
      exact hSBB k ha i j
    · simp only [if_neg ha]
      norm_num
  · (try split_ifs) <;> norm_num
  · (try split_ifs) <;> norm_num
  · (try split_ifs) <;> norm_num
  · by_cases ha : k ∈ S
    ·
      exfalso
      apply hne
      rw [polarization_swap_first, polarization_swap_last hF, polarization_swap_first]
      exact hSKB k ha j i
    · simp only [if_neg ha]
      norm_num
  · (try split_ifs) <;> norm_num
  · (try split_ifs) <;> norm_num
  · (try split_ifs) <;> norm_num
  · (try split_ifs) <;> norm_num
  · (try split_ifs) <;> norm_num
  · (try split_ifs) <;> norm_num
  · (try split_ifs) <;> norm_num
  · 
    exfalso
    apply hne
    rw [polarization_swap_first, polarization_swap_last hF]
    exact hAAK j k i
  · by_cases ha : j ∈ S
    ·
      exfalso
      apply hne
      rw [polarization_swap_first]
      exact hSKB j ha i k
    · simp only [if_neg ha]
      norm_num
  · by_cases ha : j ∈ S
    ·
      exfalso
      apply hne
      rw [polarization_swap_first]
      exact hSKK j ha i k
    · simp only [if_neg ha]
      norm_num
  · (try split_ifs) <;> norm_num
  · by_cases ha : k ∈ S
    ·
      exfalso
      apply hne
      rw [polarization_swap_last hF, polarization_swap_first]
      exact hSKB k ha i j
    · simp only [if_neg ha]
      norm_num
  · (try split_ifs) <;> norm_num
  · (try split_ifs) <;> norm_num
  · (try split_ifs) <;> norm_num
  · by_cases ha : k ∈ S
    ·
      exfalso
      apply hne
      rw [polarization_swap_last hF, polarization_swap_first]
      exact hSKK k ha i j
    · simp only [if_neg ha]
      norm_num
  · (try split_ifs) <;> norm_num
  · (try split_ifs) <;> norm_num
  · (try split_ifs) <;> norm_num
  · (try split_ifs) <;> norm_num
  · (try split_ifs) <;> norm_num
  · (try split_ifs) <;> norm_num
  · (try split_ifs) <;> norm_num
  · by_cases ha : j ∈ S
    ·
      exfalso
      apply hne
      rw [polarization_swap_first, polarization_swap_last hF]
      exact hSA j ha k (D.dualVector i)
    · by_cases hb : k ∈ S
      ·
        exfalso
        apply hne
        rw [polarization_swap_first, polarization_swap_last hF, polarization_swap_first]
        exact hSA k hb j (D.dualVector i)
      · simp only [if_neg ha, if_neg hb]
        norm_num
  · (try split_ifs) <;> norm_num
  · (try split_ifs) <;> norm_num
  · (try split_ifs) <;> norm_num
  · (try split_ifs) <;> norm_num
  · (try split_ifs) <;> norm_num
  · (try split_ifs) <;> norm_num
  · (try split_ifs) <;> norm_num
  · (try split_ifs) <;> norm_num
  · (try split_ifs) <;> norm_num
  · (try split_ifs) <;> norm_num
  · (try split_ifs) <;> norm_num
  · (try split_ifs) <;> norm_num
  · (try split_ifs) <;> norm_num
  · (try split_ifs) <;> norm_num
  · (try split_ifs) <;> norm_num

theorem scalarRadicalWeight_sum_nonnegative (hF : F.IsHomogeneous 3) (hsemi : WeightSemistable F)
    (hker : LinearMap.ker (hessian F x).mulVecLin ≤ T)
    (hann : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0)
    (S : Finset (Fin m))
    (hSA : ∀ a ∈ S, ∀ b : Fin m, ∀ v : GeometricPoint n,
      polarization F (D.radicalVector a) (D.radicalVector b) v = 0)
    (hST : ∀ a ∈ S, ∀ t ∈ T, ∀ u ∈ T,
      polarization F (D.radicalVector a) t u = 0) :
    0 ≤ -2*(m : ℤ)-3*(S.card : ℤ)+(q : ℤ)+5*(d : ℤ)-3 := by
  rw [← D.sum_scalarRadicalWeight S]
  exact hsemi.nonnegative_weight_sum_of_basis_tensor hF D.basis (D.scalarRadicalWeight S)
    (D.scalarRadicalWeight_nonnegative_tensor hF hker hann S hSA hST)

end CoisotropicBasis.Data
end HessianTheorem11
