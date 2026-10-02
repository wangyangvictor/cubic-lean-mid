import CubicTenVariables.SimultaneousResidueCount
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Nonnegative residue weights in an actual translated progression box.
The proof groups integer vectors by their simultaneous reductions. Only
equality of residues is needed: no CRT representative or periodicity of
any other function on integer vectors is assumed. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.SimultaneousResidueWeightSum
open SimultaneousResidueCount
open scoped BigOperators

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- The actual product of local nonnegative weights is controlled by the
product of their complete residue sums, uniformly over every finite subset
of a translated box and a fixed integral progression. -/
theorem sum_le (q : ι → ℕ) [∀ i, NeZero (q i)]
    (hcop : Pairwise (fun i j => (q i).Coprime (q j)))
    (m : ℕ) (hm : 0 < m) (hmq : ∀ i, m.Coprime (q i))
    (w : ∀ i, (Fin n → ZMod (q i)) → ℝ) (hw : ∀ i y, 0 ≤ w i y)
    (u : Fin n → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (b : Fin n → ℤ) (S : Finset (Fin n → ℤ))
    (hbox : ∀ x ∈ S, ∀ i, |(x i : ℝ)-u i| ≤ L)
    (hres : ∀ x ∈ S, ∀ i, (m : ℤ) ∣ x i-b i) :
    (∑ x ∈ S, ∏ i, w i (fun j => (x j : ZMod (q i)))) ≤
      (4*L/(m*∏ i, q i : ℕ)+3)^n *
        ∏ i, ∑ y : Fin n → ZMod (q i), w i y := by
  classical
  let M : ℕ := m*∏ i, q i
  have hM : 0 < M := Nat.mul_pos hm (Finset.prod_pos fun i _ => NeZero.pos (q i))
  letI : NeZero M := ⟨hM.ne'⟩
  let B : ℝ := (4*L/(M : ℝ)+3)^n
  have hB : 0 ≤ B := by positivity
  let W : (∀ i, Fin n → ZMod (q i)) → ℝ := fun y => ∏ i, w i (y i)
  have hW (y) : 0 ≤ W y := Finset.prod_nonneg fun i _ => hw i (y i)
  have hfiber (y) (hy : y ∈ S.image (residues q)) :
      ((S.filter fun x => residues q x=y).card : ℝ) ≤ B := by
    apply ResidueBoxCount.card_le_of_constant_residue M _ u L hL
    · intro x hx
      exact hbox x (Finset.mem_filter.mp hx).1
    · intro x hx z hz j
      have he := (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hz).2.symm
      apply (cast_eq_iff_dvd M (x j) (z j)).mpr
      exact product_dvd q hcop m hmq (x j) (z j)
        (by simpa only [sub_sub_sub_cancel_right] using
          dvd_sub (hres x (Finset.mem_filter.mp hx).1 j) (hres z (Finset.mem_filter.mp hz).1 j))
        (fun i => congrFun (congrFun he i) j)
  calc
    _ = ∑ y ∈ S.image (residues q),
        ∑ x ∈ S.filter (fun x => residues q x=y), W (residues q x) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩) _
    _ = ∑ y ∈ S.image (residues q),
        ((S.filter fun x => residues q x=y).card : ℝ) * W y := by
      apply Finset.sum_congr rfl
      intro y hy
      calc
        _ = ∑ _x ∈ S.filter (fun x => residues q x=y), W y := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [(Finset.mem_filter.mp hx).2]
        _ = _ := by simp
    _ ≤ ∑ y ∈ S.image (residues q), B * W y :=
      Finset.sum_le_sum fun y hy => mul_le_mul_of_nonneg_right (hfiber y hy) (hW y)
    _ ≤ ∑ y : ∀ i, Fin n → ZMod (q i), B * W y :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun y _ _ => mul_nonneg hB (hW y))
    _ = B * ∏ i, ∑ y : Fin n → ZMod (q i), w i y := by
      rw [← Finset.mul_sum]
      congr 1
      exact (Fintype.prod_sum w).symm
    _ = _ := rfl

/-- In the range where the product of local moduli is at most
`T = 1 + L/m`, every residue fiber costs at most `(7*T/prod q)^n`.
This does not require the combined modulus `m*prod q` to be at most `L`. -/
theorem sum_le_normalized (q : ι → ℕ) [∀ i, NeZero (q i)]
    (hcop : Pairwise (fun i j => (q i).Coprime (q j)))
    (m : ℕ) (hm : 0 < m) (hmq : ∀ i, m.Coprime (q i))
    (w : ∀ i, (Fin n → ZMod (q i)) → ℝ) (hw : ∀ i y, 0 ≤ w i y)
    (u : Fin n → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hqL : (∏ i, q i : ℕ) ≤ 1+L/(m : ℝ))
    (b : Fin n → ℤ) (S : Finset (Fin n → ℤ))
    (hbox : ∀ x ∈ S, ∀ i, |(x i : ℝ)-u i| ≤ L)
    (hres : ∀ x ∈ S, ∀ i, (m : ℤ) ∣ x i-b i) :
    (∑ x ∈ S, ∏ i, w i (fun j => (x j : ZMod (q i)))) ≤
      (7*(1+L/(m : ℝ))/(∏ i, q i : ℕ))^n *
        ∏ i, ∑ y : Fin n → ZMod (q i), w i y := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hqR : 0 < ((∏ i, q i : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => NeZero.pos (q i))
  apply (sum_le q hcop m hm hmq w hw u L hL b S hbox hres).trans
  apply mul_le_mul_of_nonneg_right _
    (Finset.prod_nonneg fun i _ => Finset.sum_nonneg fun y _ => hw i y)
  apply pow_le_pow_left₀ (by positivity)
  rw [Nat.cast_mul]
  apply (le_div_iff₀ hqR).mpr
  have he : (4*L/((m : ℝ)*((∏ i, q i : ℕ) : ℝ))+3)*
      ((∏ i, q i : ℕ) : ℝ) = 4*(L/(m : ℝ))+3*((∏ i, q i : ℕ) : ℝ) := by
    field_simp [ne_of_gt hmR,ne_of_gt hqR]
  rw [he]
  nlinarith [div_nonneg hL hmR.le]

end CubicTenVariables.SimultaneousResidueWeightSum
