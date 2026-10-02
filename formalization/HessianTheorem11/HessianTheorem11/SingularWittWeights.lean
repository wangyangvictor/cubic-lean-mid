import HessianTheorem11.WittSubspaceBasis
import HessianTheorem11.SingularExtraRadical

/-! The actual polarization support test for the isotropic deficient-span
weights. It retains arbitrary tangent-normal-normal and normal-cubic terms. -/
noncomputable section
namespace HessianTheorem11.SingularWittWeights
open MvPolynomial Module WittSubspaceBasis
open scoped BigOperators

abbrev Index (s r l k : ℕ) := Unit ⊕ (Fin s ⊕ WittSubspaceBasis.Index r l k)
def radial {s r l k : ℕ} : Index s r l k := Sum.inl ()
def tangent {s r l k : ℕ} (i : Fin s) : Index s r l k := Sum.inr (Sum.inl i)
def normal {s r l k : ℕ} (i : WittSubspaceBasis.Index r l k) : Index s r l k := Sum.inr (Sum.inr i)
def weight {s r l k : ℕ} (active : Finset (Fin s)) : Index s r l k → ℤ :=
  Sum.elim (fun _ => -8) (Sum.elim (fun i => if i ∈ active then -2 else -3)
    WittSubspaceBasis.weight)

theorem normal_weight_bounds {r l k : ℕ} (i : WittSubspaceBasis.Index r l k) :
    2 ≤ WittSubspaceBasis.weight i ∧ WittSubspaceBasis.weight i ≤ 6 := by
  rcases i with i | ((i | i) | i) <;> norm_num [WittSubspaceBasis.weight]

theorem tangent_weight_bounds {s r l k : ℕ} (active : Finset (Fin s)) (i : Fin s) :
    -3 ≤ weight (r := r) (l := l) (k := k) active (tangent i) ∧
      weight (r := r) (l := l) (k := k) active (tangent i) ≤ -2 := by
  simp only [weight,tangent,Sum.elim_inr,Sum.elim_inl]
  split <;> norm_num

theorem sum_weight {s r l k : ℕ} (active : Finset (Fin s)) :
    ∑ i, weight (r := r) (l := l) (k := k) active i =
      -8 - 3*(s : ℤ) + active.card + 4*((r : ℤ)+2*l+k) := by
  classical
  simp only [weight,WittSubspaceBasis.weight,Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finset.sum_const,Finset.card_univ,Fintype.card_unit,Fintype.card_fin,nsmul_eq_mul]
  have he : (∑ i : Fin s, if i ∈ active then (-2 : ℤ) else -3) = -3*(s : ℤ)+active.card := by
    have hpoint (i : Fin s) : (if i ∈ active then (-2 : ℤ) else -3) =
        -3 + if i ∈ active then 1 else 0 := by split <;> norm_num
    simp_rw [hpoint]
    simp [Finset.sum_add_distrib]
    ring
  rw [he]
  ring

variable {K : Type*} [Field K] [CharZero K] {n s r l k : ℕ}

theorem nonnegative_tensor
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (b : Index s r l k → (Fin n → K)) (active : Finset (Fin s))
    (hx : (hessian F (b radial)).mulVec (b radial) = 0)
    (ht : ∀ i, (hessian F (b radial)).mulVec (b (tangent i)) = 0)
    (httt : ∀ i j a, polarization F (b (tangent i)) (b (tangent j)) (b (tangent a)) = 0)
    (hgram : ∀ i j, polarization F (b radial) (b (normal i)) (b (normal j)) ≠ 0 →
      WittSubspaceBasis.weight i + WittSubspaceBasis.weight j = 8)
    (haad : ∀ i j a, polarization F (b (tangent i)) (b (tangent j)) (b (normal a)) ≠ 0 →
      WittSubspaceBasis.weight a = 6 ∨
        (WittSubspaceBasis.weight a = 4 ∧ i ∈ active ∧ j ∈ active))
    (i j a : Index s r l k)
    (hne : polarization F (b i) (b j) (b a) ≠ 0) :
    0 ≤ weight (r := r) (l := l) (k := k) active i + weight (r := r) (l := l) (k := k) active j + weight (r := r) (l := l) (k := k) active a := by
  have hxv (i : Index s r l k) : polarization F (b radial) (b radial) (b i) = 0 := by
    rw [polarization_rotate hF]
    simp only [polarization, hx, dotProduct_zero]
  have htv (j : Fin s) (i : Index s r l k) :
      polarization F (b radial) (b (tangent j)) (b i) = 0 := by
    rw [polarization_rotate hF, polarization_swap_last hF]
    simp only [polarization, ht, dotProduct_zero]
  have hrad (j a : Index s r l k)
      (h : polarization F (b radial) (b j) (b a) ≠ 0) :
      0 ≤ weight (r := r) (l := l) (k := k) active radial + weight (r := r) (l := l) (k := k) active j + weight (r := r) (l := l) (k := k) active a := by
    rcases j with ⟨⟩ | (j | j)
    · exact (h (hxv a)).elim
    · exact (h (htv j a)).elim
    rcases a with ⟨⟩ | (a | a)
    · exact (h (by rw [polarization_swap_last hF]; exact hxv (normal j))).elim
    · exact (h (by rw [polarization_swap_last hF]; exact htv a (normal j))).elim
    have he := hgram j a h
    simp only [weight,radial,Sum.elim_inl,Sum.elim_inr]
    omega
  have httn (i j : Fin s) (a : WittSubspaceBasis.Index r l k)
      (h : polarization F (b (tangent i)) (b (tangent j)) (b (normal a)) ≠ 0) :
      0 ≤ weight (r := r) (l := l) (k := k) active (tangent i) + weight (r := r) (l := l) (k := k) active (tangent j) + weight (r := r) (l := l) (k := k) active (normal a) := by
    obtain ha | ⟨ha,hi,hj⟩ := haad i j a h
    · have hi := (tangent_weight_bounds (r := r) (l := l) (k := k) active i).1
      have hj := (tangent_weight_bounds (r := r) (l := l) (k := k) active j).1
      change 0 ≤ weight (r := r) (l := l) (k := k) active (tangent i) + weight (r := r) (l := l) (k := k) active (tangent j) + WittSubspaceBasis.weight a
      omega
    · simp [weight,tangent,normal,ha,hi,hj]
  rcases i with ⟨⟩ | (i | i)
  · exact hrad j a hne
  · rcases j with ⟨⟩ | (j | j)
    · have hh : polarization F (b radial) (b (tangent i)) (b a) ≠ 0 := by
        rwa [polarization_swap_first]
      have he := hrad (tangent i) a hh
      simpa only [add_comm (weight (r := r) (l := l) (k := k) active radial) (weight (r := r) (l := l) (k := k) active (tangent i))] using he
    · rcases a with ⟨⟩ | (a | a)
      · exact (hne (by rw [polarization_rotate hF]; exact htv i (tangent j))).elim
      · exact (hne (httt i j a)).elim
      · exact httn i j a hne
    · rcases a with ⟨⟩ | (a | a)
      · have hh : polarization F (b radial) (b (tangent i)) (b (normal j)) ≠ 0 := by
          rwa [← polarization_rotate hF]
        exact (hh (htv i (normal j))).elim
      · have hh : polarization F (b (tangent i)) (b (tangent a)) (b (normal j)) ≠ 0 := by
          rwa [polarization_swap_last hF]
        have he := httn i a j hh
        simp only [weight,tangent,normal,radial,Sum.elim_inl,Sum.elim_inr] at he ⊢
        omega
      · have hi := (tangent_weight_bounds (r := r) (l := l) (k := k) active i).1
        have hj := (normal_weight_bounds j).1
        have ha := (normal_weight_bounds a).1
        change 0 ≤ weight (r := r) (l := l) (k := k) active (tangent i) + WittSubspaceBasis.weight j + WittSubspaceBasis.weight a
        omega
  · rcases j with ⟨⟩ | (j | j)
    · have hh : polarization F (b radial) (b (normal i)) (b a) ≠ 0 := by
        rwa [polarization_swap_first]
      have he := hrad (normal i) a hh
      simpa only [add_comm (weight (r := r) (l := l) (k := k) active radial) (weight (r := r) (l := l) (k := k) active (normal i))] using he
    · rcases a with ⟨⟩ | (a | a)
      · exact (hne (by rw [polarization_rotate hF,polarization_swap_last hF]; exact htv j (normal i))).elim
      · have hh : polarization F (b (tangent j)) (b (tangent a)) (b (normal i)) ≠ 0 := by
          rwa [polarization_rotate hF]
        have he := httn j a i hh
        simp only [weight,tangent,normal,radial,Sum.elim_inl,Sum.elim_inr] at he ⊢
        omega
      · have hi := (normal_weight_bounds i).1
        have hj := (tangent_weight_bounds (r := r) (l := l) (k := k) active j).1
        have ha := (normal_weight_bounds a).1
        change 0 ≤ WittSubspaceBasis.weight i + weight (r := r) (l := l) (k := k) active (tangent j) + WittSubspaceBasis.weight a
        omega
    · rcases a with ⟨⟩ | (a | a)
      · have hh : polarization F (b radial) (b (normal i)) (b (normal j)) ≠ 0 := by
          rwa [← polarization_rotate hF]
        have he := hrad (normal i) (normal j) hh
        simp only [weight,tangent,normal,radial,Sum.elim_inl,Sum.elim_inr] at he ⊢
        omega
      · have hi := (normal_weight_bounds i).1
        have hj := (normal_weight_bounds j).1
        have ha := (tangent_weight_bounds (r := r) (l := l) (k := k) active a).1
        change 0 ≤ WittSubspaceBasis.weight i + WittSubspaceBasis.weight j + weight (r := r) (l := l) (k := k) active (tangent a)
        omega
      · have hi := (normal_weight_bounds i).1
        have hj := (normal_weight_bounds j).1
        have ha := (normal_weight_bounds a).1
        change 0 ≤ WittSubspaceBasis.weight i + WittSubspaceBasis.weight j + WittSubspaceBasis.weight a
        omega

/-- The constructed nonnegative tensor weights contradict semistability
in five normal and at least five nonradial tangent coordinates. -/
theorem impossible_of_semistable
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3) (hsemi : WeightSemistable F)
    (b : Basis (Index s r l k) K (Fin n → K)) (active : Finset (Fin s))
    (hactive : active.card ≤ 2) (hs : 5 ≤ s) (hnormal : r + 2*l + k = 5)
    (hx : (hessian F (b radial)).mulVec (b radial) = 0)
    (ht : ∀ i, (hessian F (b radial)).mulVec (b (tangent i)) = 0)
    (httt : ∀ i j a, polarization F (b (tangent i)) (b (tangent j)) (b (tangent a)) = 0)
    (hgram : ∀ i j, polarization F (b radial) (b (normal i)) (b (normal j)) ≠ 0 →
      WittSubspaceBasis.weight i + WittSubspaceBasis.weight j = 8)
    (haad : ∀ i j a, polarization F (b (tangent i)) (b (tangent j)) (b (normal a)) ≠ 0 →
      WittSubspaceBasis.weight a = 6 ∨
        (WittSubspaceBasis.weight a = 4 ∧ i ∈ active ∧ j ∈ active)) : False := by
  classical
  have hc : Fintype.card (Index s r l k) = n := by
    simpa only [Module.finrank_pi,Fintype.card_fin] using (finrank_eq_card_basis b).symm
  let e := Fintype.equivFinOfCardEq hc
  let bf := b.reindex e
  let w : Fin n → ℤ := fun i => weight active (e.symm i)
  have hw : 0 ≤ ∑ i, w i := by
    apply hsemi.nonnegative_weight_sum_of_thirdPartials hF
      (HessianTheorem11.basisMatrix bf) (basisMatrix_injective bf) w
    intro i j a hne
    rw [thirdPartialCoefficient, polarization_in_coordinates F hF] at hne
    simp only [bf,Basis.reindex_apply] at hne
    exact nonnegative_tensor F hF b active hx ht httt hgram haad
      (e.symm i) (e.symm j) (e.symm a) hne
  change 0 ≤ ∑ i : Fin n, weight active (e.symm i) at hw
  rw [e.symm.sum_comp, sum_weight] at hw
  have hd : (r : ℤ)+2*l+k=5 := by exact_mod_cast hnormal
  rw [hd] at hw
  omega

end HessianTheorem11.SingularWittWeights
