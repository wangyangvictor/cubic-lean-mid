import CubicTenVariables.ResidueBoxCount
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-! Actual finite local maxima and exact lattice-window averaging. The real
window width is independent of any final error exponent. No Hessian chart or
choice of a principal minor is assumed in these finite combinatorial lemmas. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace CubicTenVariables.LocalSupremumWindow
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

/-- The literal real-width window in a finite set of lattice frequencies. -/
def window (S : Finset (Fin n → ℤ)) (v : Fin n → ℤ) (L : ℝ) :
    Finset (Fin n → ℤ) :=
  S.filter fun a => ∀ i, |(a i : ℝ)-(v i : ℝ)| ≤ L

@[simp] theorem mem_window (S : Finset (Fin n → ℤ)) (v a : Fin n → ℤ) (L : ℝ) :
    a ∈ window S v L ↔ a ∈ S ∧ ∀ i, |(a i : ℝ)-(v i : ℝ)| ≤ L := by
  simp [window]

/-- Empty windows have maximum zero, as in the source convention. -/
def maximum (S : Finset (Fin n → ℤ)) (g : (Fin n → ℤ) → ℝ)
    (v : Fin n → ℤ) (L : ℝ) : ℝ :=
  if h : (window S v L).Nonempty then (window S v L).sup' h g else 0

theorem maximum_eq_zero_of_empty (S : Finset (Fin n → ℤ))
    (g : (Fin n → ℤ) → ℝ) (v : Fin n → ℤ) (L : ℝ)
    (h : window S v L = ∅) : maximum S g v L = 0 := by
  simp [maximum,h]

@[simp] theorem maximum_empty (g : (Fin n → ℤ) → ℝ) (v : Fin n → ℤ) (L : ℝ) :
    maximum ∅ g v L = 0 := by simp [maximum,window]

theorem maximum_attained (S : Finset (Fin n → ℤ)) (g : (Fin n → ℤ) → ℝ)
    (v : Fin n → ℤ) (L : ℝ) (h : (window S v L).Nonempty) :
    ∃ a ∈ S, (∀ i, |(a i : ℝ)-(v i : ℝ)| ≤ L) ∧ maximum S g v L = g a := by
  obtain ⟨a,ha,he⟩ := Finset.exists_mem_eq_sup' h g
  exact ⟨a,(mem_window S v a L).mp ha |>.1,(mem_window S v a L).mp ha |>.2,
    by simpa [maximum,h] using he⟩

theorem le_maximum (S : Finset (Fin n → ℤ)) (g : (Fin n → ℤ) → ℝ)
    (v a : Fin n → ℤ) (L : ℝ) (ha : a ∈ window S v L) :
    g a ≤ maximum S g v L := by
  have hn : (window S v L).Nonempty := ⟨a,ha⟩
  simp only [maximum,dif_pos hn]
  exact Finset.le_sup' g ha

theorem maximum_nonneg (S : Finset (Fin n → ℤ)) (g : (Fin n → ℤ) → ℝ)
    (hg : ∀ a ∈ S, 0 ≤ g a) (v : Fin n → ℤ) (L : ℝ) :
    0 ≤ maximum S g v L := by
  by_cases h : (window S v L).Nonempty
  · obtain ⟨a,ha,hbox,he⟩ := maximum_attained S g v L h
    rw [he]
    exact hg a ha
  · simp [maximum,h]

theorem maximum_le (S : Finset (Fin n → ℤ)) (g : (Fin n → ℤ) → ℝ)
    (v : Fin n → ℤ) (L C : ℝ) (hC : 0 ≤ C)
    (h : ∀ a ∈ window S v L, g a ≤ C) : maximum S g v L ≤ C := by
  by_cases hn : (window S v L).Nonempty
  · obtain ⟨a,ha,hbox,he⟩ := maximum_attained S g v L hn
    rw [he]
    exact h a ((mem_window S v a L).mpr ⟨ha,hbox⟩)
  · simpa [maximum,hn] using hC

theorem maximum_mono (S : Finset (Fin n → ℤ)) (g h : (Fin n → ℤ) → ℝ)
    (hgh : ∀ a ∈ S, g a ≤ h a) (v : Fin n → ℤ) (L : ℝ) :
    maximum S g v L ≤ maximum S h v L := by
  by_cases hn : (window S v L).Nonempty
  · obtain ⟨a,ha,hbox,he⟩ := maximum_attained S g v L hn
    rw [he]
    exact (hgh a ha).trans (le_maximum S h v a L ((mem_window S v a L).mpr ⟨ha,hbox⟩))
  · simp [maximum,hn]

theorem mem_window_norm (S : Finset (Fin n → ℤ)) (v a : Fin n → ℤ)
    (L : ℝ) (hL : 0 ≤ L) :
    a ∈ window S v L ↔ a ∈ S ∧ ‖(fun i => (a i : ℝ)-(v i : ℝ))‖ ≤ L := by
  simp only [mem_window,pi_norm_le_iff_of_nonneg hL,Real.norm_eq_abs]

/-- The exact nonzero frequency set; the surrounding integer box is only
an implementation of its finiteness, not an extra restriction. -/
def frequencies (n : ℕ) (B : ℝ) : Finset (Fin n → ℤ) :=
  (integerBox n ⌈max B 0⌉₊).filter fun a => a ≠ 0 ∧ ∀ i, |(a i : ℝ)| ≤ B

@[simp] theorem mem_frequencies (B : ℝ) (a : Fin n → ℤ) :
    a ∈ frequencies n B ↔ a ≠ 0 ∧ ∀ i, |(a i : ℝ)| ≤ B := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨?_,h⟩
    rw [mem_integerBox]
    intro i
    have hh : |(a i : ℝ)| ≤ (⌈max B 0⌉₊ : ℝ) :=
      (h.2 i).trans ((le_max_left B 0).trans (Nat.le_ceil _))
    exact_mod_cast hh

theorem mem_frequencies_norm (B : ℝ) (hB : 0 ≤ B) (a : Fin n → ℤ) :
    a ∈ frequencies n B ↔
      0 < ‖(fun i => (a i : ℝ))‖ ∧ ‖(fun i => (a i : ℝ))‖ ≤ B := by
  have hz : (fun i => (a i : ℝ)) = 0 ↔ a = 0 := by
    simp only [funext_iff,Pi.zero_apply,Int.cast_eq_zero]
  rw [mem_frequencies,norm_pos_iff,pi_norm_le_iff_of_nonneg hB]
  constructor
  · intro h
    exact ⟨fun ha => h.1 (hz.mp ha),by simpa only [Real.norm_eq_abs] using h.2⟩
  · intro h
    exact ⟨fun ha => h.1 (hz.mpr ha),by simpa only [Real.norm_eq_abs] using h.2⟩

theorem frequencies_empty_of_lt_one (B : ℝ) (hB : B < 1) : frequencies n B = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨hne,hbox⟩ := (mem_frequencies B a).mp ha
  have haz : a = 0 := by
    funext i
    have hi : |(a i : ℝ)| < 1 := (hbox i).trans_lt hB
    have hzi : |a i| < (1 : ℤ) := by exact_mod_cast hi
    have hlow := neg_abs_le (a i)
    have hupp := le_abs_self (a i)
    change a i = 0
    omega
  exact hne haz

theorem maximum_frequencies_zero_of_lt_one (g : (Fin n → ℤ) → ℝ)
    (B L : ℝ) (v : Fin n → ℤ) (hB : B < 1) :
    maximum (frequencies n B) g v L = 0 := by
  rw [frequencies_empty_of_lt_one B hB,maximum_empty]

/-- Exactly all integer centers within the given natural radius of a. -/
def shiftedBox (a : Fin n → ℤ) (L : ℕ) : Finset (Fin n → ℤ) :=
  (integerBox n L).image fun z => a+z

@[simp] theorem mem_shiftedBox (a v : Fin n → ℤ) (L : ℕ) :
    v ∈ shiftedBox a L ↔ ∀ i, |(a i : ℝ)-(v i : ℝ)| ≤ (L : ℝ) := by
  constructor
  · intro h
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp h
    rw [mem_integerBox] at hz
    intro i
    have hi : |(z i : ℝ)| ≤ (L : ℝ) := by exact_mod_cast hz i
    simpa using hi
  · intro h
    refine Finset.mem_image.mpr ⟨v-a,?_,by simp⟩
    rw [mem_integerBox]
    intro i
    have hi : |(v i : ℝ)-(a i : ℝ)| ≤ (L : ℝ) := by simpa only [abs_sub_comm] using h i
    exact_mod_cast hi

@[simp] theorem card_shiftedBox (a : Fin n → ℤ) (L : ℕ) :
    (shiftedBox a L).card = (2*L+1)^n := by
  rw [shiftedBox,Finset.card_image_of_injective]
  · exact card_integerBox n L
  · exact add_right_injective a

/-- A finite set containing exactly every center with a nonempty window. -/
def centers (S : Finset (Fin n → ℤ)) (L : ℕ) : Finset (Fin n → ℤ) :=
  S.biUnion fun a => shiftedBox a L

@[simp] theorem mem_centers (S : Finset (Fin n → ℤ)) (L : ℕ) (v : Fin n → ℤ) :
    v ∈ centers S L ↔ (window S v (L : ℝ)).Nonempty := by
  simp only [centers,Finset.mem_biUnion,mem_shiftedBox,Finset.nonempty_def,mem_window]

theorem maximum_zero_of_not_mem_centers (S : Finset (Fin n → ℤ))
    (g : (Fin n → ℤ) → ℝ) (L : ℕ) (v : Fin n → ℤ) (hv : v ∉ centers S L) :
    maximum S g v (L : ℝ) = 0 := by
  have h : ¬ (window S v (L : ℝ)).Nonempty := by simpa using hv
  simp [maximum,h]

/-- The unrestricted lattice sum is an actual finite sum, even for a
fractional real window width. -/
theorem tsum_maximum_eq_sum (S : Finset (Fin n → ℤ)) (g : (Fin n → ℤ) → ℝ) (L : ℝ) :
    (∑' v : Fin n → ℤ, maximum S g v L) =
      ∑ v ∈ centers S ⌈max L 0⌉₊, maximum S g v L := by
  apply tsum_eq_sum
  intro v hv
  have hn : ¬ (window S v L).Nonempty := by
    intro h
    obtain ⟨a,ha⟩ := h
    obtain ⟨haS,hbox⟩ := (mem_window S v a L).mp ha
    apply hv
    apply (mem_centers S ⌈max L 0⌉₊ v).mpr
    refine ⟨a,(mem_window S v a _).mpr ⟨haS,?_⟩⟩
    intro i
    exact (hbox i).trans ((le_max_left L 0).trans (Nat.le_ceil _))
  simp [maximum,hn]

/-- Exact counting of translated windows, before applying any inequality. -/
theorem sum_window_identity (S : Finset (Fin n → ℤ)) (g : (Fin n → ℤ) → ℝ) (L : ℕ) :
    (∑ v ∈ centers S L, ∑ a ∈ window S v (L : ℝ), g a) =
      ((2*L+1 : ℕ) : ℝ)^n * ∑ a ∈ S, g a := by
  simp only [window,Finset.sum_filter]
  rw [Finset.sum_comm]
  calc
    _ = ∑ a ∈ S, ∑ v ∈ shiftedBox a L, g a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← Finset.sum_filter]
      congr 1
      ext v
      simp only [Finset.mem_filter,mem_shiftedBox]
      constructor
      · exact fun h => h.2
      · intro hv
        exact ⟨Finset.mem_biUnion.mpr ⟨a,ha,(mem_shiftedBox a v L).mpr hv⟩,hv⟩
    _ = ((2*L+1 : ℕ) : ℝ)^n * ∑ a ∈ S, g a := by
      simp only [Finset.sum_const,card_shiftedBox,nsmul_eq_mul,Nat.cast_pow]
      exact (Finset.mul_sum ..).symm

/-- The finite l-infinity/l-one inequality in each actual window. -/
theorem window_holder (S : Finset (Fin n → ℤ)) (f g : (Fin n → ℤ) → ℝ)
    (hf : ∀ a ∈ S, 0 ≤ f a) (v : Fin n → ℤ) (L : ℝ) :
    (∑ a ∈ window S v L, f a*g a) ≤
      maximum S g v L * ∑ a ∈ window S v L, f a := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left (le_maximum S g v a L ha) (hf a (mem_window S v a L |>.mp ha).1)

/-- Exact averaging factor (2L+1)^n and the local-maximum bound used in C7.5. -/
theorem window_average_holder (S : Finset (Fin n → ℤ)) (f g : (Fin n → ℤ) → ℝ)
    (hf : ∀ a ∈ S, 0 ≤ f a) (L : ℕ) :
    ((2*L+1 : ℕ) : ℝ)^n * (∑ a ∈ S, f a*g a) ≤
      ∑ v ∈ centers S L, maximum S g v (L : ℝ) *
        ∑ a ∈ window S v (L : ℝ), f a := by
  rw [← sum_window_identity]
  exact Finset.sum_le_sum fun v _ => window_holder S f g hf v (L : ℝ)

/-- Arbitrarily translated real boxes have the requisite dimension-dependent
lattice count, without an alignment assumption on the center. -/
theorem card_le_shifted_real_box (S : Finset (Fin n → ℤ)) (u : Fin n → ℝ)
    (R : ℝ) (hR : 0 ≤ R) (hbox : ∀ a ∈ S, ∀ i, |(a i : ℝ)-u i| ≤ R) :
    (S.card : ℝ) ≤ (4*R+3)^n := by
  simpa using ResidueBoxCount.card_le_of_constant_residue 1 S u R hR hbox
    (fun _ _ _ _ _ => Subsingleton.elim _ _)

/-- Lattice counts for arbitrary selected coordinates. Rows need not coincide
with the columns chosen by a separate Hessian-chart construction. -/
theorem card_coordinate_image_le {r : ℕ} (S : Finset (Fin n → ℤ))
    (rows : Fin r → Fin n) (u : Fin r → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hbox : ∀ a ∈ S, ∀ i, |(a (rows i) : ℝ)-u i| ≤ R) :
    ((S.image fun a => fun i => a (rows i)).card : ℝ) ≤ (4*R+3)^r := by
  apply card_le_shifted_real_box _ u R hR
  intro a ha i
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
  exact hbox b hb i

end CubicTenVariables.LocalSupremumWindow
