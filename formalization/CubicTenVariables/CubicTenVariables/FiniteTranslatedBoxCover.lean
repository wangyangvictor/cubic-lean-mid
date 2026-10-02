import CubicTenVariables.ResidueBoxCount

/-! A finite partition of any translated integer box into boxes of a
prescribed positive real radius. The centers and cardinality are explicit. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.FiniteTranslatedBoxCover
open scoped BigOperators
variable {n : ℕ}

def tag (u : Fin n → ℝ) (A : ℝ) (v : Fin n → ℤ) : Fin n → ℤ :=
  fun i => ⌊((v i : ℝ)-u i)/A⌋

def center (u : Fin n → ℝ) (A : ℝ) (k : Fin n → ℤ) : Fin n → ℝ :=
  fun i => u i+A*(k i : ℝ)

def cells (V : Finset (Fin n → ℤ)) (u : Fin n → ℝ) (A : ℝ) :
    Finset (Fin n → ℤ) := by
  classical
  exact V.image (tag u A)

def piece (V : Finset (Fin n → ℤ)) (u : Fin n → ℝ) (A : ℝ)
    (k : Fin n → ℤ) : Finset (Fin n → ℤ) := by
  classical
  exact V.filter (fun v => tag u A v = k)

/-- Every frequency belongs to a box of radius A at its assigned center. -/
theorem point_box (u : Fin n → ℝ) (A : ℝ) (hA : 0 < A)
    (v : Fin n → ℤ) (i : Fin n) :
    |(v i : ℝ)-center u A (tag u A v) i| ≤ A := by
  have hlo := (le_div_iff₀ hA).mp (Int.floor_le (((v i : ℝ)-u i)/A))
  have hhi := (div_lt_iff₀ hA).mp (Int.lt_floor_add_one (((v i : ℝ)-u i)/A))
  change |(v i : ℝ)-(u i+A*(⌊((v i : ℝ)-u i)/A⌋ : ℤ))| ≤ A
  apply abs_le.mpr
  constructor <;> nlinarith

theorem piece_box (V : Finset (Fin n → ℤ)) (u : Fin n → ℝ)
    (A : ℝ) (hA : 0 < A) (k : Fin n → ℤ) :
    ∀ v ∈ piece V u A k, ∀ i, |(v i : ℝ)-center u A k i| ≤ A := by
  classical
  intro v hv i
  obtain ⟨_,hk⟩ := Finset.mem_filter.mp hv
  rw [← hk]
  exact point_box u A hA v i

theorem tag_bound (u : Fin n → ℝ) (L A : ℝ) (hA : 0 < A)
    (v : Fin n → ℤ) (hbox : ∀ i, |(v i : ℝ)-u i| ≤ L) (i : Fin n) :
    |(tag u A v i : ℝ)| ≤ L/A+1 := by
  have hx : |((v i : ℝ)-u i)/A| ≤ L/A := by
    rw [abs_div,abs_of_pos hA]
    exact div_le_div_of_nonneg_right (hbox i) hA.le
  have hx' := abs_le.mp hx
  have hlo := Int.floor_le (((v i : ℝ)-u i)/A)
  have hhi := Int.lt_floor_add_one (((v i : ℝ)-u i)/A)
  dsimp [tag]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- A uniform cardinality bound without any alignment or integrality
condition on the original center or on the new radius. -/
theorem card_cells_le (V : Finset (Fin n → ℤ)) (u : Fin n → ℝ)
    (L A : ℝ) (hL : 0 ≤ L) (hA : 0 < A)
    (hbox : ∀ v ∈ V, ∀ i, |(v i : ℝ)-u i| ≤ L) :
    ((cells V u A).card : ℝ) ≤ (7*(1+L/A))^n := by
  classical
  have hcount := ResidueBoxCount.card_le_of_constant_residue 1 (cells V u A)
    (fun _ => 0) (L/A+1) (by positivity)
    (fun k hk i => by
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hk
      simpa only [sub_zero] using tag_bound u L A hA v (hbox v hv) i)
    (fun _ _ _ _ _ => Subsingleton.elim _ _)
  apply hcount.trans
  apply pow_le_pow_left₀ (by positivity)
  have : 0 ≤ L/A := div_nonneg hL hA.le
  norm_num
  linarith

/-- Every used center stays within one new radius of the original box. -/
theorem center_norm_le (V : Finset (Fin n → ℤ)) (u : Fin n → ℝ)
    (L A : ℝ) (hL : 0 ≤ L) (hA : 0 < A)
    (hbox : ∀ v ∈ V, ∀ i, |(v i : ℝ)-u i| ≤ L)
    (k : Fin n → ℤ) (hk : k ∈ cells V u A) :
    ‖center u A k‖ ≤ ‖u‖+L+A := by
  classical
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hk
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [Real.norm_eq_abs]
  have hu : |u i| ≤ ‖u‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm u i
  have hvu := hbox v hv i
  have hcv := point_box u A hA v i
  have htri := abs_sub_le (center u A (tag u A v) i) (v i : ℝ) (u i)
  rw [abs_sub_comm (center u A (tag u A v) i) (v i : ℝ)] at htri
  have hlast := abs_add_le (center u A (tag u A v) i-u i) (u i)
  rw [sub_add_cancel] at hlast
  linarith

/-- The pieces partition the original finite frequency set exactly. -/
theorem sum_pieces (V : Finset (Fin n → ℤ)) (u : Fin n → ℝ)
    (A : ℝ) (f : (Fin n → ℤ) → ℝ) :
    (∑ k ∈ cells V u A, ∑ v ∈ piece V u A k, f v) = ∑ v ∈ V, f v := by
  classical
  simp only [piece,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  have hm : tag u A v ∈ cells V u A := Finset.mem_image_of_mem _ hv
  simp [hm]

/-- A bound for each small-box piece gives the expected covering factor.
No sign condition on f is needed because the partition is exact. -/
theorem sum_le_of_piece_bound (V : Finset (Fin n → ℤ)) (u : Fin n → ℝ)
    (L A M : ℝ) (hL : 0 ≤ L) (hA : 0 < A) (hM : 0 ≤ M)
    (hbox : ∀ v ∈ V, ∀ i, |(v i : ℝ)-u i| ≤ L)
    (f : (Fin n → ℤ) → ℝ)
    (hbound : ∀ k ∈ cells V u A, (∑ v ∈ piece V u A k, f v) ≤ M) :
    (∑ v ∈ V, f v) ≤ (7*(1+L/A))^n*M := by
  rw [← sum_pieces V u A f]
  calc
    _ ≤ ∑ _k ∈ cells V u A, M := Finset.sum_le_sum hbound
    _ = ((cells V u A).card : ℝ)*M := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (card_cells_le V u L A hL hA hbox) hM

end CubicTenVariables.FiniteTranslatedBoxCover
