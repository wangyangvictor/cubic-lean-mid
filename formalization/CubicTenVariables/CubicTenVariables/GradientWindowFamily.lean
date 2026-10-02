import CubicTenVariables.GradientWindowActiveCount
import CubicTenVariables.ScaledGradientSliceVolume
import CubicTenVariables.SelectedCoordinateVolume
import CubicTenVariables.FiniteFiberVolumeSum
import CubicTenVariables.LocalSupremumWindow

/-! Finite families of actual gradient windows. The selected output rows
are grouped independently of the input coordinates used for Fubini. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.GradientWindowFamily
open MvPolynomial MeasureTheory RealRegularGradientChart SelectedGradientCoordinates
open SelectedGradientSliceVolume GradientWindowScaling GradientWindowActiveCount
open scoped BigOperators ENNReal
variable {F : MvPolynomial (Fin 10) ℝ}

/-- A fixed selected-output fiber has uniformly bounded total window volume. -/
theorem exists_fixed_rows_bound (D : Data F) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (β δ L : ℝ), β ≠ 0 → 0 ≤ δ → 0 ≤ L →
      ∀ (b : Fin 7 → ℤ) (T : Finset (Fin 10 → ℤ))
        (a : (Fin 10 → ℤ) → (Fin 10 → ℤ)),
      (∀ v ∈ T, selected D v=b) →
      (∀ v ∈ T, ∀ i, |(a v i : ℝ)-(v i : ℝ)| ≤ L) →
      (∑ v ∈ T, (volume (window F D.box 1 β (fun i => (a v i : ℝ)) δ)).toReal) ≤
        C*(1+δ+L)^3*min 1 ((δ/|β|)^7) := by
  classical
  obtain ⟨A,hA,hsize⟩ := ScaledGradientSliceVolume.exists_uniform_bound F D
  obtain ⟨K,hK,hcount⟩ := GradientWindowActiveCount.exists_bound D
  let Q : ℝ := (4*D.radius)^3
  have hr := D.radius_pos
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  let C : ℝ := (1+Q)*K*A
  have hC : 1 ≤ C := by
    dsimp [C]
    have h₁ : 1 ≤ (1+Q)*K := by nlinarith
    nlinarith
  refine ⟨C,hC,?_⟩
  intro β δ L hβ hδ hL b T a hrow hnear
  let S : (Fin 10 → ℤ) → Set ((Fin 7 → ℝ) × (Complement D.cols → ℝ)) :=
    fun v => {zw | combine D.cols D.cols_injective zw.1 zw.2 ∈
      window F D.box 1 β (fun i => (a v i : ℝ)) δ}
  have hS (v : Fin 10 → ℤ) : MeasurableSet (S v) :=
    (ScaledGradientSliceVolume.measurableSet_window F D β _ δ).preimage
      (SelectedCoordinateVolume.measurable_combine D.cols D.cols_injective)
  have houter : ∀ v ∈ T, S v ⊆ Set.univ ×ˢ ScaledGradientSliceVolume.complementBox F D := by
    intro v _ zw hzw
    exact ⟨Set.mem_univ _,ScaledGradientSliceVolume.mem_complementBox_of_mem_slice
      F D β _ δ zw.2 zw.1 hzw⟩
  have hm : 0 ≤ min 1 ((δ/|β|)^7) := le_min (by norm_num) (by positivity)
  have hvol (v : Fin 10 → ℤ) :
      (volume.prod volume) (S v)=volume (window F D.box 1 β (fun i => (a v i : ℝ)) δ) :=
    (SelectedCoordinateVolume.measurePreserving_combine D.cols D.cols_injective).measure_preimage
      (ScaledGradientSliceVolume.measurableSet_window F D β _ δ).nullMeasurableSet
  have hb := FiniteFiberVolumeSum.sum_prod_toReal_le volume volume T S (fun v _ => hS v)
    (ScaledGradientSliceVolume.complementBox F D) houter
    (ScaledGradientSliceVolume.volume_complementBox_ne_top F D)
    (K*(1+δ+L)^3) (A*min 1 ((δ/|β|)^7))
    (mul_nonneg (zero_le_one.trans hK) (by positivity))
    (mul_nonneg (zero_le_one.trans hA) hm)
    (fun w _ v _ => hsize β hβ δ hδ _ w)
    (fun w _ => hcount β δ L hδ hL w b T a hrow hnear)
  simp only [hvol,ScaledGradientSliceVolume.volume_complementBox,
    ENNReal.toReal_ofReal (show 0 ≤ (4*D.radius)^3 from hQ)] at hb
  calc
    _ ≤ Q*(K*(1+δ+L)^3)*(A*min 1 ((δ/|β|)^7)) := hb
    _ ≤ (1+Q)*(K*(1+δ+L)^3)*(A*min 1 ((δ/|β|)^7)) := by
      gcongr
      linarith
    _ = _ := by dsimp [C]; ring

/-- All selected output rows are counted after the fixed-row Fubini estimate.
The constant precedes every scalar, width, cutoff and finite family. -/
theorem exists_bound (D : Data F) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (β δ B L : ℝ), β ≠ 0 → 0 ≤ δ → 0 ≤ B → 0 ≤ L →
      ∀ (T : Finset (Fin 10 → ℤ)) (a : (Fin 10 → ℤ) → (Fin 10 → ℤ)),
      (∀ v ∈ T, ∀ i, |(a v i : ℝ)| ≤ B) →
      (∀ v ∈ T, ∀ i, |(a v i : ℝ)-(v i : ℝ)| ≤ L) →
      (∑ v ∈ T, (volume (window F D.box 1 β (fun i => (a v i : ℝ)) δ)).toReal) ≤
        C*(1+B+L)^7*(1+δ+L)^3*min 1 ((δ/|β|)^7) := by
  classical
  obtain ⟨C,hC,hfixed⟩ := exists_fixed_rows_bound D
  refine ⟨4^7*C,by nlinarith,?_⟩
  intro β δ B L hβ hδ hB hL T a hfreq hnear
  let Q := T.image (selected D)
  let g := fun v => (volume (window F D.box 1 β (fun i => (a v i : ℝ)) δ)).toReal
  have hcenter (v : Fin 10 → ℤ) (hv : v ∈ T) (i : Fin 10) : |(v i : ℝ)| ≤ B+L := by
    calc
      _ ≤ |(a v i : ℝ)|+|(a v i : ℝ)-(v i : ℝ)| := by
        simpa only [sub_zero,abs_sub_comm,add_comm] using abs_sub_le (v i : ℝ) (a v i : ℝ) 0
      _ ≤ B+L := add_le_add (hfreq v hv i) (hnear v hv i)
  have hQ : (Q.card : ℝ) ≤ 4^7*(1+B+L)^7 := by
    have hc := LocalSupremumWindow.card_coordinate_image_le T D.rows (fun _ => 0)
      (B+L) (add_nonneg hB hL) (fun v hv i => by simpa using hcenter v hv (D.rows i))
    calc
      _ ≤ (4*(B+L)+3)^7 := hc
      _ ≤ (4*(1+B+L))^7 := pow_le_pow_left₀ (by positivity) (by linarith) 7
      _ = _ := mul_pow _ _ _
  have hsplit : (∑ v ∈ T, g v)=∑ b ∈ Q, ∑ v ∈ T with selected D v=b, g v := by
    exact (Finset.sum_fiberwise_of_maps_to (fun v hv => Finset.mem_image.mpr ⟨v,hv,rfl⟩) g).symm
  have hm : 0 ≤ min 1 ((δ/|β|)^7) := le_min (by norm_num) (by positivity)
  calc
    _ = ∑ b ∈ Q, ∑ v ∈ T with selected D v=b, g v := hsplit
    _ ≤ ∑ _b ∈ Q, C*(1+δ+L)^3*min 1 ((δ/|β|)^7) := by
      apply Finset.sum_le_sum
      intro b _
      exact hfixed β δ L hβ hδ hL b (T.filter fun v => selected D v=b) a
        (fun v hv => (Finset.mem_filter.mp hv).2)
        (fun v hv => hnear v (Finset.mem_filter.mp hv).1)
    _ = (Q.card : ℝ)*(C*(1+δ+L)^3*min 1 ((δ/|β|)^7)) := by simp [nsmul_eq_mul]
    _ ≤ (4^7*(1+B+L)^7)*(C*(1+δ+L)^3*min 1 ((δ/|β|)^7)) := by
      exact mul_le_mul_of_nonneg_right hQ (by positivity)
    _ = _ := by ring

end CubicTenVariables.GradientWindowFamily
