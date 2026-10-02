import CubicTenVariables.ComplementMergedSieve
import CubicTenVariables.ComplementDeepProfile

/-! Exact identification of the finite-tail sieve profile with the
manuscript's depth-indexed numerical profile. This only changes indices
and reciprocals; it makes no arithmetic counting assertion. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace CubicTenVariables.ComplementSieveProfileBridge
open ComplementDeepWeights
open scoped BigOperators

/-- Actual depth represented by a finite tail index. -/
def depth (i : Fin 5) (k : Fin (5-i.val)) : ℕ := i.val+k.val+2

theorem depth_mem (i : Fin 5) (k : Fin (5-i.val)) :
    depth i k ∈ Finset.Icc (i.val+2) 6 := by
  simp only [depth,Finset.mem_Icc]
  have hi := i.isLt
  have hk := k.isLt
  omega

theorem depth_lt_iff (i : Fin 5) (k l : Fin (5-i.val)) :
    depth i k < depth i l ↔ k < l := by
  simp only [depth,Fin.lt_def]
  omega

/-- Reindex products by the literal consecutive depths. -/
theorem prod_depth {M : Type*} [CommMonoid M] (i : Fin 5) (g : ℕ → M) :
    (∏ k : Fin (5-i.val), g (depth i k)) = ∏ j ∈ Finset.Icc (i.val+2) 6, g j := by
  apply Finset.prod_bij (fun k _ => depth i k)
  · intro k _
    exact depth_mem i k
  · intro k _ l _ hkl
    apply Fin.ext
    dsimp [depth] at hkl
    omega
  · intro j hj
    have hj' := Finset.mem_Icc.mp hj
    refine ⟨⟨j-(i.val+2),by have hi := i.isLt; omega⟩,Finset.mem_univ _,?_⟩
    dsimp [depth]
    omega
  · intro k _
    rfl

/-- Reindex sums by the same bijection. -/
theorem sum_depth {M : Type*} [AddCommMonoid M] (i : Fin 5) (g : ℕ → M) :
    (∑ k : Fin (5-i.val), g (depth i k)) = ∑ j ∈ Finset.Icc (i.val+2) 6, g j := by
  apply Finset.sum_bij (fun k _ => depth i k)
  · intro k _
    exact depth_mem i k
  · intro k _ l _ hkl
    apply Fin.ext
    dsimp [depth] at hkl
    omega
  · intro j hj
    have hj' := Finset.mem_Icc.mp hj
    refine ⟨⟨j-(i.val+2),by have hi := i.isLt; omega⟩,Finset.mem_univ _,?_⟩
    dsimp [depth]
    omega
  · intro k _
    rfl

/-- The actual affine dimensions 8,7,6,4,3 correspond to codimensions
2,3,4,6,7 in the ten-dimensional frequency space. -/
theorem dimension_eq (i : Fin 5) (k : Fin (5-i.val)) :
    (ComplementMergedSieve.dimensionProfile i k : ℝ)+1 = 11-codim (depth i k) := by
  fin_cases i <;> fin_cases k <;>
    norm_num [ComplementMergedSieve.dimensionProfile,ComplementSieveTuple.tailIndex,
      MicrolocalDepthSupportCount.profile,depth,codim]

theorem exponent_eq (i : Fin 5) :
    (ComplementProgressionCounts.profile i : ℝ) = ComplementDeepProfile.exponent (i.val+2) := by
  fin_cases i <;> norm_num [ComplementProgressionCounts.profile,ComplementDeepProfile.exponent,codim]

/-- The height factor has the identical merged-scale product. -/
theorem merged_product_eq (i : Fin 5) (A B : ℕ → ℝ) :
    (∏ k : Fin (5-i.val), A (depth i k)*B (depth i k)) =
      ∏ j ∈ Finset.Icc (i.val+2) 6, A j*B j :=
  prod_depth i (fun j => A j*B j)

/-- Literal equality between the sieve's quotient-form profile and the
manuscript's negative-power profile, with all ordered tail terms retained. -/
theorem profile_eq (i : Fin 5) (A B : ℕ → ℝ) (T : ℝ)
    (hA : ∀ j ∈ Finset.Icc (i.val+2) 6, 1 ≤ A j)
    (hB : ∀ j ∈ Finset.Icc (i.val+2) 6, 1 ≤ B j) :
    StratifiedSieveData.profile (ComplementMergedSieve.dimensionProfile i)
      (fun k => A (depth i k)*B (depth i k)) T (ComplementProgressionCounts.profile i : ℝ) =
        ComplementDeepProfile.profile (i.val+2) A B T := by
  let α : ℝ := ComplementProgressionCounts.profile i
  let d := ComplementMergedSieve.dimensionProfile i
  let R : Fin (5-i.val) → ℝ := fun k => A (depth i k)*B (depth i k)
  have hR (k : Fin (5-i.val)) : 0 ≤ R k := mul_nonneg
    (zero_le_one.trans (hA _ (depth_mem i k))) (zero_le_one.trans (hB _ (depth_mem i k)))
  have hα : α = ComplementDeepProfile.exponent (i.val+2) := exponent_eq i
  have hfirst : (∏ k, (R k)^(α-(d k : ℝ)-1))⁻¹ =
      ∏ j ∈ Finset.Icc (i.val+2) 6,
        (A j*B j)^(11-codim j-ComplementDeepProfile.exponent (i.val+2)) := by
    calc
      _ = ∏ k, ((R k)^(α-(d k : ℝ)-1))⁻¹ := (Finset.prod_inv_distrib _).symm
      _ = ∏ k, (R k)^(11-codim (depth i k)-ComplementDeepProfile.exponent (i.val+2)) := by
        apply Finset.prod_congr rfl
        intro k _
        rw [← Real.rpow_neg (hR k)]
        congr 1
        have hd := dimension_eq i k
        change (d k : ℝ)+1 = _ at hd
        linarith
      _ = _ := prod_depth i (fun j =>
        (A j*B j)^(11-codim j-ComplementDeepProfile.exponent (i.val+2)))
  have htail (j : Fin (5-i.val)) :
      (∏ k, if j < k then (R k)^((d j : ℝ)-(d k : ℝ)) else 1)⁻¹ =
        ∏ n ∈ Finset.Icc (i.val+2) 6,
          (A n*B n)^(if depth i j < n then codim (depth i j)-codim n else 0) := by
    calc
      _ = ∏ k, (if j < k then (R k)^((d j : ℝ)-(d k : ℝ)) else 1)⁻¹ :=
        (Finset.prod_inv_distrib _).symm
      _ = ∏ k, (R k)^(if depth i j < depth i k then
          codim (depth i j)-codim (depth i k) else 0) := by
        apply Finset.prod_congr rfl
        intro k _
        by_cases hjk : j < k
        · rw [if_pos hjk,if_pos ((depth_lt_iff i j k).mpr hjk),← Real.rpow_neg (hR k)]
          congr 1
          have hj := dimension_eq i j
          have hk := dimension_eq i k
          change (d j : ℝ)+1 = _ at hj
          change (d k : ℝ)+1 = _ at hk
          linarith
        · rw [if_neg hjk,if_neg (by intro hh; exact hjk ((depth_lt_iff i j k).mp hh))]
          simp
      _ = _ := prod_depth i (fun n =>
        (A n*B n)^(if depth i j < n then codim (depth i j)-codim n else 0))
  change (1+T^α/(∏ k, (R k)^(α-(d k : ℝ)-1))+
      ∑ j, T^((d j : ℝ)+1)/(∏ k, if j < k then (R k)^((d j : ℝ)-(d k : ℝ)) else 1)) = _
  unfold ComplementDeepProfile.profile
  rw [div_eq_mul_inv,hfirst,hα]
  congr 1
  calc
    _ = ∑ j, T^(11-codim (depth i j))*
        (∏ n ∈ Finset.Icc (i.val+2) 6,
          (A n*B n)^(if depth i j < n then codim (depth i j)-codim n else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [div_eq_mul_inv,htail]
      have hd := dimension_eq i j
      change (d j : ℝ)+1 = _ at hd
      rw [hd]
    _ = _ := sum_depth i (fun h => T^(11-codim h)*
      (∏ n ∈ Finset.Icc (i.val+2) 6,
        (A n*B n)^(if h < n then codim h-codim n else 0)))

end CubicTenVariables.ComplementSieveProfileBridge
