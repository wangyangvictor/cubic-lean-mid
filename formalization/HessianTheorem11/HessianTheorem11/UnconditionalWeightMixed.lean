import HessianTheorem11.UnconditionalWeightPolyhedron
import HessianTheorem11.UnconditionalWeightIntegral

/-! The fixed-coordinate relative optimizer: some character bounds are
zero (existence of a limit), while others are one (positive target-ideal
order). Its unique rational least-length point is proved, not assumed. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace HessianTheorem11.UnconditionalWeightMixed
open UnconditionalWeightOptimization
variable {n : ℕ}

def character (a : Fin n → ℤ) : WeightSpace n →ₗ[ℝ] ℝ :=
  UnconditionalWeightPolyhedron.row (fun i => (a i : ℚ))

def feasible (S T : Finset (Fin n → ℤ)) : Set (WeightSpace n) :=
  {w | weightSum w = 0 ∧ (∀ a ∈ S, 0 ≤ character a w) ∧ ∀ a ∈ T, 1 ≤ character a w}

def MinimumNorm (S T : Finset (Fin n → ℤ)) (w : WeightSpace n) : Prop :=
  w ∈ feasible S T ∧ ∀ v ∈ feasible S T, ‖w‖ ≤ ‖v‖

def constraintMatrix (S T : Finset (Fin n → ℤ)) : Matrix (Fin 2 ⊕ (S ⊕ T)) (Fin n) ℚ :=
  Sum.elim (fun i _ => if i = 0 then 1 else -1)
    (Sum.elim (fun a j => (a.val j : ℚ)) (fun a j => (a.val j : ℚ)))

def constraintBounds (S T : Finset (Fin n → ℤ)) : (Fin 2 ⊕ (S ⊕ T)) → ℚ :=
  Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (fun _ => 1))

theorem feasible_iff_polyhedron (S T : Finset (Fin n → ℤ)) (w : WeightSpace n) :
    w ∈ feasible S T ↔ w ∈ UnconditionalWeightPolyhedron.feasible
      (constraintMatrix S T) (constraintBounds S T) := by
  classical
  constructor
  · rintro ⟨hw,hS,hT⟩ i
    rcases i with i | a | a
    · fin_cases i <;> simp [constraintMatrix,constraintBounds,UnconditionalWeightPolyhedron.row,
        show (∑ j, w j) = 0 from hw,Finset.sum_neg_distrib]
    · simpa [constraintMatrix,constraintBounds,character] using hS a.val a.property
    · simpa [constraintMatrix,constraintBounds,character] using hT a.val a.property
  · intro h
    refine ⟨?_,?_,?_⟩
    rotate_left
    · intro a ha
      simpa [constraintMatrix,constraintBounds,character] using h (Sum.inr (Sum.inl ⟨a,ha⟩))
    · intro a ha
      simpa [constraintMatrix,constraintBounds,character] using h (Sum.inr (Sum.inr ⟨a,ha⟩))
    have hp := h (Sum.inl 0)
    have hm := h (Sum.inl 1)
    change weightSum w = 0
    have hp' : 0 ≤ ∑ j, w j := by
      simpa [constraintMatrix,constraintBounds,UnconditionalWeightPolyhedron.row] using hp
    have hm' : 0 ≤ -(∑ j, w j) := by
      simpa [constraintMatrix,constraintBounds,UnconditionalWeightPolyhedron.row,
        Finset.sum_neg_distrib] using hm
    change (∑ j, w j) = 0
    linarith

theorem minimumNorm_iff_polyhedron (S T : Finset (Fin n → ℤ)) (w : WeightSpace n) :
    MinimumNorm S T w ↔ UnconditionalWeightPolyhedron.MinimumNorm
      (constraintMatrix S T) (constraintBounds S T) w := by
  simp only [MinimumNorm,UnconditionalWeightPolyhedron.MinimumNorm,feasible_iff_polyhedron]

theorem minimumNorm_unique {S T : Finset (Fin n → ℤ)} {u v : WeightSpace n}
    (hu : MinimumNorm S T u) (hv : MinimumNorm S T v) : u = v :=
  UnconditionalWeightPolyhedron.minimumNorm_unique
    ((minimumNorm_iff_polyhedron S T u).mp hu) ((minimumNorm_iff_polyhedron S T v).mp hv)

theorem exists_unique_minimumNorm (S T : Finset (Fin n → ℤ))
    (hne : (feasible S T).Nonempty) : ∃! w, MinimumNorm S T w := by
  obtain ⟨w,hw,hu⟩ := UnconditionalWeightPolyhedron.exists_unique_minimumNorm
    (constraintMatrix S T) (constraintBounds S T)
    (hne.imp fun w hw => (feasible_iff_polyhedron S T w).mp hw)
  exact ⟨w,(minimumNorm_iff_polyhedron S T w).mpr hw,
    fun v hv => hu v ((minimumNorm_iff_polyhedron S T v).mp hv)⟩

theorem minimumNorm_rational {S T : Finset (Fin n → ℤ)} {w : WeightSpace n}
    (hw : MinimumNorm S T w) : ∃ u : Fin n → ℚ, ∀ j, (u j : ℝ) = w j :=
  UnconditionalWeightPolyhedron.minimumNorm_rational ((minimumNorm_iff_polyhedron S T w).mp hw)

theorem feasible_ne_zero {S T : Finset (Fin n → ℤ)} (hT : T.Nonempty)
    {w : WeightSpace n} (hw : w ∈ feasible S T) : w ≠ 0 := by
  obtain ⟨a,ha⟩ := hT
  intro hz
  have h := hw.2.2 a ha
  rw [hz,map_zero] at h
  norm_num at h

theorem normalized_bound {S T : Finset (Fin n → ℤ)} (hT : T.Nonempty)
    {w : WeightSpace n} (hw : MinimumNorm S T w)
    (v : WeightSpace n) (hv : weightSum v = 0)
    (hvS : ∀ a ∈ S, 0 ≤ character a v) (b : ℝ) (hb : 0 < b)
    (hvT : ∀ a ∈ T, b ≤ character a v) : b / ‖v‖ ≤ 1 / ‖w‖ := by
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr (feasible_ne_zero hT hw.1)
  have hfeas : b⁻¹ • v ∈ feasible S T := by
    refine ⟨by simp [hv],?_,?_⟩
    · intro a ha
      rw [map_smul]
      exact mul_nonneg (inv_nonneg.mpr hb.le) (hvS a ha)
    · intro a ha
      rw [map_smul]
      change 1 ≤ b⁻¹ * character a v
      calc
        1 = b⁻¹ * b := (inv_mul_cancel₀ hb.ne').symm
        _ ≤ _ := mul_le_mul_of_nonneg_left (hvT a ha) (inv_nonneg.mpr hb.le)
  have hmin := hw.2 _ hfeas
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hb)] at hmin
  have hvpos : 0 < ‖v‖ := by nlinarith [inv_pos.mpr hb]
  apply (div_le_div_iff₀ hvpos hwpos).mpr
  have hh := mul_le_mul_of_nonneg_left hmin hb.le
  simpa only [← mul_assoc,mul_inv_cancel₀ hb.ne',one_mul] using hh

theorem minimumNorm_active {S T : Finset (Fin n → ℤ)} (hT : T.Nonempty)
    {w : WeightSpace n} (hw : MinimumNorm S T w) : ∃ a ∈ T, character a w = 1 := by
  obtain ⟨a,ha,hmin⟩ := Finset.exists_mem_eq_inf' hT (fun a => character a w)
  have hlevel : ∀ b ∈ T, character a w ≤ character b w := by
    intro b hb
    rw [← hmin]
    exact Finset.inf'_le _ hb
  have hpos : 0 < character a w := lt_of_lt_of_le zero_lt_one (hw.1.2.2 a ha)
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr (feasible_ne_zero hT hw.1)
  have h := normalized_bound hT hw w hw.1.1 hw.1.2.1 _ hpos hlevel
  have hh := (div_le_div_iff₀ hn hn).mp h
  refine ⟨a,ha,le_antisymm ?_ (hw.1.2.2 a ha)⟩
  nlinarith

theorem exists_integral_optimal_ray (S T : Finset (Fin n → ℤ))
    (hT : T.Nonempty) (hne : (feasible S T).Nonempty) :
    ∃ (w : WeightSpace n) (N : ℤ) (z : Fin n → ℤ),
      MinimumNorm S T w ∧ 0 < N ∧
      WithLp.toLp 2 (fun j => (z j : ℝ)) = (N : ℝ) • w ∧
      (∑ j, z j) = 0 ∧ (∀ a ∈ S, 0 ≤ ∑ j, a j * z j) ∧
      (∀ a ∈ T, 0 < ∑ j, a j * z j) ∧ z ≠ 0 := by
  obtain ⟨w,hw,_⟩ := exists_unique_minimumNorm S T hne
  obtain ⟨N,z,hN,hz⟩ := exists_positive_integral_multiple w (minimumNorm_rational hw)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hweight (a : Fin n → ℤ) :
      (∑ j, (a j : ℝ) * (z j : ℝ)) = (N : ℝ) * character a w := by
    have h := congrArg (character a) hz
    rw [map_smul] at h
    simpa [character,UnconditionalWeightPolyhedron.row] using h
  have hsum : ∑ j, z j = 0 := by
    have h := congrArg weightSum hz
    rw [map_smul,hw.1.1,smul_zero] at h
    change (∑ j, (z j : ℝ)) = 0 at h
    exact_mod_cast h
  have hS : ∀ a ∈ S, 0 ≤ ∑ j, a j * z j := by
    intro a ha
    have h : 0 ≤ ∑ j, (a j : ℝ) * (z j : ℝ) := by
      rw [hweight]
      exact mul_nonneg hNr.le (hw.1.2.1 a ha)
    exact_mod_cast h
  have hT' : ∀ a ∈ T, 0 < ∑ j, a j * z j := by
    intro a ha
    have h : 0 < ∑ j, (a j : ℝ) * (z j : ℝ) := by
      rw [hweight]
      exact mul_pos hNr (lt_of_lt_of_le zero_lt_one (hw.1.2.2 a ha))
    exact_mod_cast h
  refine ⟨w,N,z,hw,hN,hz,hsum,hS,hT',?_⟩
  intro he
  obtain ⟨a,ha⟩ := hT
  have h := hT' a ha
  simp [he] at h

end HessianTheorem11.UnconditionalWeightMixed
