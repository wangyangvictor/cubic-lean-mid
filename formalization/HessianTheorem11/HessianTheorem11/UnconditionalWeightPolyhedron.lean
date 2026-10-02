import HessianTheorem11.UnconditionalWeightRationalLinear
import HessianTheorem11.UnconditionalWeightOptimization

/-! Actual rational minimum-norm points of finite rational polyhedra.
This extends the zero-instability optimizer to the mixed zero/positive
bounds required by relative instability. No polyhedral optimization or
rationality statement is an external input. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace HessianTheorem11.UnconditionalWeightPolyhedron
open Filter
open scoped Topology
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
variable {n : ℕ} {ι : Type*} [Fintype ι]

def row (a : Fin n → ℚ) : Space n →ₗ[ℝ] ℝ where
  toFun w := ∑ j, (a j : ℝ) * w j
  map_add' u v := by simp [mul_add,Finset.sum_add_distrib]
  map_smul' t w := by simp [Finset.mul_sum]; congr 1; funext j; ring

def feasible (A : Matrix ι (Fin n) ℚ) (b : ι → ℚ) : Set (Space n) :=
  {w | ∀ i, (b i : ℝ) ≤ row (A i) w}

def MinimumNorm (A : Matrix ι (Fin n) ℚ) (b : ι → ℚ) (w : Space n) : Prop :=
  w ∈ feasible A b ∧ ∀ v ∈ feasible A b, ‖w‖ ≤ ‖v‖

theorem feasible_closed (A : Matrix ι (Fin n) ℚ) (b : ι → ℚ) :
    IsClosed (feasible A b) := by
  have he : feasible A b = ⋂ i, {w | (b i : ℝ) ≤ row (A i) w} := by
    ext w
    simp [feasible]
  rw [he]
  exact isClosed_iInter fun i => isClosed_le continuous_const (row (A i)).continuous_of_finiteDimensional

theorem feasible_convex (A : Matrix ι (Fin n) ℚ) (b : ι → ℚ) :
    Convex ℝ (feasible A b) := by
  intro u hu v hv a c ha hc hac i
  change (b i : ℝ) ≤ row (A i) (a • u + c • v)
  rw [map_add,map_smul,map_smul]
  change (b i : ℝ) ≤ a * row (A i) u + c * row (A i) v
  calc
    (b i : ℝ) = a * (b i : ℝ) + c * (b i : ℝ) := by rw [← add_mul,hac,one_mul]
    _ ≤ a * row (A i) u + c * row (A i) v := add_le_add
      (mul_le_mul_of_nonneg_left (hu i) ha) (mul_le_mul_of_nonneg_left (hv i) hc)

theorem minimumNorm_inf {A : Matrix ι (Fin n) ℚ} {b : ι → ℚ} {w : Space n}
    (hw : MinimumNorm A b w) :
    ‖(0 : Space n)-w‖ = ⨅ z : feasible A b, ‖(0 : Space n)-z‖ := by
  letI : Nonempty (feasible A b) := ⟨⟨w,hw.1⟩⟩
  simp only [zero_sub,norm_neg]
  apply le_antisymm
  · exact le_ciInf fun z => hw.2 z z.property
  · exact ciInf_le (f := fun z : feasible A b => ‖(z : Space n)‖)
      ⟨0,by rintro _ ⟨z,rfl⟩; exact norm_nonneg _⟩ (⟨w,hw.1⟩ : feasible A b)

theorem minimumNorm_inner {A : Matrix ι (Fin n) ℚ} {b : ι → ℚ} {w : Space n}
    (hw : MinimumNorm A b w) (v : Space n) (hv : v ∈ feasible A b) :
    0 ≤ inner ℝ w (v-w) := by
  have h := (norm_eq_iInf_iff_real_inner_le_zero (feasible_convex A b) hw.1).mp
    (minimumNorm_inf hw) v hv
  simp only [zero_sub,inner_neg_left] at h
  linarith

theorem minimumNorm_unique {A : Matrix ι (Fin n) ℚ} {b : ι → ℚ} {u v : Space n}
    (hu : MinimumNorm A b u) (hv : MinimumNorm A b v) : u = v := by
  have h1 := minimumNorm_inner hu v hv.1
  have h2 := minimumNorm_inner hv u hu.1
  simp only [inner_sub_right,real_inner_self_eq_norm_sq] at h1 h2
  rw [real_inner_comm] at h2
  have hn : ‖u-v‖ = 0 := by
    have he := norm_sub_sq_real u v
    nlinarith [norm_nonneg (u-v)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

theorem exists_unique_minimumNorm (A : Matrix ι (Fin n) ℚ) (b : ι → ℚ)
    (hne : (feasible A b).Nonempty) : ∃! w, MinimumNorm A b w := by
  obtain ⟨w,hw,he⟩ := exists_norm_eq_iInf_of_complete_convex hne
    (feasible_closed A b).isComplete (feasible_convex A b) (0 : Space n)
  have hmin : MinimumNorm A b w := by
    refine ⟨hw,?_⟩
    intro v hv
    have h := ciInf_le (f := fun z : feasible A b => ‖(0 : Space n)-z‖)
      ⟨0,by rintro _ ⟨z,rfl⟩; exact norm_nonneg _⟩ ⟨v,hv⟩
    rw [← he] at h
    simpa only [zero_sub,norm_neg] using h
  exact ⟨w,hmin,fun v hv => minimumNorm_unique hv hmin⟩

theorem feasible_near_tight_direction {A : Matrix ι (Fin n) ℚ} {b : ι → ℚ}
    {w : Space n} (hw : w ∈ feasible A b) (v : Space n)
    (htight : ∀ i, row (A i) w = (b i : ℝ) → row (A i) v = 0) :
    ∀ᶠ t : ℝ in 𝓝 0, w + t • v ∈ feasible A b := by
  change ∀ᶠ t : ℝ in 𝓝 0, ∀ i, (b i : ℝ) ≤ row (A i) (w+t • v)
  rw [Filter.eventually_all]
  intro i
  by_cases ht : row (A i) w = (b i : ℝ)
  · exact Filter.Eventually.of_forall fun t => by simp [ht,htight i ht]
  · have hstrict : (b i : ℝ) < row (A i) w := lt_of_le_of_ne (hw i) (Ne.symm ht)
    have hc : Continuous (fun t : ℝ => row (A i) (w+t • v)) :=
      (row (A i)).continuous_of_finiteDimensional.comp
        (continuous_const.add (continuous_id.smul continuous_const))
    exact ((hc.tendsto 0).eventually_const_lt (by simpa using hstrict)).mono fun t ht => ht.le

theorem minimumNorm_orthogonal_tight {A : Matrix ι (Fin n) ℚ} {b : ι → ℚ}
    {w : Space n} (hw : MinimumNorm A b w) (v : Space n)
    (htight : ∀ i, row (A i) w = (b i : ℝ) → row (A i) v = 0) :
    inner ℝ w v = 0 := by
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp
    (feasible_near_tight_direction hw.1 v htight)
  have hp : w + (ε/2) • v ∈ feasible A b := hball (by
    rw [Real.dist_eq,sub_zero,abs_of_pos (by linarith : 0 < ε/2)]
    linarith)
  have hm : w + (-(ε/2)) • v ∈ feasible A b := hball (by
    rw [Real.dist_eq,sub_zero,abs_neg,abs_of_pos (by linarith : 0 < ε/2)]
    linarith)
  have h1 := minimumNorm_inner hw _ hp
  have h2 := minimumNorm_inner hw _ hm
  simp only [add_sub_cancel_left,real_inner_smul_right] at h1 h2
  nlinarith

/-- Rationality is proved from the actual tight rational equations and
the orthogonality of the optimizer to their common kernel. -/
theorem minimumNorm_rational {A : Matrix ι (Fin n) ℚ} {b : ι → ℚ} {w : Space n}
    (hw : MinimumNorm A b w) : ∃ u : Fin n → ℚ, ∀ j, (u j : ℝ) = w j := by
  classical
  let Tight := {i : ι // row (A i) w = (b i : ℝ)}
  let T : Matrix Tight (Fin n) ℚ := fun i j => A i.val j
  let c : Tight → ℚ := fun i => b i.val
  apply UnconditionalWeightRationalLinear.rational_of_normal_solution T c (fun j => w j)
  · intro i
    exact i.property
  · intro v hv
    have ht : ∀ i, row (A i) w = (b i : ℝ) → row (A i) (WithLp.toLp 2 v) = 0 := by
      intro i hi
      exact hv (⟨i,hi⟩ : Tight)
    have h := minimumNorm_orthogonal_tight hw (WithLp.toLp 2 v) ht
    simpa only [PiLp.inner_apply,RCLike.inner_apply',conj_trivial] using h

theorem exists_rational_minimumNorm (A : Matrix ι (Fin n) ℚ) (b : ι → ℚ)
    (hne : (feasible A b).Nonempty) :
    ∃ u : Fin n → ℚ, MinimumNorm A b (WithLp.toLp 2 (fun j => (u j : ℝ))) := by
  obtain ⟨w,hw,_⟩ := exists_unique_minimumNorm A b hne
  obtain ⟨u,hu⟩ := minimumNorm_rational hw
  refine ⟨u,?_⟩
  have he : WithLp.toLp 2 (fun j => (u j : ℝ)) = w := by ext j; exact hu j
  rwa [he]

end HessianTheorem11.UnconditionalWeightPolyhedron
