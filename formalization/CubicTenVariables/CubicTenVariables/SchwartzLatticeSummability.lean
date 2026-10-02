import CubicTenVariables.LatticeFrequencyTail
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Topology.ContinuousMap.Compact

/-! Uniform absolute convergence of integer translates of an actual Schwartz
function on the coordinate space, with its existing sup norm. No Fourier or
Poisson identity is assumed here. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.SchwartzLatticeSummability
open scoped BigOperators SchwartzMap
variable {n : ℕ}

/-- A nonsingular summable lattice decay weight when `n < N`. -/
def decay (N : ℕ) (z : Fin n → ℤ) : ℝ :=
  (1 + ‖(fun i => (z i : ℝ))‖) ^ (-(N : ℝ))

theorem decay_nonneg (N : ℕ) (z : Fin n → ℤ) : 0 ≤ decay N z :=
  Real.rpow_nonneg (by positivity) _

theorem summable_decay (N : ℕ) (hN : n < N) : Summable (decay (n := n) N) := by
  classical
  have hzero : Summable (fun z : Fin n → ℤ => if z = 0 then (1 : ℝ) else 0) :=
    (hasSum_ite_eq (0 : Fin n → ℤ) (1 : ℝ)).summable
  have hsum := hzero.add (LatticeFrequencyTail.summable_norm_rpow N hN)
  apply Summable.of_nonneg_of_le (decay_nonneg N) _ hsum
  intro z
  by_cases hz : z = 0
  · subst z
    simp [decay, ← Pi.zero_def]
  · have hcast : (fun i => (z i : ℝ)) ≠ 0 := by
      intro h
      apply hz
      funext i
      have hi : (z i : ℝ) = 0 := by simpa using congrFun h i
      exact_mod_cast hi
    simp only [if_neg hz, zero_add]
    exact Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr hcast)
      (by linarith) (neg_nonpos.mpr (Nat.cast_nonneg _))

/-- Every prescribed order of decay is uniform on a bounded translation ball.
The constant depends on `f`, the radius and the order, before `x` and `z`. -/
theorem exists_uniform_decay (f : SchwartzMap (Fin n → ℝ) ℂ) (N : ℕ)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Fin n → ℝ, ‖x‖ ≤ R → ∀ z : Fin n → ℤ,
      ‖f (x + fun i => (z i : ℝ))‖ ≤ C * decay N z := by
  let A : ℝ := 2 ^ N * (Finset.Iic (N, 0)).sup
    (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f
  have hA : 0 ≤ A := by positivity
  have hbound (y : Fin n → ℝ) : (1 + ‖y‖) ^ N * ‖f y‖ ≤ A := by
    simpa only [norm_iteratedFDeriv_zero] using
      (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
        (m := (N, 0)) (k := N) (n := 0) le_rfl le_rfl f y)
  refine ⟨(1 + R) ^ N * A, by positivity, ?_⟩
  intro x hx z
  let y : Fin n → ℝ := fun i => (z i : ℝ)
  have hy : ‖y‖ ≤ ‖x + y‖ + ‖x‖ := by
    simpa only [add_sub_cancel_left] using norm_sub_le (x + y) x
  have hcompare : 1 + ‖y‖ ≤ (1 + R) * (1 + ‖x + y‖) := by
    nlinarith [norm_nonneg (x + y), mul_nonneg hR (norm_nonneg (x + y))]
  have hp : (1 + ‖y‖) ^ N * ‖f (x + y)‖ ≤ (1 + R) ^ N * A := by
    calc
      _ ≤ ((1 + R) * (1 + ‖x + y‖)) ^ N * ‖f (x + y)‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hcompare N)
          (norm_nonneg _)
      _ = (1 + R) ^ N * ((1 + ‖x + y‖) ^ N * ‖f (x + y)‖) := by
        rw [mul_pow, mul_assoc]
      _ ≤ (1 + R) ^ N * A := mul_le_mul_of_nonneg_left (hbound _) (by positivity)
  have hpos : 0 < (1 + ‖y‖) ^ N := by positivity
  have hfinal : ‖f (x + y)‖ ≤ ((1 + R) ^ N * A) / (1 + ‖y‖) ^ N :=
    (le_div_iff₀ hpos).2 (by simpa [mul_comm] using hp)
  simpa [decay, y, Real.rpow_neg_natCast, zpow_neg, zpow_natCast, div_eq_mul_inv]
    using hfinal

/-- A single nonnegative summable majorant for all translates in any bounded
set. This includes the empty set and dimension zero. -/
theorem exists_majorant_of_isBounded (f : SchwartzMap (Fin n → ℝ) ℂ)
    (K : Set (Fin n → ℝ)) (hK : Bornology.IsBounded K) :
    ∃ g : (Fin n → ℤ) → ℝ, (∀ z, 0 ≤ g z) ∧ Summable g ∧
      ∀ x ∈ K, ∀ z : Fin n → ℤ, ‖f (x + fun i => (z i : ℝ))‖ ≤ g z := by
  obtain ⟨R, hR, hbound⟩ := hK.exists_pos_norm_le
  obtain ⟨C, hC, hCbound⟩ := exists_uniform_decay f (n + 1) R hR.le
  refine ⟨fun z => C * decay (n + 1) z, fun z => mul_nonneg hC (decay_nonneg _ _),
    (summable_decay (n + 1) (by omega)).mul_left C, ?_⟩
  intro x hx z
  exact hCbound x (hbound x hx) z

theorem exists_majorant_of_isCompact (f : SchwartzMap (Fin n → ℝ) ℂ)
    (K : Set (Fin n → ℝ)) (hK : IsCompact K) :
    ∃ g : (Fin n → ℤ) → ℝ, (∀ z, 0 ≤ g z) ∧ Summable g ∧
      ∀ x ∈ K, ∀ z : Fin n → ℤ, ‖f (x + fun i => (z i : ℝ))‖ ≤ g z :=
  exists_majorant_of_isBounded f K hK.isBounded

theorem summable_norm_translate (f : SchwartzMap (Fin n → ℝ) ℂ) (x : Fin n → ℝ) :
    Summable (fun z : Fin n → ℤ => ‖f (x + fun i => (z i : ℝ))‖) := by
  obtain ⟨g, _, hg, hbound⟩ := exists_majorant_of_isCompact f {x} isCompact_singleton
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hbound x (by simp)) hg

theorem summable_translate (f : SchwartzMap (Fin n → ℝ) ℂ) (x : Fin n → ℝ) :
    Summable (fun z : Fin n → ℤ => f (x + fun i => (z i : ℝ))) :=
  (summable_norm_translate f x).of_norm

/-- A lattice translate as a continuous map, for compact restriction norms. -/
def translate (f : SchwartzMap (Fin n → ℝ) ℂ) (z : Fin n → ℤ) :
    C((Fin n → ℝ), ℂ) :=
  ⟨fun x => f (x + fun i => (z i : ℝ)), f.continuous.comp (continuous_id.add continuous_const)⟩

theorem summable_norm_restrict (f : SchwartzMap (Fin n → ℝ) ℂ)
    (K : TopologicalSpace.Compacts (Fin n → ℝ)) :
    Summable (fun z : Fin n → ℤ => ‖(translate f z).restrict K‖) := by
  obtain ⟨g, hg0, hg, hbound⟩ := exists_majorant_of_isCompact f K K.isCompact
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun z => ?_) hg
  rw [ContinuousMap.norm_le _ (hg0 z)]
  intro x
  exact hbound x.1 x.2 z

/-- Convergence in the compact-open topology of continuous maps. -/
theorem summable_translate_continuousMap (f : SchwartzMap (Fin n → ℝ) ℂ) :
    Summable (translate f) :=
  ContinuousMap.summable_of_locally_summable_norm (summable_norm_restrict f)

/-- The literal pointwise lattice periodization is continuous. -/
theorem continuous_periodization (f : SchwartzMap (Fin n → ℝ) ℂ) :
    Continuous (fun x : Fin n → ℝ => ∑' z : Fin n → ℤ,
      f (x + fun i => (z i : ℝ))) := by
  have heq : (fun x : Fin n → ℝ => ∑' z : Fin n → ℤ,
      f (x + fun i => (z i : ℝ))) = (∑' z : Fin n → ℤ, translate f z) := by
    funext x
    exact (ContinuousMap.hasSum_apply (summable_translate_continuousMap f).hasSum x).tsum_eq
  rw [heq]
  exact (∑' z : Fin n → ℤ, translate f z).continuous

end CubicTenVariables.SchwartzLatticeSummability
