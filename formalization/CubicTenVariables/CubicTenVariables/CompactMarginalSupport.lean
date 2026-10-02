import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Support and continuity of a compactly supported marginal

The marginal is the actual integral over the remaining real coordinates. Its
support is contained in the first projection of the original support, and all
slices vanish outside the same compact set in the remaining coordinates.
-/

noncomputable section

namespace CubicTenVariables.CompactMarginal

open MeasureTheory

/-- The actual marginal in the first real coordinate. -/
def marginal {m : ℕ} (a : ℝ × (Fin m → ℝ) → ℝ) (t : ℝ) : ℝ :=
  ∫ y : Fin m → ℝ, a (t, y)

/-- Every slice vanishes outside the projection of the full topological support. -/
theorem slice_eq_zero_of_notMem_projection {m : ℕ}
    (a : ℝ × (Fin m → ℝ) → ℝ) (t : ℝ) (y : Fin m → ℝ)
    (hy : y ∉ Prod.snd '' tsupport a) : a (t, y) = 0 := by
  by_contra hne
  exact hy ⟨(t, y), subset_tsupport a hne, rfl⟩

/-- The marginal vanishes outside the first projection of the full support. -/
theorem marginal_eq_zero_of_notMem_projection {m : ℕ}
    (a : ℝ × (Fin m → ℝ) → ℝ) (t : ℝ)
    (ht : t ∉ Prod.fst '' tsupport a) : marginal a t = 0 := by
  have hz : ∀ y : Fin m → ℝ, a (t, y) = 0 := by
    intro y
    by_contra hne
    exact ht ⟨(t, y), subset_tsupport a hne, rfl⟩
  simp [marginal, hz]

/-- The full slice integral can be restricted to the same projected support for every `t`.
No regularity or compactness assumption is needed for this identity. -/
theorem marginal_eq_setIntegral {m : ℕ}
    (a : ℝ × (Fin m → ℝ) → ℝ) (t : ℝ) :
    marginal a t = ∫ y in Prod.snd '' tsupport a, a (t, y) := by
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero
    (slice_eq_zero_of_notMem_projection a t)).symm

theorem support_marginal_subset_projection {m : ℕ}
    (a : ℝ × (Fin m → ℝ) → ℝ) :
    Function.support (marginal a) ⊆ Prod.fst '' tsupport a := by
  intro t ht
  by_contra hnot
  exact ht (marginal_eq_zero_of_notMem_projection a t hnot)

theorem tsupport_marginal_subset_projection {m : ℕ}
    (a : ℝ × (Fin m → ℝ) → ℝ) (hcompact : HasCompactSupport a) :
    tsupport (marginal a) ⊆ Prod.fst '' tsupport a :=
  closure_minimal (support_marginal_subset_projection a)
    (hcompact.isCompact.image continuous_fst).isClosed

/-- Compact support of the actual marginal, independently of its continuity. -/
theorem hasCompactSupport_marginal {m : ℕ}
    (a : ℝ × (Fin m → ℝ) → ℝ) (hcompact : HasCompactSupport a) :
    HasCompactSupport (marginal a) :=
  HasCompactSupport.intro (hcompact.isCompact.image continuous_fst)
    (marginal_eq_zero_of_notMem_projection a)

theorem hasCompactSupport_slice {m : ℕ}
    (a : ℝ × (Fin m → ℝ) → ℝ) (hcompact : HasCompactSupport a) (t : ℝ) :
    HasCompactSupport (fun y : Fin m → ℝ => a (t, y)) :=
  HasCompactSupport.intro (hcompact.isCompact.image continuous_snd)
    (slice_eq_zero_of_notMem_projection a t)

/-- Every continuous slice is integrable over the remaining real coordinates. -/
theorem integrable_slice {m : ℕ}
    (a : ℝ × (Fin m → ℝ) → ℝ) (ha : Continuous a)
    (hcompact : HasCompactSupport a) (t : ℝ) :
    Integrable (fun y : Fin m → ℝ => a (t, y)) :=
  (ha.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    (hasCompactSupport_slice a hcompact t)

/-- Integrating a continuous compactly supported function gives a continuous marginal. -/
theorem continuous_marginal {m : ℕ}
    (a : ℝ × (Fin m → ℝ) → ℝ) (ha : Continuous a)
    (hcompact : HasCompactSupport a) : Continuous (marginal a) := by
  have heq : marginal a = fun t => ∫ y in Prod.snd '' tsupport a, a (t, y) :=
    funext (marginal_eq_setIntegral a)
  rw [heq]
  exact continuous_parametric_integral_of_continuous
    (f := fun t y => a (t, y)) ha (hcompact.isCompact.image continuous_snd)

end CubicTenVariables.CompactMarginal
