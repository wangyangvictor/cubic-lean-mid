import CubicTenVariables.GenericHyperplaneFrameOpen
import CubicTenVariables.ReducedVertexBaseChange

/-! Literal equality between a full-rank generic-hyperplane frame image
and the zero space of the full generic equation. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace CubicTenVariables.GenericHyperplaneFrameKernel
open MvPolynomial GenericReducedProjectiveHyperplane
open scoped Matrix

variable {K : Type*} [Field K] {n : ℕ}

def normal (u : Fin (n+1) → K) : Module.Dual K (Fin (n+1) → K) where
  toFun x := ∑ i, u i * x i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem range_eq_ker (u : Fin (n+1) → K) (hu : u 0 ≠ 0)
    (B : Matrix (Fin (n+1)) (Fin n) K) (hB : Function.Injective B.mulVec)
    (hcol : ∀ j, ∑ i, u i * B i j = 0) :
    LinearMap.range B.mulVecLin = LinearMap.ker (normal u) := by
  classical
  have hle : LinearMap.range B.mulVecLin ≤ LinearMap.ker (normal u) := by
    rintro x ⟨y, rfl⟩
    change (∑ i, u i * (B.mulVec y) i) = 0
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hcol, zero_mul, Finset.sum_const_zero]
  have hnormal : normal u ≠ 0 := by
    intro hz
    have h := congrArg (fun f : Module.Dual K (Fin (n+1) → K) => f (Pi.single 0 1)) hz
    have hv : normal u (Pi.single 0 1) = u 0 := by
      simp [normal, Pi.single_apply]
    change normal u (Pi.single 0 1) = 0 at h
    rw [hv] at h
    exact hu h
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hnormal
  simp only [Module.finrank_pi, Fintype.card_fin] at hk
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [LinearMap.finrank_range_of_inj hB]
  simp only [Module.finrank_pi, Fintype.card_fin]
  omega

/-- The frame spans the actual generic hyperplane, not just a subspace
inside it. -/
theorem generic_range_iff
    {k : Type*} [Field k] (L : Type*) [Field L]
    [Algebra (ParameterRing k n) L] [IsFractionRing (ParameterRing k n) L]
    (B : Matrix (Fin (n+1)) (Fin n) L) (hB : Function.Injective B.mulVec)
    (hcol : ∀ j, ∑ i, algebraMap (ParameterRing k n) L (X i) * B i j = 0)
    (x : Fin (n+1) → L) :
    (∃ y, B.mulVec y = x) ↔ eval x (equation (k := k) (n := n) L) = 0 := by
  let u : Fin (n+1) → L := fun i => algebraMap (ParameterRing k n) L (X i)
  have hu : u 0 ≠ 0 := by
    exact (map_ne_zero_iff _ (IsFractionRing.injective (ParameterRing k n) L)).mpr
      (X_ne_zero (0 : Fin (n+1)))
  have he := range_eq_ker u hu B hB hcol
  change x ∈ LinearMap.range B.mulVecLin ↔ _
  rw [he]
  change (∑ i, u i * x i) = 0 ↔ _
  simp only [equation, map_sum, map_mul, eval_C, eval_X, u]


/-- The same image equality holds on geometric points after any field extension. -/
theorem generic_range_iff_after_fieldExtension
    {k : Type*} [Field k] (L : Type*) [Field L]
    [Algebra (ParameterRing k n) L] [IsFractionRing (ParameterRing k n) L]
    (E : Type*) [Field E] [Algebra L E]
    (B : Matrix (Fin (n+1)) (Fin n) L) (hB : Function.Injective B.mulVec)
    (hcol : ∀ j, ∑ i, algebraMap (ParameterRing k n) L (X i) * B i j = 0)
    (x : Fin (n+1) → E) :
    (∃ y, (B.map (algebraMap L E)).mulVec y = x) ↔
      eval x (map (algebraMap L E) (equation (k := k) (n := n) L)) = 0 := by
  let φ := algebraMap L E
  let u : Fin (n+1) → E := fun i => φ (algebraMap (ParameterRing k n) L (X i))
  have hu : u 0 ≠ 0 := by
    apply (map_ne_zero φ).mpr
    exact (map_ne_zero_iff _ (IsFractionRing.injective (ParameterRing k n) L)).mpr
      (X_ne_zero (0 : Fin (n+1)))
  have hcols : ∀ j, ∑ i, u i * (B.map φ) i j = 0 := by
    intro j
    have he := congrArg φ (hcol j)
    simpa only [map_sum, map_mul, map_zero, Matrix.map_apply, u] using he
  have he := range_eq_ker u hu (B.map φ)
    (ReducedVertexBaseChange.map_frame_injective B hB) hcols
  change x ∈ LinearMap.range (B.map φ).mulVecLin ↔ _
  rw [he]
  change (∑ i, u i * x i) = 0 ↔ _
  simp only [equation, map_sum, map_mul, map_C, map_X, eval_C, eval_X, u, φ]

end CubicTenVariables.GenericHyperplaneFrameKernel
