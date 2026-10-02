import HessianTheorem11.UnconditionalValuationPolynomial
import HessianTheorem11.ReducedRelativeOrder

/-! Normalize an arbitrary invertible weighted coordinate frame to SL by
scaling one column. Every weighted flag and actual original-coordinate
degeneration curve is preserved. -/
noncomputable section
namespace HessianTheorem11.UnconditionalSpecialLinearFrame
open MvPolynomial Matrix PolynomialRestriction PolynomialWeightTransport
  RationalDescent ReducedRelative ReducedWeightCurve
variable {K : Type*} [Field K] {n : ℕ}

theorem weightFlag_mul_diagonal (B : Matrix (Fin n) (Fin n) K)
    (s : Fin n → K) (hs : ∀ i, s i ≠ 0) (w : Fin n → ℤ) :
    weightFlag (B * diagonal s) w = weightFlag B w := by
  classical
  funext a
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    have h := (weightFlag B w a).smul_mem (s i)
      (Submodule.subset_span (show (fun j => B j i) ∈
        {v | ∃ k, w k ≤ a ∧ v = fun j => B j k} from ⟨i,hi,rfl⟩))
    have he : (fun j => (B * diagonal s) j i) = s i • (fun j => B j i) := by
      funext j
      simp [mul_diagonal,Pi.smul_apply,smul_eq_mul,mul_comm]
    rwa [he]
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    have h := (weightFlag (B * diagonal s) w a).smul_mem ((s i)⁻¹)
      (Submodule.subset_span (show (fun j => (B * diagonal s) j i) ∈
        {v | ∃ k, w k ≤ a ∧ v = fun j => (B * diagonal s) j k} from ⟨i,hi,rfl⟩))
    have he : (s i)⁻¹ • (fun j => (B * diagonal s) j i) = (fun j => B j i) := by
      funext j
      simp [mul_diagonal,Pi.smul_apply,smul_eq_mul,← mul_assoc,hs i,mul_comm]
    rwa [he] at h

def determinantScale (hn : 0 < n) (B : Matrix (Fin n) (Fin n) K) : Fin n → K :=
  fun i => if i = ⟨0,hn⟩ then B.det⁻¹ else 1

theorem determinantScale_ne_zero (hn : 0 < n) (B : Matrix (Fin n) (Fin n) K)
    (hB : B.det ≠ 0) : ∀ i, determinantScale hn B i ≠ 0 := by
  intro i
  simp only [determinantScale]
  split_ifs <;> simp [hB]

def normalizeMatrix (hn : 0 < n) (B : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) K := B * diagonal (determinantScale hn B)

theorem normalizeMatrix_det (hn : 0 < n) (B : Matrix (Fin n) (Fin n) K)
    (hB : B.det ≠ 0) : (normalizeMatrix hn B).det = 1 := by
  classical
  simp [normalizeMatrix,Matrix.det_mul,Matrix.det_diagonal,determinantScale,hB]

theorem normalizeMatrix_flag (hn : 0 < n) (B : Matrix (Fin n) (Fin n) K)
    (hB : B.det ≠ 0) (w : Fin n → ℤ) :
    weightFlag (normalizeMatrix hn B) w = weightFlag B w :=
  weightFlag_mul_diagonal B _ (determinantScale_ne_zero hn B hB) w

def normalizeFrame (hn : 0 < n) (f : WeightFrame K n) : WeightFrame K n where
  matrix := normalizeMatrix hn f.matrix
  injective := by
    apply Matrix.mulVec_injective_iff_isUnit.mpr
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    have hd : f.matrix.det ≠ 0 := isUnit_iff_ne_zero.mp
      ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp f.injective))
    rw [normalizeMatrix_det hn f.matrix hd]
    exact isUnit_one
  weight := f.weight
  sum_zero := f.sum_zero

@[simp] theorem normalizeFrame_weight (hn : 0 < n) (f : WeightFrame K n) :
    (normalizeFrame hn f).weight = f.weight := rfl

theorem normalizeFrame_det (hn : 0 < n) (f : WeightFrame K n) :
    (normalizeFrame hn f).matrix.det = 1 := by
  apply normalizeMatrix_det
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_injective_iff_isUnit.mp f.injective))

theorem normalizeFrame_flag (hn : 0 < n) (f : WeightFrame K n) :
    (normalizeFrame hn f).flag = f.flag := by
  apply normalizeMatrix_flag
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_injective_iff_isUnit.mp f.injective))

theorem curve_restrict_diagonal (s : Fin n → K) (F : MvPolynomial (Fin n) K)
    (w : Fin n → ℤ) (t : K) :
    curve (restrict (diagonal s) F) w t = restrict (diagonal s) (curve F w t) := by
  ext e
  simp only [coeff_curve,UnconditionalValuationWeights.coeff_restrict_diagonal]
  ring

theorem originalCurve_normalizeFrame (hn : 0 < n) (f : WeightFrame K n)
    (F : MvPolynomial (Fin n) K) (t : K) :
    originalCurve F (normalizeFrame hn f) t = originalCurve F f t := by
  have hu : IsUnit (diagonal (determinantScale hn f.matrix)).det := by
    apply isUnit_iff_ne_zero.mpr
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => determinantScale_ne_zero hn f.matrix
      (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
        (Matrix.mulVec_injective_iff_isUnit.mp f.injective))) i
  simp only [originalCurve,normalizeFrame,normalizeMatrix]
  rw [← restrict_restrict,curve_restrict_diagonal,restrict_restrict,Matrix.mul_inv_rev,
    ← Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hu,Matrix.one_mul]

theorem originalTest_normalizeFrame [Infinite K] (hn : 0 < n) (f : WeightFrame K n)
    {d : ℕ} (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (q : MvPolynomial (Fin n →₀ ℕ) K) :
    originalTest d F (normalizeFrame hn f) q = originalTest d F f q := by
  apply Polynomial.funext
  intro t
  rw [originalTest_eval F hF,originalTest_eval F hF,originalCurve_normalizeFrame]

theorem relativeOrder_normalizeFrame [Infinite K] (hn : 0 < n) (f : WeightFrame K n)
    {d : ℕ} (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (S : Set (MvPolynomial (Fin n) K)) :
    relativeOrder d F S (normalizeFrame hn f) = relativeOrder d F S f := by
  unfold relativeOrder relativeOrderSupport
  simp only [originalTest_normalizeFrame hn f F hF]

end HessianTheorem11.UnconditionalSpecialLinearFrame
