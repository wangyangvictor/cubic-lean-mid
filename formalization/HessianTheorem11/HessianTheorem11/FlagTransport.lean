import HessianTheorem11.Polarization
import HessianTheorem11.Semistability
import HessianTheorem11.PolynomialWeightTransport

/-! Weighted flags and changes of splitting. All statements here are linear
algebra and polynomial substitution, with no geometric input. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Module

variable {K : Type*} [Field K] {n : ℕ}

def weightFlag (B : Matrix (Fin n) (Fin n) K) (w : Fin n → ℤ) :
    ℤ → Submodule K (Fin n → K) :=
  fun a => Submodule.span K {v | ∃ i, w i ≤ a ∧ v = fun j => B j i}

def frameEquiv (B : Matrix (Fin n) (Fin n) K) (hB : Function.Injective B.mulVec) :
    (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  LinearEquiv.ofInjectiveEndo B.mulVecLin hB

theorem frameEquiv_apply (B : Matrix (Fin n) (Fin n) K)
    (hB : Function.Injective B.mulVec) (v : Fin n → K) :
    frameEquiv B hB v = B.mulVec v := rfl

theorem frameEquiv_symm_column (B : Matrix (Fin n) (Fin n) K)
    (hB : Function.Injective B.mulVec) (j : Fin n) :
    (frameEquiv B hB).symm (fun i => B i j) = Pi.single j 1 := by
  apply (frameEquiv B hB).injective
  simp only [LinearEquiv.apply_symm_apply, frameEquiv_apply]
  exact (Matrix.mulVec_single_one _ _).symm

theorem inverse_coordinate_zero_of_mem_weightFlag
    (B : Matrix (Fin n) (Fin n) K) (hB : Function.Injective B.mulVec)
    (w : Fin n → ℤ) (a : ℤ) (v : Fin n → K) (hv : v ∈ weightFlag B w a)
    (i : Fin n) (hi : a < w i) : (frameEquiv B hB).symm v i = 0 := by
  classical
  let f := (LinearMap.proj i).comp (frameEquiv B hB).symm.toLinearMap
  have hker : weightFlag B w a ≤ LinearMap.ker f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    change (frameEquiv B hB).symm (fun k => B k j) i = 0
    rw [frameEquiv_symm_column]
    have hij : i ≠ j := by rintro rfl; omega
    simp [hij]
  exact hker hv

def frameTransition (B C : Matrix (Fin n) (Fin n) K)
    (hB : Function.Injective B.mulVec) : Matrix (Fin n) (Fin n) K :=
  fun i j => (frameEquiv B hB).symm (fun k => C k j) i

theorem matrix_mul_frameTransition (B C : Matrix (Fin n) (Fin n) K)
    (hB : Function.Injective B.mulVec) : B * frameTransition B C hB = C := by
  ext i j
  change B.mulVec ((frameEquiv B hB).symm (fun k => C k j)) i = C i j
  exact congrFun ((frameEquiv B hB).apply_symm_apply (fun k => C k j)) i

theorem frameTransition_weight_monotone
    (B C : Matrix (Fin n) (Fin n) K) (w : Fin n → ℤ)
    (hB : Function.Injective B.mulVec) (hflags : weightFlag B w = weightFlag C w)
    (i j : Fin n) (hne : frameTransition B C hB i j ≠ 0) : w i ≤ w j := by
  by_contra hnot
  apply hne
  apply inverse_coordinate_zero_of_mem_weightFlag B hB w (w j)
  · rw [hflags]
    exact Submodule.subset_span ⟨j, le_rfl, rfl⟩
  · omega

theorem positiveWeights_of_same_weightFlag
    (F : MvPolynomial (Fin n) K) (B C : Matrix (Fin n) (Fin n) K)
    (w : Fin n → ℤ) (hB : Function.Injective B.mulVec)
    (hflags : weightFlag B w = weightFlag C w)
    (hpositive : HasPositiveWeights (PolynomialRestriction.restrict B F) w) :
    HasPositiveWeights (PolynomialRestriction.restrict C F) w := by
  have hp := PolynomialWeightTransport.hasPositiveWeights_restrict_of_entry_weights
    (frameTransition B C hB) w w (frameTransition_weight_monotone B C w hB hflags)
    (PolynomialRestriction.restrict B F) hpositive
  rwa [PolynomialWeightTransport.restrict_restrict, matrix_mul_frameTransition] at hp

end HessianTheorem11
