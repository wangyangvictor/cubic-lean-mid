import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Rationality of solutions of rational linear equations orthogonal to
their kernel. The proof uses a Q-linear retraction of R, actual dual-map
factorization, and positivity of a sum of real squares. No rational-polyhedron
or optimization input is used. -/
noncomputable section
namespace HessianTheorem11.UnconditionalWeightRationalLinear
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def rationalDot (u : ι → ℚ) : (ι → ℚ) →ₗ[ℚ] ℚ where
  toFun z := ∑ j, u j * z j
  map_add' z v := by simp [mul_add,Finset.sum_add_distrib]
  map_smul' a z := by simp [Finset.mul_sum]; congr 1; funext j; ring

/-- Every rational functional annihilating a rational matrix kernel is
an actual rational linear combination of the matrix rows. -/
theorem rational_row_combination (A : Matrix κ ι ℚ) (u : ι → ℚ)
    (hu : ∀ z : ι → ℚ, A.mulVec z = 0 → ∑ j, u j * z j = 0) :
    ∃ c : κ → ℚ, ∀ j, u j = ∑ i, c i * A i j := by
  classical
  have hmem : rationalDot u ∈ (LinearMap.ker A.mulVecLin).dualAnnihilator := by
    apply (Submodule.mem_dualAnnihilator (rationalDot u)).mpr
    intro z hz
    exact hu z hz
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hmem
  obtain ⟨g,hg⟩ := hmem
  refine ⟨fun i => g (Pi.single i 1),?_⟩
  intro j
  have he := LinearMap.congr_fun hg (Pi.single j 1)
  have hsum : A.mulVec (Pi.single j 1) = ∑ i, A i j • Pi.single i 1 := by
    ext i
    simp [Pi.single_apply]
  change g (A.mulVec (Pi.single j 1)) = rationalDot u (Pi.single j 1) at he
  rw [hsum,map_sum] at he
  simpa [rationalDot,Pi.single_apply,mul_comm] using he.symm

/-- Rational kernel annihilation remains true after extension to real
coordinates; this follows from the actual row combination above. -/
theorem rational_annihilator_real (A : Matrix κ ι ℚ) (u : ι → ℚ)
    (hu : ∀ z : ι → ℚ, A.mulVec z = 0 → ∑ j, u j * z j = 0)
    (v : ι → ℝ) (hv : ∀ i, ∑ j, (A i j : ℝ) * v j = 0) :
    ∑ j, (u j : ℝ) * v j = 0 := by
  obtain ⟨c,hc⟩ := rational_row_combination A u hu
  simp_rw [hc,Rat.cast_sum,Rat.cast_mul,Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc,← Finset.mul_sum,hv,mul_zero]
  exact Finset.sum_const_zero

def rationalRetraction : ℝ →ₗ[ℚ] ℚ := (Algebra.linearMap ℚ ℝ).leftInverse

@[simp] theorem rationalRetraction_rat (q : ℚ) : rationalRetraction (q : ℝ) = q := by
  exact LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr (algebraMap ℚ ℝ).injective) q

@[simp] theorem rationalRetraction_rat_mul (q : ℚ) (a : ℝ) :
    rationalRetraction ((q : ℝ) * a) = q * rationalRetraction a := by
  exact rationalRetraction.map_smul q a

@[simp] theorem rationalRetraction_mul_rat (a : ℝ) (q : ℚ) :
    rationalRetraction (a * (q : ℝ)) = rationalRetraction a * q := by
  rw [mul_comm,rationalRetraction_rat_mul,mul_comm]

/-- The real normal solution of a rational linear system is rational.
The system may be rectangular, dependent, or have zero rows. -/
theorem rational_of_normal_solution (A : Matrix κ ι ℚ) (b : κ → ℚ) (w : ι → ℝ)
    (hAw : ∀ i, ∑ j, (A i j : ℝ) * w j = (b i : ℝ))
    (hnormal : ∀ v : ι → ℝ, (∀ i, ∑ j, (A i j : ℝ) * v j = 0) →
      ∑ j, w j * v j = 0) : ∃ u : ι → ℚ, ∀ j, (u j : ℝ) = w j := by
  let u : ι → ℚ := fun j => rationalRetraction (w j)
  have hAu : ∀ i, ∑ j, A i j * u j = b i := by
    intro i
    have h := congrArg rationalRetraction (hAw i)
    simpa only [map_sum,rationalRetraction_rat_mul,rationalRetraction_rat,u] using h
  have hAnn : ∀ z : ι → ℚ, A.mulVec z = 0 → ∑ j, u j * z j = 0 := by
    intro z hz
    have hzero : ∀ i, ∑ j, (A i j : ℝ) * (z j : ℝ) = 0 := by
      intro i
      have h : ∑ j, A i j * z j = 0 := congrFun hz i
      exact_mod_cast h
    have h := congrArg rationalRetraction (hnormal (fun j => (z j : ℝ)) hzero)
    simp only [map_sum,map_zero] at h
    simpa only [rationalRetraction_mul_rat,u] using h
  let v : ι → ℝ := fun j => w j - (u j : ℝ)
  have hAv : ∀ i, ∑ j, (A i j : ℝ) * v j = 0 := by
    intro i
    simp only [v,mul_sub,Finset.sum_sub_distrib,hAw]
    have h : ∑ j, (A i j : ℝ) * (u j : ℝ) = (b i : ℝ) := by exact_mod_cast hAu i
    rw [h,sub_self]
  have hwv := hnormal v hAv
  have huv := rational_annihilator_real A u hAnn v hAv
  have hsq : ∑ j, (v j)^2 = 0 := by
    calc
      ∑ j, (v j)^2 = ∑ j, (w j - (u j : ℝ)) * v j := by simp only [v,pow_two]
      _ = (∑ j, w j * v j) - ∑ j, (u j : ℝ) * v j := by
        simp only [sub_mul,Finset.sum_sub_distrib]
      _ = 0 := by rw [hwv,huv,sub_self]
  refine ⟨u,?_⟩
  intro j
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (v i))).mp hsq j
    (Finset.mem_univ j)
  have hvj : v j = 0 := eq_zero_of_pow_eq_zero hj
  exact (sub_eq_zero.mp hvj).symm

end HessianTheorem11.UnconditionalWeightRationalLinear
