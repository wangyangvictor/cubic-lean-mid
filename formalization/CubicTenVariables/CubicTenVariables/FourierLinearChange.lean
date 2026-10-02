import CubicTenVariables.ProjectiveFourierIdentity
import HessianTheorem11.PolynomialRestriction
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Module.Submodule.Map

/-! Exact changes of physical coordinates and dual frequencies for the
literal finite-field Fourier sums. The transpose, zero-frequency subtraction,
and finite subspace sums are retained explicitly. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.FourierLinearChange
open MvPolynomial Matrix HessianTheorem11.PolynomialRestriction
open FiniteFieldFourier ProjectiveFourierIdentity
open scoped BigOperators Classical
variable {K : Type*} [Field K] [Fintype K] {n : ℕ}

omit [Fintype K] in
/-- The actual transpose is dual to the physical coordinate matrix. -/
theorem transpose_pairing (A : Matrix (Fin n) (Fin n) K) (v x : Fin n → K) :
    dotProduct (A.transpose.mulVec v) x = dotProduct v (A.mulVec x) := by
  rw [mulVec_transpose,dotProduct_mulVec]

/-- Changing the physical variables by A sends the frequency v to Aᵀv.
This identity is valid for arbitrary polynomials and additive characters. -/
theorem zeroFiberSum_restrict_transpose (ψ : AddChar K ℂ)
    (F : MvPolynomial (Fin n) K) (A : Matrix (Fin n) (Fin n) K)
    (hA : IsUnit A) (v : Fin n → K) :
    zeroFiberSum ψ (restrict A F) (A.transpose.mulVec v) = zeroFiberSum ψ F v := by
  let E : (Fin n → K) ≃ (Fin n → K) := Equiv.ofBijective A.mulVec
    ⟨mulVec_injective_iff_isUnit.mpr hA,mulVec_surjective_iff_isUnit.mpr hA⟩
  unfold zeroFiberSum
  simp only [Finset.sum_filter]
  apply Fintype.sum_equiv E
  intro x
  simp only [eval_restrict,transpose_pairing,Equiv.ofBijective_apply,E]

omit [Fintype K] in
theorem transpose_mulVec_eq_zero_iff (A : Matrix (Fin n) (Fin n) K)
    (hA : IsUnit A) (v : Fin n → K) : A.transpose.mulVec v = 0 ↔ v = 0 := by
  have hi := mulVec_injective_iff_isUnit.mpr ((isUnit_transpose A).mpr hA)
  constructor
  · intro hv
    apply hi
    simpa only [mulVec_zero] using hv
  · rintro rfl
    exact mulVec_zero _

/-- The manuscript's subtraction at frequency zero is preserved exactly. -/
theorem normalized_restrict_transpose (ψ : AddChar K ℂ)
    (F : MvPolynomial (Fin n) K) (A : Matrix (Fin n) (Fin n) K)
    (hA : IsUnit A) (v : Fin n → K) :
    normalizedFourierSum ψ (restrict A F) (A.transpose.mulVec v) =
      normalizedFourierSum ψ F v := by
  simp only [normalizedFourierSum,zeroFiberSum_restrict_transpose ψ F A hA,
    transpose_mulVec_eq_zero_iff A hA]

/-- Equivalent inverse-transpose formulation, useful when the new
frequency plane has already been put in coordinate form. -/
theorem normalized_restrict (ψ : AddChar K ℂ)
    (F : MvPolynomial (Fin n) K) (A : Matrix (Fin n) (Fin n) K)
    (hA : IsUnit A) (w : Fin n → K) :
    normalizedFourierSum ψ (restrict A F) w =
      normalizedFourierSum ψ F ((A.transpose)⁻¹.mulVec w) := by
  have ht : IsUnit A.transpose.det := (isUnit_iff_isUnit_det _).mp ((isUnit_transpose A).mpr hA)
  have h := normalized_restrict_transpose ψ F A hA ((A.transpose)⁻¹.mulVec w)
  simpa only [mulVec_mulVec,mul_nonsing_inv _ ht,one_mulVec] using h

/-- The exact finite second moment on a frequency set transports to
its actual image under the transpose matrix. -/
theorem finite_second_moment_image (ψ : AddChar K ℂ)
    (F : MvPolynomial (Fin n) K) (A : Matrix (Fin n) (Fin n) K)
    (hA : IsUnit A) (V : Finset (Fin n → K)) :
    (∑ w ∈ V.image A.transpose.mulVec, ‖normalizedFourierSum ψ (restrict A F) w‖^2) =
      ∑ v ∈ V, ‖normalizedFourierSum ψ F v‖^2 := by
  rw [Finset.sum_image]
  · simp only [normalized_restrict_transpose ψ F A hA]
  · intro x hx y hy hxy
    exact (mulVec_injective_iff_isUnit.mpr ((isUnit_transpose A).mpr hA)) hxy

/-- In particular, every finite-field linear subspace has exactly the
same second moment after the physical and dual coordinate changes. -/
theorem submodule_second_moment (ψ : AddChar K ℂ)
    (F : MvPolynomial (Fin n) K) (A : Matrix (Fin n) (Fin n) K)
    (hA : IsUnit A) (L : Submodule K (Fin n → K)) :
    (∑ w : L.map A.transpose.mulVecLin,
      ‖normalizedFourierSum ψ (restrict A F) (w : Fin n → K)‖^2) =
      ∑ v : L, ‖normalizedFourierSum ψ F (v : Fin n → K)‖^2 := by
  let E := Submodule.equivMapOfInjective A.transpose.mulVecLin
    (mulVec_injective_iff_isUnit.mpr ((isUnit_transpose A).mpr hA)) L
  symm
  apply Fintype.sum_equiv E.toEquiv
  intro v
  exact congrArg (fun z : ℂ => ‖z‖^2)
    (normalized_restrict_transpose ψ F A hA (v : Fin n → K)).symm

end CubicTenVariables.FourierLinearChange
