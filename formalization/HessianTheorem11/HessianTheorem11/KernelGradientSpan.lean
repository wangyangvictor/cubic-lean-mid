import HessianTheorem11.NormalQuadrics
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Polarization identifies the common annihilator of kernel quadrics with
the orthogonal complement of the span of their actual gradient values. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Module
variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

def coordinatePairing : LinearMap.BilinForm K (Fin n → K) := dotProductBilin K K

def kernelGradientSpan (F : MvPolynomial (Fin n) K) (L : Submodule K (Fin n → K)) :
    Submodule K (Fin n → K) := Submodule.span K (gradient F '' (L : Set (Fin n → K)))

theorem coordinatePairing_nondegenerate :
    (coordinatePairing (K := K) (n := n)).Nondegenerate := by
  intro x hx
  ext i
  have h := hx (Pi.single i 1)
  simpa [coordinatePairing, dotProductBilin] using h

theorem coordinatePairing_reflexive : (coordinatePairing (K := K) (n := n)).IsRefl := by
  intro x y h
  change dotProduct y x = 0
  rw [dotProduct_comm]
  exact h

theorem polarization_diagonal_eq_gradient
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3) (v u : Fin n → K) :
    polarization F v u u = 2 * dotProduct v (gradient F u) := by
  rw [polarization, hessian_mulVec_self hF, dotProduct_smul]
  simp [smul_eq_mul]

theorem kernelQuadraticAnnihilator_eq_orthogonal_kernelGradientSpan
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (L : Submodule K (Fin n → K)) :
    kernelQuadraticAnnihilator F L =
      (coordinatePairing (K := K) (n := n)).orthogonal (kernelGradientSpan F L) := by
  classical
  ext v
  constructor
  · intro hv
    have hle : kernelGradientSpan F L ≤ LinearMap.ker
        ((coordinatePairing (K := K) (n := n)) v) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨u, hu, rfl⟩
      change dotProduct v (gradient F u) = 0
      have h := hv u hu u hu
      rw [polarization_diagonal_eq_gradient F hF] at h
      exact (mul_eq_zero.mp h).resolve_left (by norm_num)
    intro y hy
    change dotProduct y v = 0
    rw [dotProduct_comm]
    exact hle hy
  · intro hv
    have hdiag (u : Fin n → K) (hu : u ∈ L) : polarization F v u u = 0 := by
      rw [polarization_diagonal_eq_gradient F hF]
      have h := hv (gradient F u) (Submodule.subset_span (Set.mem_image_of_mem _ hu))
      change dotProduct (gradient F u) v = 0 at h
      rw [dotProduct_comm] at h
      rw [h, mul_zero]
    intro u hu w hw
    have h := hdiag (u+w) (L.add_mem hu hw)
    rw [polarization_add_second, polarization_add_third hF,
      polarization_add_third hF, hdiag u hu, hdiag w hw,
      polarization_swap_last hF v w u] at h
    linear_combination (1/2 : K) * h

/-- The actual gradient values on the Hessian kernel span the conormal
space in the thirteen-variable incidence equality case. -/
theorem kernelGradientSpan_eq_conormal_of_thirteen
    (F : MvPolynomial (Fin 13) K) (hF : F.IsHomogeneous 3)
    (hsemi : WeightSemistable F) (x : Fin 13 → K) (hx : eval x F = 0)
    (T : Submodule K (Fin 13 → K)) (hxT : x ∈ T)
    (hxL : x ∉ LinearMap.ker (hessian F x).mulVecLin)
    (hann : T ≤ kernelQuadraticAnnihilator F (LinearMap.ker (hessian F x).mulVecLin))
    (hdim : finrank K T + finrank K (LinearMap.ker (hessian F x).mulVecLin) = 16) :
    kernelGradientSpan F (LinearMap.ker (hessian F x).mulVecLin) =
      (coordinatePairing (K := K) (n := 13)).orthogonal T := by
  have h := kernel_quadratic_annihilator_eq_of_thirteen F hF hsemi x hx T hxT hxL hann hdim
  rw [kernelQuadraticAnnihilator_eq_orthogonal_kernelGradientSpan F hF] at h
  rw [← h, LinearMap.BilinForm.orthogonal_orthogonal
    coordinatePairing_nondegenerate coordinatePairing_reflexive]

end HessianTheorem11
