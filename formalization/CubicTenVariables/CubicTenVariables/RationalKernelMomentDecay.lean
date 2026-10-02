import CubicTenVariables.RationalPlaneMomentDecay
import CubicTenVariables.IntegralLinearKernelContainment

/-! The extension-field moment limit for any fixed integral equation
model of an eight-dimensional rational linear space. Different equation
models are compared by a proved rational row relation, so their reductions
are not silently identified. -/

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace CubicTenVariables.RationalKernelMomentDecay
open MvPolynomial Matrix HessianTheorem11 ProjectiveFourierIdentity RationalPlaneReduction
open Filter
open scoped BigOperators Classical Topology

def planeRows {n : ℕ} (e : Fin 2 ↪ Fin n) (A : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin 2) (Fin n) ℤ := fun j i => A i (e j)

theorem ker_planeRows {n : ℕ} (e : Fin 2 ↪ Fin n) (A : Matrix (Fin n) (Fin n) ℤ)
    (K : Type*) [Field K] :
    LinearMap.ker ((planeRows e A).map (Int.castRingHom K)).mulVecLin = plane e A K := by
  ext v
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, funext_iff, Pi.zero_apply, mem_plane]
  rfl

theorem exists_kernel_to_plane {n r : ℕ} (B : Matrix (Fin r) (Fin n) ℤ)
    (e : Fin 2 ↪ Fin n) (A : Matrix (Fin n) (Fin n) ℤ)
    (h : LinearMap.ker (B.map (Int.castRingHom ℚ)).mulVecLin ≤ plane e A ℚ) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ p : ℕ, ¬ p ∣ D →
      ∀ (K : Type*) [Field K] [CharP K p],
        LinearMap.ker (B.map (Int.castRingHom K)).mulVecLin ≤ plane e A K := by
  simpa only [ker_planeRows] using
    IntegralLinearKernelContainment.exists_uniform_containment B (planeRows e A)
      (by simpa only [ker_planeRows] using h)

theorem exists_decay_ten
    (smooth : Literature.SmoothInfinityGeometricIntegrality)
    (spread : CubicGenericIntegralityUniform.Uniform)
    (weil : Literature.AffinePlaneCubicWeil)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    {r : ℕ} (B : Matrix (Fin r) (Fin 10) ℤ)
    (hB : Module.finrank ℚ (LinearMap.ker (B.map (Int.castRingHom ℚ)).mulVecLin) = 8) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ p : ℕ, p.Prime → ¬ p ∣ N →
      ∀ (K : ℕ → Type) [∀ a, Field (K a)] [∀ a, Fintype (K a)]
        [∀ a, CharP (K a) p]
        (ψ : ∀ a, AddChar (K a) ℂ) (U : ∀ a, Finset (Fin 10 → K a)),
        (∀ a, 1 ≤ a → Fintype.card (K a) = p^a) →
        (∀ a, 1 ≤ a → ψ a ≠ 1) →
        (∀ a, 1 ≤ a → ∀ v ∈ U a, (B.map (Int.castRingHom (K a))).mulVec v = 0) →
        Tendsto (fun a =>
          (∑ v ∈ U a, ‖normalizedFourierSum (ψ a) (map (Int.castRingHom (K a)) F) v‖^2) /
            (p : ℝ)^(a*18)) atTop (𝓝 0) := by
  obtain ⟨e,A,_hA,hplane,N,hN,hlimit⟩ :=
    RationalPlaneMomentDecay.exists_decay_ten smooth spread weil F hF hAn _ hB
  obtain ⟨D,hD,hcontain⟩ := exists_kernel_to_plane B e A hplane.ge
  refine ⟨N*D,one_le_mul_of_one_le_of_one_le hN hD,?_⟩
  intro p hp hpND K _ _ _ ψ U hcard hψ hU
  have hpN : ¬ p ∣ N := fun h => hpND (dvd_mul_of_dvd_left h D)
  have hpD : ¬ p ∣ D := fun h => hpND (dvd_mul_of_dvd_right h N)
  apply hlimit p hp hpN K ψ U hcard hψ
  intro a ha v hv
  exact hcontain p hpD (K a) (hU a ha v hv)

end CubicTenVariables.RationalKernelMomentDecay
