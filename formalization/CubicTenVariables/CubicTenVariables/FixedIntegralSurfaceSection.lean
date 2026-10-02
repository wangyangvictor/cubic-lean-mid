import CubicTenVariables.HypersurfaceIntegralFrameCertificate
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# A fixed integral surface section from the Bertini certificate

A nonzero polynomial over `Z` cannot vanish at every integral parameter
tuple.  Applying this elementary fact to the frame certificate produces one
fixed integer matrix.  The value of the certificate at that matrix is the
single explicit integer whose nonvanishing controls all coefficient fields.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace CubicTenVariables.FixedIntegralSurfaceSection

open MvPolynomial Literature HessianTheorem11
open HessianTheorem11.PolynomialRestriction
open ReducedHyperplaneIntegrality

private theorem exists_integer_eval_ne_zero
    {σ : Type*} (P : MvPolynomial σ ℤ) (hP : P ≠ 0) :
    ∃ x : σ → ℤ, eval x P ≠ 0 := by
  by_contra h
  push_neg at h
  apply hP
  apply MvPolynomial.funext
  intro x
  simpa only [map_zero] using h x

/-- A fixed integral projective hyperplane section, with one actual integer
certificate controlling injectivity, degree, and geometric integrality over
every field in which that integer remains nonzero. -/
theorem exists_fixed_integral_surface_section
    (integralityOpen : HomogeneousHypersurfaceIntegralityOpen)
    {d : ℕ} (hd : 2 ≤ d)
    (F : MvPolynomial (Fin 4) ℤ) (hF0 : F ≠ 0)
    (hF : F.IsHomogeneous d)
    (hgeom : IsDomain (MvPolynomial (Fin 4) GeometricField ⧸
      Ideal.span {map (Int.castRingHom GeometricField) F})) :
    ∃ (A : Matrix (Fin 4) (Fin 3) ℤ) (N : ℤ), A 0 0 ≠ 0 ∧ N ≠ 0 ∧
      ∀ (K : Type) [Field K], (N : K) ≠ 0 →
        (A 0 0 : K) ≠ 0 ∧
        Function.Injective (A.map (Int.castRingHom K)).mulVec ∧
        (map (Int.castRingHom K) (restrict A F)).IsHomogeneous d ∧
        (map (Int.castRingHom K) (restrict A F)).totalDegree = d ∧
        IsDomain (MvPolynomial (Fin 3) (AlgebraicClosure K) ⧸
          Ideal.span {map (algebraMap K (AlgebraicClosure K))
            (map (Int.castRingHom K) (restrict A F))}) := by
  obtain ⟨Δ, hΔ, hgood⟩ :=
    HypersurfaceIntegralFrameCertificate.exists_nonzero_surface_hyperplane_certificate
      integralityOpen hd F hF0 hF hgeom
  let P : MvPolynomial (Parameters 4 3) ℤ := Δ * X (0, 0)
  have hP : P ≠ 0 := mul_ne_zero hΔ (X_ne_zero (0, 0))
  obtain ⟨a, ha⟩ := exists_integer_eval_ne_zero P hP
  let A : Matrix (Fin 4) (Fin 3) ℤ := fun i j => a (i, j)
  let N : ℤ := eval a P
  have hprodInt : eval a Δ * A 0 0 ≠ 0 := by
    simpa only [P, map_mul, eval_X, A] using ha
  refine ⟨A, N, (mul_ne_zero_iff.mp hprodInt).2, ha, ?_⟩
  intro K _ hN
  have hprod : eval₂ (Int.castRingHom K)
      (fun ij => (A ij.1 ij.2 : K)) P ≠ 0 := by
    have he : eval₂ (Int.castRingHom K) (fun ij => (A ij.1 ij.2 : K)) P =
        (N : K) := by
      change eval₂ (Int.castRingHom K) (fun ij => (a ij : K)) P =
        ((eval a P : ℤ) : K)
      simpa only [eval₂_eq_eval_map] using
        (map_eval (Int.castRingHom K) a P).symm
    exact he ▸ hN
  have hsplit : eval₂ (Int.castRingHom K)
        (fun ij => (A ij.1 ij.2 : K)) Δ ≠ 0 ∧ (A 0 0 : K) ≠ 0 := by
    apply mul_ne_zero_iff.mp
    simpa only [P, eval₂_mul, eval₂_X] using hprod
  have hh := hgood K (A.map (Int.castRingHom K)) (by
    simpa only [Matrix.map_apply] using hsplit.1)
  have hrestrict : restrict (A.map (Int.castRingHom K))
      (map (Int.castRingHom K) F) =
      map (Int.castRingHom K) (restrict A F) := by
    exact (map_restrict (Int.castRingHom K) A F).symm
  rw [hrestrict] at hh
  exact ⟨hsplit.2, hh⟩

end CubicTenVariables.FixedIntegralSurfaceSection
