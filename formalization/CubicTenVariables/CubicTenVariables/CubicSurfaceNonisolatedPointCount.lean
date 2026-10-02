import CubicTenVariables.CubicSurfaceSingularLineUnique
import CubicTenVariables.CubicSingularPlanePoint
import CubicTenVariables.FiniteFieldCubicSingularPointCount
import CubicTenVariables.SmoothCubicProjectivePointCount

/-! The nonisolated cubic-surface branch: the actual geometric singular
line descends over a perfect field, and projection from its rational point
gives a uniform finite-field bound. No rationality/classification or point-
count literature premise is used. The isolated conjugate-point cases are
not asserted here. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CubicSurfaceNonisolatedPointCount
open MvPolynomial HessianTheorem11 Literature Module
open CubicSurfaceProjectiveSingular ProjectiveFourierIdentity
variable {K : Type*} [Field K]

/-- Nonfiniteness concerns the actual projective singular set over the
algebraic closure, not the automatically finite set of base-field points. -/
theorem exists_singular_point [PerfectField K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hI : GeometricallyIntegralForm F)
    (hinf : ¬ (singularPoints (map (algebraMap K (AlgebraicClosure K)) F)).Finite) :
    ∃ z : Fin 4 → K, z ≠ 0 ∧ eval z F = 0 ∧ gradient F z = 0 := by
  let G := map (algebraMap K (AlgebraicClosure K)) F
  have hG : G.IsHomogeneous 3 := hF.map _
  have hGne : G ≠ 0 := by
    intro hz
    apply hI.1
    apply map_injective (algebraMap K (AlgebraicClosure K))
      (algebraMap K (AlgebraicClosure K)).injective
    simpa only [map_zero] using hz
  have hirr : Irreducible G :=
    ((Ideal.span_singleton_prime hGne).mp ((Ideal.Quotient.isDomain_iff_prime _).mp hI.2)).irreducible
  obtain ⟨L,⟨hLd,hL⟩,_⟩ :=
    CubicSurfaceSingularLineUnique.exists_unique_line_of_not_finite G hG hirr hinf
  apply CubicSingularPlanePoint.exists_point_of_linear_singularCone F L (by omega)
  ext x
  change (x ∈ L) ↔ eval x G = 0 ∧ ∀ i, eval x (pderiv i G) = 0
  simpa only [HessianTheorem11.gradient, funext_iff, Pi.zero_apply] using hL x

/-- One absolute constant precedes every finite field and every integral
nonconical cubic surface with nonfinite geometric projective singular set. -/
theorem exists_affine_bound :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (K : Type) [Field K] [Fintype K]
      (F : MvPolynomial (Fin 4) K), F.IsHomogeneous 3 →
      (2 : K) ≠ 0 → (3 : K) ≠ 0 → GeometricallyIntegralForm F →
      GeometricallyNonconicalCubic F →
      ¬ (singularPoints (map (algebraMap K (AlgebraicClosure K)) F)).Finite →
      |(affineZeroCount F : ℝ) - (Fintype.card K : ℝ)^3| ≤
        B * ((Fintype.card K : ℝ)-1) * (Fintype.card K : ℝ) := by
  obtain ⟨B,hB,h⟩ := FiniteFieldCubicSingularPointCount.exists_bound 3 (by decide)
  refine ⟨B,hB,?_⟩
  intro K _ _ F hF h2 h3 hI hNC hinf
  simpa only [Nat.reduceSub, pow_one] using
    h K F hF h2 h3 hI hNC (exists_singular_point F hF hI hinf)

/-- The same branch in actual projective-point notation: error `O(q)`
around `q²+q+1`, uniformly over all finite fields outside characteristics 2,3. -/
theorem exists_projective_bound :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (K : Type) [Field K] [Fintype K]
      (F : MvPolynomial (Fin 4) K), F.IsHomogeneous 3 →
      (2 : K) ≠ 0 → (3 : K) ≠ 0 → GeometricallyIntegralForm F →
      GeometricallyNonconicalCubic F →
      ¬ (singularPoints (map (algebraMap K (AlgebraicClosure K)) F)).Finite →
      |(Nat.card (zeroPoints F) : ℝ) -
        ((Fintype.card K : ℝ)^2 + (Fintype.card K : ℝ) + 1)| ≤
        B * (Fintype.card K : ℝ) := by
  obtain ⟨B,hB,h⟩ := exists_affine_bound
  refine ⟨B,hB,?_⟩
  intro K _ _ F hF h2 h3 hI hNC hinf
  have hb := h K F hF h2 h3 hI hNC hinf
  let q : ℝ := Fintype.card K
  have hq : 0 < q-1 := by
    have hh : (1 : ℝ) < Fintype.card K := by exact_mod_cast (Fintype.one_lt_card (α := K))
    dsimp only [q]
    linarith
  have hc := SmoothCubicProjectivePointCount.real_affine_cone_card F hF (by decide)
  have he : (affineZeroCount F : ℝ) - q^3 =
      (q-1) * ((Nat.card (zeroPoints F) : ℝ) - (q^2+q+1)) := by
    change (affineZeroCount F : ℝ) = 1 + (q-1) * (Nat.card (zeroPoints F) : ℝ) at hc
    rw [hc]
    ring
  change |(affineZeroCount F : ℝ) - q^3| ≤ B*(q-1)*q at hb
  rw [he,abs_mul,abs_of_pos hq] at hb
  apply le_of_mul_le_mul_left (a := q-1) ?_ hq
  calc
    (q-1) * |(Nat.card (zeroPoints F) : ℝ) - (q^2+q+1)| ≤ B*(q-1)*q := hb
    _ = (q-1) * (B*q) := by ring

end CubicTenVariables.CubicSurfaceNonisolatedPointCount
