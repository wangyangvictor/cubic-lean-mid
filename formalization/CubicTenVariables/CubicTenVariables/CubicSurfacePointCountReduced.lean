import CubicTenVariables.CubicSurfaceNonisolatedPointCount
import CubicTenVariables.CubicSurfaceIsolatedSingularBound
import CubicTenVariables.SmoothCubicProjectivePointCount

/-!
The cubic-surface point-count input after separating the cases already proved
in this development.

The only residual input concerns a geometrically integral nonconical cubic
surface whose actual geometric projective singular set is finite and nonempty,
has at most four points, and contains no point defined over the ground field.
Smooth surfaces are handled by `SmoothCubicWeil`; a nonfinite singular locus is
handled by `CubicSurfaceNonisolatedPointCount`; and a ground-field singular
point is handled by `FiniteFieldCubicSingularPointCount`.

No extension-field trace array or potential-goodness premise occurs here.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace CubicTenVariables.CubicSurfacePointCountReduced

open MvPolynomial HessianTheorem11 Literature ProjectiveFourierIdentity
open CubicSurfaceProjectiveSingular

/-- The literal point-count remainder after the elementary singular-surface
case split. It applies only to a finite nonempty geometric singular set with
no ground-field point. The set may consist of more than one Galois orbit.
The cardinality bound records the proved geometric restriction on this
branch. -/
def IsolatedConjugateCubicSurfacePointCount : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ (K : Type) [Field K] [Fintype K]
    (F : MvPolynomial (Fin 4) K), F.IsHomogeneous 3 →
    (2 : K) ≠ 0 → (3 : K) ≠ 0 → GeometricallyIntegralForm F →
    GeometricallyNonconicalCubic F →
    (singularPoints (map (algebraMap K (AlgebraicClosure K)) F)).Finite →
    (∃ x : Fin 4 → AlgebraicClosure K,
      x ≠ 0 ∧ x ∈ geometricSingularCone F) →
    (¬ ∃ z : Fin 4 → K,
      z ≠ 0 ∧ eval z F = 0 ∧ gradient F z = 0) →
    (singularPoints (map (algebraMap K (AlgebraicClosure K)) F)).ncard ≤ 4 →
    |(affineZeroCount F : ℝ) - (Fintype.card K : ℝ)^3| ≤
      C * ((Fintype.card K : ℝ)-1) * (Fintype.card K : ℝ)

variable {K : Type} [Field K] [Fintype K]

/-- Exact conversion from a projective `O(q)` bound to its affine-cone
`O((q-1)q)` form. -/
theorem affine_bound_of_projective_bound
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (C : ℝ)
    (hp : |(Nat.card (zeroPoints F) : ℝ) -
      ((Fintype.card K : ℝ)^2 + (Fintype.card K : ℝ) + 1)| ≤
        C * (Fintype.card K : ℝ)) :
    |(affineZeroCount F : ℝ) - (Fintype.card K : ℝ)^3| ≤
      C * ((Fintype.card K : ℝ)-1) * (Fintype.card K : ℝ) := by
  let q : ℝ := Fintype.card K
  have hq : 0 ≤ q-1 := by
    have hh : (1 : ℝ) ≤ Fintype.card K := by
      exact_mod_cast Nat.succ_le_of_lt (Fintype.card_pos (α := K))
    dsimp only [q]
    linarith
  have hc := SmoothCubicProjectivePointCount.real_affine_cone_card F hF (by decide)
  have he : (affineZeroCount F : ℝ) - q^3 =
      (q-1) * ((Nat.card (zeroPoints F) : ℝ) - (q^2+q+1)) := by
    change (affineZeroCount F : ℝ) =
      1 + (q-1)*(Nat.card (zeroPoints F) : ℝ) at hc
    rw [hc]
    ring
  change |(affineZeroCount F : ℝ) - q^3| ≤ C*(q-1)*q
  rw [he, abs_mul, abs_of_nonneg hq]
  calc
    (q-1)*|(Nat.card (zeroPoints F) : ℝ) - (q^2+q+1)| ≤ (q-1)*(C*q) :=
      mul_le_mul_of_nonneg_left hp hq
    _ = C*(q-1)*q := by ring

/-- Smooth cubic surfaces satisfy the required affine estimate with constant
`10`, directly from the displayed smooth cubic Weil input. -/
theorem smooth_affine_bound (weil : SmoothCubicWeil)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hI : GeometricallyIntegralForm F) (hsmooth : ProjectivelySmooth F) :
    |(affineZeroCount F : ℝ) - (Fintype.card K : ℝ)^3| ≤
      10 * ((Fintype.card K : ℝ)-1) * (Fintype.card K : ℝ) := by
  have hsq := SmoothCubicProjectivePointCount.projective_error_sq
    weil 2 (by decide) (by decide) F hI.1 hF hsmooth
  have hm : CubicSlicingNumerics.projectiveMainTerm (Fintype.card K) 2 =
      (Fintype.card K : ℝ)^2 + (Fintype.card K : ℝ) + 1 := by
    simp [CubicSlicingNumerics.projectiveMainTerm, Finset.sum_range_succ] <;> ring
  rw [hm] at hsq
  have hp : |(Nat.card (zeroPoints F) : ℝ) -
      ((Fintype.card K : ℝ)^2 + (Fintype.card K : ℝ) + 1)| ≤
        10 * (Fintype.card K : ℝ) := by
    apply abs_le_of_sq_le_sq _ (by positivity)
    nlinarith [hsq]
  exact affine_bound_of_projective_bound F hF 10 hp

/-- A failed projective-smoothness test supplies an actual nonzero geometric
singular representative. -/
theorem exists_geometric_singular_of_not_projectivelySmooth
    (F : MvPolynomial (Fin 4) K) (hsmooth : ¬ ProjectivelySmooth F) :
    ∃ x : Fin 4 → AlgebraicClosure K,
      x ≠ 0 ∧ x ∈ geometricSingularCone F := by
  by_contra! h
  apply hsmooth
  intro x hx
  by_contra hne
  exact h x hne hx

/-- An integral cubic surface with finite geometric singular set has at most
four actual projective singular points. -/
theorem geometric_singularPoints_ncard_le_four
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hI : GeometricallyIntegralForm F)
    (hfin : (singularPoints
      (map (algebraMap K (AlgebraicClosure K)) F)).Finite) :
    (singularPoints (map (algebraMap K (AlgebraicClosure K)) F)).ncard ≤ 4 := by
  let G := map (algebraMap K (AlgebraicClosure K)) F
  have hGne : G ≠ 0 := by
    intro hz
    apply hI.1
    apply map_injective (algebraMap K (AlgebraicClosure K))
      (algebraMap K (AlgebraicClosure K)).injective
    simpa only [map_zero] using hz
  have hirr : Irreducible G :=
    ((Ideal.span_singleton_prime hGne).mp
      ((Ideal.Quotient.isDomain_iff_prime _).mp hI.2)).irreducible
  exact CubicSurfaceIsolatedSingularBound.ncard_singularPoints_le_four
    G (hF.map _) hirr hfin

private theorem coefficient_mono (A B q : ℝ) (hAB : A ≤ B) (hq : 1 ≤ q) :
    A * (q-1) * q ≤ B * (q-1) * q := by
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hAB (sub_nonneg.mpr hq)) (by positivity)

/-- The complete cubic-surface affine estimate after replacing the broad
finite-extension amplification principle by the isolated-conjugate remainder.
The three singular branches are: rational singular point, nonfinite geometric
singular locus, and the residual finite singular set without a ground-field
point. -/
theorem exists_uniform_affine_bound
    (isolated : IsolatedConjugateCubicSurfacePointCount)
    (weil : SmoothCubicWeil) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (K : Type) [Field K] [Fintype K]
      (F : MvPolynomial (Fin 4) K), F.IsHomogeneous 3 →
      (2 : K) ≠ 0 → (3 : K) ≠ 0 → GeometricallyIntegralForm F →
      GeometricallyNonconicalCubic F →
      |(affineZeroCount F : ℝ) - (Fintype.card K : ℝ)^3| ≤
        C * ((Fintype.card K : ℝ)-1) * (Fintype.card K : ℝ) := by
  obtain ⟨Cr, hCr, hr⟩ :=
    FiniteFieldCubicSingularPointCount.exists_bound 3 (by decide)
  obtain ⟨Cn, hCn, hn⟩ :=
    CubicSurfaceNonisolatedPointCount.exists_affine_bound
  obtain ⟨Ci, hCi, hi⟩ := isolated
  let C := max 10 (max Cr (max Cn Ci))
  refine ⟨C, (by dsimp only [C]; norm_num), ?_⟩
  intro K _ _ F hF h2 h3 hI hNC
  have hq : (1 : ℝ) ≤ Fintype.card K := by
    exact_mod_cast Nat.succ_le_of_lt (Fintype.card_pos (α := K))
  by_cases hsmooth : ProjectivelySmooth F
  · exact (smooth_affine_bound weil F hF hI hsmooth).trans
      (coefficient_mono 10 C _ (by
        dsimp only [C]
        exact le_max_left _ _) hq)
  · have hs := exists_geometric_singular_of_not_projectivelySmooth F hsmooth
    let G := map (algebraMap K (AlgebraicClosure K)) F
    by_cases hfin : (singularPoints G).Finite
    · by_cases hrat : ∃ z : Fin 4 → K,
          z ≠ 0 ∧ eval z F = 0 ∧ gradient F z = 0
      · have hb := hr K F hF h2 h3 hI hNC hrat
        have hb' : |(affineZeroCount F : ℝ) - (Fintype.card K : ℝ)^3| ≤
            Cr * ((Fintype.card K : ℝ)-1) * (Fintype.card K : ℝ) := by
          simpa only [Nat.reduceSub, pow_one] using hb
        exact hb'.trans (coefficient_mono Cr C _ (by
            dsimp only [C]
            exact le_max_of_le_right (le_max_left _ _)) hq)
      · have hcard : (singularPoints G).ncard ≤ 4 :=
          geometric_singularPoints_ncard_le_four F hF hI hfin
        have hb := hi K F hF h2 h3 hI hNC hfin hs hrat hcard
        exact hb.trans (coefficient_mono Ci C _ (by
          dsimp only [C]
          exact le_max_of_le_right (le_max_of_le_right (le_max_right _ _))) hq)
    · have hb := hn K F hF h2 h3 hI hNC hfin
      exact hb.trans (coefficient_mono Cn C _ (by
        dsimp only [C]
        exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))) hq)

end CubicTenVariables.CubicSurfacePointCountReduced
