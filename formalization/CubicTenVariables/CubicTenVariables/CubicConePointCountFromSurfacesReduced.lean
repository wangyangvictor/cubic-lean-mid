import CubicTenVariables.CubicGoodHyperplanePointCountReduced
import CubicTenVariables.CubicConePointCountFromSurfaces

/-! Nine-variable cubic counts obtained from the reduced cubic-surface
interface and the existing exact cone decomposition. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace CubicTenVariables.CubicConePointCountFromSurfacesReduced

open MvPolynomial Literature HessianTheorem11
open HessianTheorem11.PolynomialRestriction

theorem exists_nine_variable_bound
    (isolated : CubicSurfacePointCountReduced.IsolatedConjugateCubicSurfacePointCount)
    (weil : SmoothCubicWeil) :
    ∃ N : ℕ, 0 < N ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ (K : Type) [Field K] [Fintype K], (N : K) ≠ 0 →
        ∀ F : MvPolynomial (Fin 9) K, ∀ hF : F.IsHomogeneous 3,
          GeometricallyIntegralForm F →
          Module.finrank K (ReducedCubicVertex.affineVertex F hF) ≤ 5 →
          |(affineZeroCount F : ℝ) - (Fintype.card K : ℝ)^8| ≤
            C * ((Fintype.card K : ℝ)-1) * (Fintype.card K : ℝ)^6 := by
  obtain ⟨A,hA,C,hC,hbase⟩ :=
    CubicGoodHyperplanePointCountReduced.exists_uniform_base_bound_through_nine
      isolated weil
  refine ⟨6*A, Nat.mul_pos (by decide) hA, C, hC, ?_⟩
  intro K _ _ hNA F hF hI hv
  have hprod : (6 : K) * (A : K) ≠ 0 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hNA
  have h6 : (6 : K) ≠ 0 := (mul_ne_zero_iff.mp hprod).1
  have hAK : (A : K) ≠ 0 := (mul_ne_zero_iff.mp hprod).2
  have h23 : (2 : K) * (3 : K) ≠ 0 := by
    rw [show (2 : K) * (3 : K) = 6 by norm_num]
    exact h6
  have h2 : (2 : K) ≠ 0 := (mul_ne_zero_iff.mp h23).1
  have h3 : (3 : K) ≠ 0 := (mul_ne_zero_iff.mp h23).2
  obtain ⟨E,Q,hQ,_hE,_hQeq,hfactor,heval,hvertex⟩ :=
    ReducedConeCoordinates.exists_cone_coordinates F hF h2 h3
  have hQI : GeometricallyIntegralForm Q := by
    constructor
    · intro hzero
      apply hI.1
      rw [hfactor,hzero]
      simp [restrict]
    · exact ReducedConeCoordinates.quotient_domain_baseChange_of_factor
        F Q (ReducedConeCoordinates.projection E)
        (ReducedConeCoordinates.sectionMatrix E)
        (ReducedConeCoordinates.projection_section E) hfactor hI.2
  have hQN : GeometricallyNonconicalCubic Q :=
    ReducedConeCoordinates.translation_baseChange_eq_zero Q hQ h2 hvertex
  have hb := hbase (9 - Module.finrank K (ReducedCubicVertex.affineVertex F hF))
    (by omega) (by omega) K hAK Q hQ hQI hQN
  have hcount : (affineZeroCount F : ℝ) =
      (Fintype.card K : ℝ) ^ Module.finrank K
        (ReducedCubicVertex.affineVertex F hF) * (affineZeroCount Q : ℝ) := by
    have hc := AffineConePointCount.zero_card F Q E heval
    have hc' : affineZeroCount F =
        Fintype.card K ^ Module.finrank K (ReducedCubicVertex.affineVertex F hF) *
          affineZeroCount Q := by
      simpa only [affineZeroCount, Nat.card_eq_fintype_card] using hc
    exact_mod_cast hc'
  exact CubicConePointCountFromSurfaces.cone_error_le_nat
    (Fintype.card K) C _ _
    (Module.finrank K (ReducedCubicVertex.affineVertex F hF))
    (9 - Module.finrank K (ReducedCubicVertex.affineVertex F hF)) 9
    (by positivity) (by omega) (by omega) hcount hb

end CubicTenVariables.CubicConePointCountFromSurfacesReduced
