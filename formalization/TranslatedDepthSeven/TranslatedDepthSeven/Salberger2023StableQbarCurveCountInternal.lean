import TranslatedDepthSeven.Salberger2023ProjectedCurveCountInternal
import TranslatedDepthSeven.StableQbarCurveRationalData

/-!
# Internal high-degree counting for stable geometric curves

The projection and the rational model are constructed here.  The displayed
hypotheses concern only the actual geometric curve, its finite set of
integral affine points, and the logarithmic degree and coordinate bounds.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published Filter
open scoped Topology
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000

theorem exists_eventually_stableQbarCurve_count_internal
    (N : ℕ) (hN : 1 < N) (Cd ε : ℝ) (hCd : 0 ≤ Cd) (hε : 0 < ε) :
    ∃ cutoff : ℕ, ∀ᶠ V : ℝ in atTop, ∀ δ M : ℕ,
      cutoff < δ → (δ : ℝ) ≤ Cd * (1 + Real.log V) → (M : ℝ) ≤ V →
      ∀ Q : Ideal (MvPolynomial (Fin (N + 1)) Qbar),
        Q.IsPrime →
        Q.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) Qbar) →
        HasProjectiveDimensionDegree Q 1 δ →
        (∀ g : Qbar ≃ₐ[ℚ] Qbar, conjugateIdeal g Q = Q) →
      ∀ S : Finset (IntVector N),
        (∀ z ∈ S, ∀ f ∈ Q,
          eval (fun i ↦ (integralAffineChartVector z i : Qbar)) f = 0) →
        (∀ z ∈ S, ∀ i, (z i).natAbs ≤ M) →
        (S.card : ℝ) ≤ V ^ (ε / 2) := by
  classical
  obtain ⟨cutoff, hcount⟩ :=
    exists_eventually_projectedCurve_count_internal N Cd ε hCd hε
  refine ⟨cutoff, ?_⟩
  filter_upwards [hcount, eventually_ge_atTop (1 : ℝ)] with V hcountV hV
  intro δ M hhigh hδ hM Q hQprime hQhom hQdegree hstable S hzero hbox
  by_cases hS : S.Nonempty
  · obtain ⟨I, hIprime, hIhom, hIdegree, hIX, _hIQ, hIzero⟩ :=
      exists_rationalCurveData_of_stableQbar
        Q hQprime hQhom hQdegree hstable S hS hzero
    obtain ⟨A, hA, G, hprojection, _hImageDegree⟩ :=
      exists_mem_boundedIntegralAffineProjectionMatrices N 1 δ hN
        I hIprime hIhom hIX δ hIdegree le_rfl
    exact hcountV δ M hhigh hδ hM I hIprime hIhom hIdegree
      A G hA hprojection S hIzero hbox
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hS
    simp only [hempty, Finset.card_empty, Nat.cast_zero]
    exact Real.rpow_nonneg (by linarith) _

end

end TranslatedDepthSeven
