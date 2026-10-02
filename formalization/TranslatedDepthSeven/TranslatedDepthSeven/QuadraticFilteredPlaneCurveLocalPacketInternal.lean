import TranslatedDepthSeven.QuadraticFilteredPlaneCurveMonomialBlockInternal
import TranslatedDepthSeven.QuadraticFilteredPlaneCurveThreshold
import TranslatedDepthSeven.Salberger2023PlaneCurveLocalPacketInternal

/-! # A uniform half-power residue packet bound for nonlinear plane curves

An irreducible curve of degree `δ ≥ 2` has at most `δ*k` integral points
in a smooth residue class once `p > 4 B^((k+1)/(2k+1))`. All inputs to this
statement are the actual equation, box, residue class, and nonzero partial.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 3000000

theorem card_curvePacket_le_degree_mul_columnDegree_of_weighted_block
    {N δ k s p V : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hIprime : I.IsPrime)
    (hIhomogeneous : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hIdegree : HasProjectiveDimensionDegree I 1 δ)
    (F : Fin s → MvPolynomial (Fin (N + 1)) ℤ) (w : Fin s → ℕ)
    (hF : LinearIndependent ℚ (fun i => Ideal.Quotient.mk I ((F i).map (Int.castRingHom ℚ))))
    (hFhom : ∀ i, (F i).IsHomogeneous k)
    (points : Finset (IntVector N))
    (hIzero : ∀ z ∈ points, ∀ f ∈ I,
      eval (rationalIntegralAffineChartPoint z) f = 0)
    (hbound : ∀ z ∈ points, ∀ i,
      (eval (integralAffineChartVector z) (F i)).natAbs ≤ V ^ w i)
    (hpositive : 0 < affineLineJetWeight s)
    (disc : CurveNormalizationResidueDisc
      (Fin (N + 1)) (Fin points.card) p (affineLineJetWeight s) hpositive
      (fun j => integralAffineChartVector (points.equivFin.symm j).1))
    (hlarge : s.factorial * V ^ (∑ i, w i) < p ^ affineLineJetWeight s) :
    points.card ≤ δ * k := by
  classical
  let x : Fin points.card → Fin (N + 1) → ℤ :=
    fun j => integralAffineChartVector (points.equivFin.symm j).1
  have hlarge' : s.factorial * (∏ i, V ^ w i) < p ^ affineLineJetWeight s := by
    rw [Finset.prod_pow_eq_pow_sum]
    exact hlarge
  obtain ⟨G, hGhom, hGnot, hGzeroFin⟩ :=
    exists_curvePacket_auxiliary_of_residue_disc
      I F hF hFhom x hpositive disc (fun i => V ^ w i)
      (fun j i => hbound (points.equivFin.symm j).1 (points.equivFin.symm j).2 i) hlarge'
  have hGzero : ∀ z ∈ points,
      eval (rationalIntegralAffineChartPoint z) G = 0 := by
    intro z hz
    let j : Fin points.card := points.equivFin ⟨z, hz⟩
    have hj := hGzeroFin j
    have hx : x j = integralAffineChartVector z := by
      dsimp only [x, j]
      rw [Equiv.symm_apply_apply]
    simpa only [rationalIntegralAffineChartPoint, hx] using hj
  exact card_integralAffinePoints_on_projectiveCurve_auxiliary_le
    rationalProjectiveCurveAuxiliaryFirstChartBezout_internal
      I G hIprime hIhomogeneous hIdegree hGhom hGnot points hIzero hGzero

theorem card_integralPlaneCurvePacket_le_degree_mul_of_halfPower_threshold_internal
    {δ k p V : ℕ} (hδ : 2 ≤ δ) (hk : 2 ≤ k) (hV : 1 ≤ V) (hpprime : p.Prime)
    (P : MvPolynomial (Fin 3) ℤ) (hPhom : P.IsHomogeneous δ)
    (hPirred : Irreducible (P.map (Int.castRingHom ℚ)))
    (points : Finset (IntVector 2))
    (hPzero : ∀ z ∈ points, eval (integralAffineChartVector z) P = 0)
    (center : Fin 2 → ℤ)
    (hsame : ∀ z ∈ points, ∀ i, (p : ℤ) ∣ z i - center i)
    (v : Fin 2)
    (hpartial : (eval center (pderiv v (planeCurveFirstChartDehomogenize P)) : ZMod p) ≠ 0)
    (hbox : ∀ z ∈ points, ∀ i, (integralAffineChartVector z i).natAbs ≤ V)
    (hp : 4 * (V : ℝ) ^ quadraticFilteredCurveExponent k < p) :
    points.card ≤ δ * k := by
  classical
  by_cases hnonempty : points.Nonempty
  · letI : Nonempty (Fin points.card) := ⟨⟨0, Finset.card_pos.mpr hnonempty⟩⟩
    let Pq := P.map (Int.castRingHom ℚ)
    let I : Ideal (MvPolynomial (Fin 3) ℚ) := Ideal.span ({Pq} : Set _)
    have hIprime : I.IsPrime :=
      (Ideal.span_singleton_prime hPirred.ne_zero).mpr hPirred.prime
    have hIhom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) ℚ) := by
      apply Ideal.homogeneous_span
      intro G hG
      have hGP : G = Pq := Set.mem_singleton_iff.mp hG
      exact ⟨δ, hGP.symm ▸ hPhom.map (Int.castRingHom ℚ)⟩
    have hIdegree : HasProjectiveDimensionDegree I 1 δ :=
      hasProjectiveDimensionDegree_principal_homogeneous Pq
        (hPhom.map _) hPirred.ne_zero (by omega) hIprime
    have hIzero : ∀ z ∈ points, ∀ f ∈ I,
        eval (rationalIntegralAffineChartPoint z) f = 0 := by
      intro z hz f hf
      obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.mp hf
      rw [map_mul]
      suffices eval (rationalIntegralAffineChartPoint z) Pq = 0 by simp [this]
      have he := (MvPolynomial.eval₂_comp (Int.castRingHom ℚ)
        (integralAffineChartVector z) P).symm
      rw [show eval (rationalIntegralAffineChartPoint z) Pq =
          (eval (integralAffineChartVector z) P : ℚ) by
        simpa only [Pq, eval_map, rationalIntegralAffineChartPoint] using he]
      simp [hPzero z hz]
    obtain ⟨F, w, hF, hFhom, hw, hFbound⟩ :=
      exists_quadraticFilteredPlaneCurveMonomialBlock_internal hδ hk P hPhom hPirred
    have hpositive : 0 < affineLineJetWeight (2 * k + 1) := by
      rw [affineLineJetWeight_two_mul_add_one]
      positivity
    let y : Fin points.card → Fin 2 → ℤ := fun j => (points.equivFin.symm j).1
    let disc : CurveNormalizationResidueDisc
        (Fin 3) (Fin points.card) p (affineLineJetWeight (2 * k + 1)) hpositive
        (fun j => integralAffineChartVector (points.equivFin.symm j).1) := by
      simpa only [y, planeCurveFirstChartPoint, integralAffineChartVector] using
        planeCurveFirstChartResidueDiscAt p (affineLineJetWeight (2 * k + 1)) hpprime
          hpositive P y center
          (fun j => hPzero (points.equivFin.symm j).1 (points.equivFin.symm j).2)
          (fun j i => hsame (points.equivFin.symm j).1 (points.equivFin.symm j).2 i) v hpartial
    apply card_curvePacket_le_degree_mul_columnDegree_of_weighted_block
      I hIprime hIhom hIdegree F w hF hFhom points hIzero
      (fun z hz i => hFbound V (integralAffineChartVector z) rfl (hbox z hz 1) (hbox z hz 2) i)
      hpositive disc
    rw [hw]
    exact quadraticFiltered_curve_determinant_size_of_prime_threshold (by omega) hV hp
  · simp only [Finset.not_nonempty_iff_eq_empty] at hnonempty
    simp [hnonempty]

end
end TranslatedDepthSeven
