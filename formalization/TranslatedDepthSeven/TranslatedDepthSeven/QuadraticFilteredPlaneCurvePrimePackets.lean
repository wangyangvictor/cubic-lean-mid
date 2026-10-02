import TranslatedDepthSeven.QuadraticFilteredPlaneCurveLocalPacketInternal
import TranslatedDepthSeven.Salberger2023PlaneCurvePrimePackets

/-! # The full smooth residue packets for the half-power plane-curve count -/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial

theorem card_integralPlaneCurve_smoothResiduePacket_le_degree_mul
    {δ k p B : ℕ} (hδ : 2 ≤ δ) (hk : 2 ≤ k) (hB : 1 ≤ B) (hpprime : p.Prime)
    (P : MvPolynomial (Fin 3) ℤ) (hPhom : P.IsHomogeneous δ)
    (hPirred : Irreducible (P.map (Int.castRingHom ℚ)))
    (S : Finset (IntVector 2))
    (hPzero : ∀ z ∈ S, eval (integralAffineChartVector z) P = 0)
    (hbox : ∀ z ∈ S, ∀ i, (integralAffineChartVector z i).natAbs ≤ B)
    (hp : 4 * (B : ℝ) ^ quadraticFilteredCurveExponent k < p)
    (rho : Fin 2 → ZMod p)
    (hrho : rho ∈ planeCurveSmoothResidues (planeCurveFirstChartDehomogenize P) p) :
    (integralResiduePacket S rho).card ≤ δ * k := by
  classical
  by_cases hnonempty : (integralResiduePacket S rho).Nonempty
  · obtain ⟨center, hcenter⟩ := hnonempty
    obtain ⟨v, hv⟩ := ((mem_planeCurveSmoothResidues_iff _ hpprime rho).mp hrho).2
    have heval (g : MvPolynomial (Fin 2) ℤ) :
        eval (integralResidueVector center) (map (Int.castRingHom (ZMod p)) g) =
          (eval center g : ZMod p) := by
      rw [eval_map]
      exact (eval₂_comp (Int.castRingHom (ZMod p)) center g).symm
    rw [← (mem_integralResiduePacket_iff.mp hcenter).2, heval] at hv
    apply card_integralPlaneCurvePacket_le_degree_mul_of_halfPower_threshold_internal
      hδ hk hB hpprime P hPhom hPirred (integralResiduePacket S rho)
      (fun z hz => hPzero z (mem_integralResiduePacket_iff.mp hz).1)
      center ?_ v hv
      (fun z hz => hbox z (mem_integralResiduePacket_iff.mp hz).1) hp
    intro z hz i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    rw [Int.cast_sub]
    exact sub_eq_zero.mpr
      (intVectorCongruent_of_mem_same_integralResiduePacket hz hcenter i)
  · rw [Finset.not_nonempty_iff_eq_empty] at hnonempty
    simp [hnonempty]

end
end TranslatedDepthSeven
