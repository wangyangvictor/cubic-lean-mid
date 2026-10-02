import TranslatedDepthSeven.PlaneCurveDerivativeCertificate
import TranslatedDepthSeven.Salberger2023PlaneCurveLocalPacketInternal

/-!
# The actual prime packets of an integral plane curve

This supplies all three local hypotheses of the global prime-cover count:
the explicit derivative certificate places a point in a smooth residue,
there are at most degree times prime such residues, and each full packet
has at most degree squared points.  No residue-disc or local-count premise
is left to the caller.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

set_option maxHeartbeats 2000000

/-- Every full residue packet over a smooth point satisfies the internal
local determinant bound, including an empty packet. -/
theorem card_integralPlaneCurve_smoothResiduePacket_le
    {δ p B : ℕ} (hδ : 1 ≤ δ) (hB : 1 ≤ B) (hpprime : p.Prime)
    (P : MvPolynomial (Fin 3) ℤ) (hPhom : P.IsHomogeneous δ)
    (hPirred : Irreducible (P.map (Int.castRingHom ℚ)))
    (S : Finset (IntVector 2))
    (hPzero : ∀ z ∈ S, eval (integralAffineChartVector z) P = 0)
    (hbox : ∀ z ∈ S, ∀ i, (integralAffineChartVector z i).natAbs ≤ B)
    (hp : 4 * (B : ℝ) ^ (8 / ((δ : ℝ) + 3)) < p)
    (rho : Fin 2 → ZMod p)
    (hrho : rho ∈ planeCurveSmoothResidues (planeCurveFirstChartDehomogenize P) p) :
    (integralResiduePacket S rho).card ≤ δ ^ 2 := by
  classical
  by_cases hnonempty : (integralResiduePacket S rho).Nonempty
  · obtain ⟨center, hcenter⟩ := hnonempty
    obtain ⟨v, hv⟩ :=
      ((mem_planeCurveSmoothResidues_iff _ hpprime rho).mp hrho).2
    have heval (g : MvPolynomial (Fin 2) ℤ) :
        eval (integralResidueVector center) (map (Int.castRingHom (ZMod p)) g) =
          (eval center g : ZMod p) := by
      rw [eval_map]
      exact (eval₂_comp (Int.castRingHom (ZMod p)) center g).symm
    rw [← (mem_integralResiduePacket_iff.mp hcenter).2, heval] at hv
    apply card_integralPlaneCurvePacket_le_degree_sq_of_prime_threshold_internal
      hδ hB hpprime P hPhom hPirred (integralResiduePacket S rho)
      (fun z hz ↦ hPzero z (mem_integralResiduePacket_iff.mp hz).1)
      center ?_ v hv
      (fun z hz ↦ hbox z (mem_integralResiduePacket_iff.mp hz).1)
      hp
    intro z hz i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    rw [Int.cast_sub]
    exact sub_eq_zero.mpr
      (intVectorCongruent_of_mem_same_integralResiduePacket hz hcenter i)
  · rw [Finset.not_nonempty_iff_eq_empty] at hnonempty
    simp [hnonempty]

/-- The exact local conjunction consumed by the uniform prime-cover count,
for the literal derivative certificate and the literal smooth-residue set. -/
theorem integralPlaneCurve_primePacket_data
    {δ p B : ℕ} (hδ : 1 ≤ δ) (hB : 1 ≤ B) (hpprime : p.Prime)
    (P : MvPolynomial (Fin 3) ℤ) (hPhom : P.IsHomogeneous δ)
    (hPirred : Irreducible (P.map (Int.castRingHom ℚ)))
    (S : Finset (IntVector 2))
    (hPzero : ∀ z ∈ S, eval (integralAffineChartVector z) P = 0)
    (hbox : ∀ z ∈ S, ∀ i, (integralAffineChartVector z i).natAbs ≤ B)
    (hp : 4 * (B : ℝ) ^ (8 / ((δ : ℝ) + 3)) < p) :
    let f := planeCurveFirstChartDehomogenize P
    (∀ z ∈ S, ¬ (p : ℤ) ∣ planeCurveDerivativeCertificate f z →
      integralResidueVector z ∈ planeCurveSmoothResidues f p) ∧
    (planeCurveSmoothResidues f p).card ≤ δ * p ∧
    (∀ rho ∈ planeCurveSmoothResidues f p,
      (integralResiduePacket S rho).card ≤ δ ^ 2) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro z hz hD
    apply residue_mem_planeCurveSmoothResidues_of_certificate _ z ?_ hpprime hD
    exact (planeCurveFirstChart_eval z P).trans (hPzero z hz)
  · exact (card_planeCurveSmoothResidues_le _ hpprime).trans
      (Nat.mul_le_mul_right p
        ((totalDegree_planeCurveFirstChartDehomogenize_le P).trans
          hPhom.totalDegree_le))
  · exact card_integralPlaneCurve_smoothResiduePacket_le hδ hB hpprime
      P hPhom hPirred S hPzero hbox hp

end

end TranslatedDepthSeven
