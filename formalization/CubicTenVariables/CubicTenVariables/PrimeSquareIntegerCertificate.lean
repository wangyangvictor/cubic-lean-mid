import CubicTenVariables.PrimeSquareMicrolocalBound
import CubicTenVariables.MicrolocalIntegerCertificate

/-! Positive polynomial-height exceptional integers for the actual
prime-square sum off the next microlocal depth locus. The equations come
from the same incidence's exact depth models, and the same integer keeps
the reduced frequency nonzero. The proved prime-field family count interface
remains explicit; no prime-square estimate is assumed as application data. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PrimeSquareIntegerCertificate
open MvPolynomial HessianTheorem11
open ProjectiveMicrolocalModels

private theorem cast_eval (P : MvPolynomial (Fin 10) ℤ) (v : Fin 10 → ℤ) :
    (eval v P : GeometricField) =
      eval₂ (Int.castRingHom GeometricField) (fun a => (v a : GeometricField)) P := by
  simpa only [Function.comp_def,Int.coe_castRingHom,eval₂_eq_eval_map] using
    map_eval (Int.castRingHom GeometricField) v P

/-- Fixed equations and constants precede every frequency and prime.
The positive certificate is literally N times an equation value and a
nonzero coordinate. The same C bounds both its height and the original sum.
Level zero is included. -/
theorem exists_off_depth_certificate (lit : FixedFamilyPrimeFieldPointCount.Uniform)
    {t : ℕ} {F : MvPolynomial (Fin 10) ℤ} (hF : F.IsHomogeneous 3)
    {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10} {N B : ℕ}
    (h : TenMicrolocalIncidence.Conclusion F f N B) (hN : 1 ≤ N)
    (j : ℕ) (hj : j ≤ 8) :
    ∃ (u : ℕ) (G : Fin u → MvPolynomial (Fin 10) ℤ) (C : ℝ) (D : ℕ),
      1 ≤ C ∧
      (∀ x : GeometricPoint 10, (∀ i, eval₂ (Int.castRingHom GeometricField) x (G i) = 0) ↔
        x ∈ ProjectiveMicrolocalDepth.depth f (j+1)) ∧
      ∀ v : Fin 10 → ℤ, v ≠ 0 →
        (fun a => (v a : GeometricField)) ∉ ProjectiveMicrolocalDepth.depth f (j+1) →
        ∃ Δ : ℕ, 1 ≤ Δ ∧
          (∃ (i : Fin u) (k : Fin 10), eval v (G i) ≠ 0 ∧ v k ≠ 0 ∧
            Δ = N * (eval v (G i) * v k).natAbs) ∧
          (∀ H : ℝ, 1 ≤ H → (∀ a, |(v a : ℝ)| ≤ H) → (Δ : ℝ) ≤ C * H^D) ∧
          ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ Δ →
            ‖completeCubicSum F (p^2) v‖ ≤ C * (p : ℝ)^(11+j) := by
  obtain ⟨u,G,d,hd,hI,hgeo,hgood⟩ := h.depth_models ⟨j,by omega⟩
  obtain ⟨Cb,hCb,hbound⟩ := PrimeSquareMicrolocalBound.exists_off_depth_bound lit hF h
  obtain ⟨Ch,D,hCh,hcert⟩ := MicrolocalIntegerCertificate.exists_bounded_certificate N hN G
  let C : ℝ := max Ch Cb
  refine ⟨u,G,C,D,hCh.trans (le_max_left _ _),hgeo,?_⟩
  intro v hv hoff
  have hG : ∃ i, eval v (G i) ≠ 0 := by
    by_contra! hz
    apply hoff
    apply (hgeo _).mp
    intro i
    rw [← cast_eval,hz i,Int.cast_zero]
  obtain ⟨Δ,hΔ,heq,hheight,hreduce⟩ := hcert v hv hG
  refine ⟨Δ,hΔ,heq,?_,?_⟩
  · intro H hH hvH
    exact (hheight H hH hvH).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (by linarith) D))
  · intro p _ hp
    obtain ⟨hpN,hvp,hGp⟩ := hreduce p hp (ZMod p)
    have hdim : ¬ ((j+1 : ℕ) : Dimension) ≤
        IntegralGeometricFiberDepth.geometricFiberDimension f (ZMod p)
          (fun a => (v a : ZMod p)) := by
      intro hd
      obtain ⟨i,hi⟩ := hGp
      exact hi (((hgood p Fact.out hpN (ZMod p)).1 _).mpr hd i)
    exact (hbound p hpN v hvp j hdim).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (Nat.cast_nonneg _) _))

end CubicTenVariables.PrimeSquareIntegerCertificate
