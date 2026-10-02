import TranslatedDepthSeven.PrimitiveProjectiveCurvePacketBoundInternal
import TranslatedDepthSeven.PlaneCurveDerivativeCertificate
import TranslatedDepthSeven.HypersurfaceProperDerivative

/-! Actual smooth projective residue packets in one chart. -/
namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
set_option maxHeartbeats 3000000

/-- The projective reduction in the first chart, as a total function. -/
def primitiveProjectiveFirstResidue (p : ℕ) (x : Fin 3 → ℤ) : Fin 2 → ZMod p :=
  fun i ↦ (x 0 : ZMod p)⁻¹ * (x i.succ : ZMod p)

/-- Only vectors whose first coordinate is a unit modulo p enter this
packet. The residue equality is kept as multiplication, avoiding division. -/
def primitiveProjectiveFirstPacket (p : ℕ) (S : Finset (Fin 3 → ℤ))
    (rho : Fin 2 → ZMod p) : Finset (Fin 3 → ℤ) := by
  classical
  exact S.filter fun x ↦ (x 0 : ZMod p) ≠ 0 ∧
    ∀ i, (x i.succ : ZMod p) = (x 0 : ZMod p) * rho i

 theorem eval_cast_projective {n : ℕ} (F : MvPolynomial (Fin 3) ℤ)
    (x : Fin 3 → ℤ) :
    eval (fun i ↦ (x i : ZMod n)) (F.map (Int.castRingHom (ZMod n))) =
      (eval x F : ZMod n) := by
  rw [eval_map]
  exact (eval₂_comp (Int.castRingHom (ZMod n)) x F).symm

 theorem eval_cast_plane {n : ℕ} (F : MvPolynomial (Fin 2) ℤ)
    (x : Fin 2 → ℤ) :
    eval (fun i ↦ (x i : ZMod n)) (F.map (Int.castRingHom (ZMod n))) =
      (eval x F : ZMod n) := by
  rw [eval_map]
  exact (eval₂_comp (Int.castRingHom (ZMod n)) x F).symm

/-- A nonsingular projective integer point has a smooth normalized
reduction whenever the first coordinate and one gradient entry survive. -/
theorem primitiveProjectiveFirstResidue_mem_smooth
    {d p : ℕ} (hp : p.Prime) (P : MvPolynomial (Fin 3) ℤ)
    (hPhom : P.IsHomogeneous d) (x : Fin 3 → ℤ) (hPx : eval x P = 0)
    (hx0 : (x 0 : ZMod p) ≠ 0) (j : Fin 3)
    (hgradient : (eval x (pderiv j P) : ZMod p) ≠ 0) :
    primitiveProjectiveFirstResidue p x ∈
      planeCurveSmoothResidues (planeCurveFirstChartDehomogenize P) p := by
  letI : Fact p.Prime := ⟨hp⟩
  let rho := primitiveProjectiveFirstResidue p x
  let z : Fin 2 → ℤ := fun i ↦ ZMod.cast (rho i)
  have hz : ∀ i, (z i : ZMod p) = rho i := fun i ↦ ZMod.intCast_zmod_cast _
  have hscale : ∀ i, (x i : ZMod p) =
      (x 0 : ZMod p) * (planeCurveFirstChartPoint z i : ZMod p) := by
    intro i
    refine Fin.cases ?_ (fun a ↦ ?_) i
    · simp [planeCurveFirstChartPoint]
    · simp only [planeCurveFirstChartPoint, Fin.cases_succ, hz, rho,
        primitiveProjectiveFirstResidue]
      simp [← mul_assoc, hx0]
  have hzero : (eval (planeCurveFirstChartPoint z) P : ZMod p) = 0 := by
    apply (mul_eq_zero.mp (show (x 0 : ZMod p) ^ d *
      (eval (planeCurveFirstChartPoint z) P : ZMod p) = 0 by
      rw [← eval_homogeneous_scaled_modular P hPhom x z hscale, hPx, Int.cast_zero])).resolve_left
    exact pow_ne_zero _ hx0
  have hgrad : (eval (planeCurveFirstChartPoint z) (pderiv j P) : ZMod p) ≠ 0 := by
    intro h
    apply hgradient
    rw [eval_homogeneous_scaled_modular (pderiv j P) hPhom.pderiv x z hscale, h, mul_zero]
  obtain ⟨a, ha⟩ := exists_nonzero_affine_partial_of_homogeneous_gradient
    (P.map (Int.castRingHom (ZMod p))) (hPhom.map _)
    (fun i ↦ (planeCurveFirstChartPoint z i : ZMod p)) (by simp [planeCurveFirstChartPoint])
    (by rwa [eval_cast_projective])
    ⟨j, by
      rw [pderiv_map]
      change eval (fun i ↦ (planeCurveFirstChartPoint z i : ZMod p))
        ((pderiv j P).map (Int.castRingHom (ZMod p))) ≠ 0
      rwa [eval_cast_projective]⟩
  apply (mem_planeCurveSmoothResidues_iff _ hp _).mpr
  have heval (f : MvPolynomial (Fin 2) ℤ) :
      eval rho (f.map (Int.castRingHom (ZMod p))) = (eval z f : ZMod p) := by
    rw [← show (fun i ↦ (z i : ZMod p)) = rho from funext hz, eval_cast_plane]
  refine ⟨?_, a, ?_⟩
  · rw [heval, planeCurveFirstChart_eval]
    exact hzero
  · rw [heval, eval_pderiv_planeCurveFirstChartDehomogenize]
    rw [pderiv_map] at ha
    change eval (fun i ↦ (planeCurveFirstChartPoint z i : ZMod p))
      ((pderiv a.succ P).map (Int.castRingHom (ZMod p))) ≠ 0 at ha
    rw [eval_cast_projective] at ha
    exact ha

/-- A full literal smooth residue packet has the proved 2d² bound. -/
theorem card_primitiveProjectiveFirstPacket_le
    {d B p : ℕ} (hd : 2 ≤ d) (hB : 1 ≤ B) (hp : p.Prime)
    (P : MvPolynomial (Fin 3) ℤ) (hPhom : P.IsHomogeneous d)
    (hPirred : Irreducible (P.map (Int.castRingHom ℚ)))
    (S : Finset (Fin 3 → ℤ))
    (hprimitive : ∀ x ∈ S, IsPrimitiveIntVector x)
    (hzero : ∀ x ∈ S, eval x P = 0)
    (hbox : ∀ x ∈ S, ∀ i, (x i).natAbs ≤ B) (hlarge : 4 * B < p)
    (rho : Fin 2 → ZMod p)
    (hrho : rho ∈ planeCurveSmoothResidues (planeCurveFirstChartDehomogenize P) p) :
    (primitiveProjectiveFirstPacket p S rho).card ≤ 2 * d ^ 2 := by
  classical
  let z : Fin 2 → ℤ := fun i ↦ ZMod.cast (rho i)
  have hz : (fun i ↦ (z i : ZMod p)) = rho := by
    funext i
    exact ZMod.intCast_zmod_cast _
  obtain ⟨hP, v, hv⟩ := (mem_planeCurveSmoothResidues_iff _ hp _).mp hrho
  have heval (f : MvPolynomial (Fin 2) ℤ) :
      eval rho (f.map (Int.castRingHom (ZMod p))) = (eval z f : ZMod p) := by
    rw [← hz, eval_cast_plane]
  apply card_primitivePlaneCurve_firstChartPacket_le hd hB hp P hPhom hPirred
    (primitiveProjectiveFirstPacket p S rho)
    (fun x hx ↦ hprimitive x (Finset.mem_filter.mp hx).1)
    (fun x hx ↦ hzero x (Finset.mem_filter.mp hx).1)
    (fun x hx ↦ (Finset.mem_filter.mp hx).2.1)
    z (by rwa [heval] at hP) ?_ v (by rwa [heval] at hv)
    (fun x hx ↦ hbox x (Finset.mem_filter.mp hx).1) hlarge
  intro x hx i
  rw [congrFun hz i]
  exact (Finset.mem_filter.mp hx).2.2 i

end
end TranslatedDepthSeven
