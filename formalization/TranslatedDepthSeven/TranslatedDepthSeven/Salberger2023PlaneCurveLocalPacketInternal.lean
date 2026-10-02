import TranslatedDepthSeven.Salberger2023PlaneCurveMonomialBlockInternal
import TranslatedDepthSeven.RationalProjectiveCurveFirstChartBezoutInternal

/-!
# An unconditional local packet bound for a literal plane curve

This file supplies the two algebraic inputs of the local determinant
argument internally.  The degree block is selected from the literal plane
monomials, and the final intersection bound is the proved rational
first-chart Bezout theorem.  Thus the final plane-curve packet theorem only
asks for its integral equation, irreducibility over `ℚ`, and the actual
smooth residue-class data.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

universe w

/-- The local determinant argument with one explicit degree block.  This is
the useful intermediate form of equation (3.14): neither a global monomial
selection principle nor a literature Bezout premise occurs in its type. -/
theorem card_curvePacket_le_degree_sq_of_residue_disc_of_block_internal
    {N δ p V : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hIprime : I.IsPrime)
    (hIhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hIdegree : HasProjectiveDimensionDegree I 1 δ)
    (F : Fin (salbergerCurveMonomialCount δ) →
      MvPolynomial (Fin (N + 1)) ℤ)
    (hF : SalbergerCurveDegreeMonomialBlock I F)
    (points : Finset (IntVector N))
    (hIzero : ∀ z ∈ points, ∀ f ∈ I,
      MvPolynomial.eval (rationalIntegralAffineChartPoint z) f = 0)
    (hbox : ∀ z ∈ points, ∀ i,
      (integralAffineChartVector z i).natAbs ≤ V)
    (hpositive : 0 <
      affineLineJetWeight (salbergerCurveMonomialCount δ))
    (disc : CurveNormalizationResidueDisc.{0,0,w}
      (Fin (N + 1)) (Fin points.card) p
      (affineLineJetWeight (salbergerCurveMonomialCount δ)) hpositive
      (fun j ↦ integralAffineChartVector (points.equivFin.symm j).1))
    (hlarge : (salbergerCurveMonomialCount δ).factorial *
      V ^ (δ * salbergerCurveMonomialCount δ) <
        p ^ affineLineJetWeight (salbergerCurveMonomialCount δ)) :
    points.card ≤ δ ^ 2 := by
  classical
  obtain ⟨hFindependent, hFhomogeneous, hFheight⟩ := hF
  let x : Fin points.card → Fin (N + 1) → ℤ :=
    fun j ↦ integralAffineChartVector (points.equivFin.symm j).1
  have hbound : ∀ j i,
      (MvPolynomial.eval (x j) (F i)).natAbs ≤ V ^ δ := by
    intro j i
    apply hFheight V (x j)
    intro a
    exact hbox (points.equivFin.symm j).1
      (points.equivFin.symm j).2 a
  have hlarge' : (salbergerCurveMonomialCount δ).factorial *
      ∏ _i : Fin (salbergerCurveMonomialCount δ), V ^ δ <
        p ^ affineLineJetWeight (salbergerCurveMonomialCount δ) := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← pow_mul] using hlarge
  obtain ⟨G, hGhom, hGnot, hGzeroFin⟩ :=
    exists_curvePacket_auxiliary_of_residue_disc
      I F hFindependent hFhomogeneous x hpositive disc
        (fun _ ↦ V ^ δ) hbound hlarge'
  have hGzero : ∀ z ∈ points,
      MvPolynomial.eval (rationalIntegralAffineChartPoint z) G = 0 := by
    intro z hz
    let j : Fin points.card := points.equivFin ⟨z, hz⟩
    have hj := hGzeroFin j
    have hx : x j = integralAffineChartVector z := by
      dsimp only [x, j]
      rw [Equiv.symm_apply_apply]
    simpa only [rationalIntegralAffineChartPoint, hx] using hj
  have hcard := card_integralAffinePoints_on_projectiveCurve_auxiliary_le
    rationalProjectiveCurveAuxiliaryFirstChartBezout_internal
      I G hIprime hIhomogeneous hIdegree hGhom hGnot points
        hIzero hGzero
  simpa [pow_two] using hcard

private theorem eval_map_intCast_eq_plane
    {N : ℕ} (x : Fin (N + 1) → ℤ) (P : MvPolynomial (Fin (N + 1)) ℤ) :
    MvPolynomial.eval (fun i ↦ (x i : ℚ))
        (P.map (Int.castRingHom ℚ)) =
      (MvPolynomial.eval x P : ℚ) := by
  rw [MvPolynomial.eval_map]
  exact (MvPolynomial.eval₂_comp (Int.castRingHom ℚ) x P).symm

/-- Equation (3.14) for a literal irreducible integral homogeneous plane
equation.  All Hilbert-function, residue-disc, determinant, auxiliary-form,
and Bezout steps are discharged in the proof. -/
theorem card_integralPlaneCurvePacket_le_degree_sq_of_prime_threshold_internal
    {δ p V : ℕ} (hδ : 1 ≤ δ) (hV : 1 ≤ V) (hpprime : p.Prime)
    (P : MvPolynomial (Fin 3) ℤ)
    (hPhom : P.IsHomogeneous δ)
    (hPirred : Irreducible (P.map (Int.castRingHom ℚ)))
    (points : Finset (IntVector 2))
    (hPzero : ∀ z ∈ points,
      MvPolynomial.eval (integralAffineChartVector z) P = 0)
    (center : Fin 2 → ℤ)
    (hsame : ∀ z ∈ points, ∀ i, (p : ℤ) ∣ z i - center i)
    (v : Fin 2)
    (hpartial : (MvPolynomial.eval center
      (MvPolynomial.pderiv v (planeCurveFirstChartDehomogenize P)) : ZMod p) ≠ 0)
    (hbox : ∀ z ∈ points, ∀ i,
      (integralAffineChartVector z i).natAbs ≤ V)
    (hp : 4 * (V : ℝ) ^ (8 / ((δ : ℝ) + 3)) < p) :
    points.card ≤ δ ^ 2 := by
  classical
  let Pℚ : MvPolynomial (Fin 3) ℚ := P.map (Int.castRingHom ℚ)
  let I : Ideal (MvPolynomial (Fin 3) ℚ) := Ideal.span ({Pℚ} : Set _)
  have hPne : P ≠ 0 := by
    intro hzero
    subst P
    exact hPirred.ne_zero rfl
  have hPℚne : Pℚ ≠ 0 := hPirred.ne_zero
  have hIprime : I.IsPrime := by
    exact (Ideal.span_singleton_prime hPℚne).mpr hPirred.prime
  have hIhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 3) ℚ) := by
    apply Ideal.homogeneous_span
    intro G hG
    have hGP : G = Pℚ := Set.mem_singleton_iff.mp hG
    exact ⟨δ, hGP.symm ▸ hPhom.map (Int.castRingHom ℚ)⟩
  have hIdegree : HasProjectiveDimensionDegree I 1 δ := by
    exact hasProjectiveDimensionDegree_principal_homogeneous Pℚ
      (hPhom.map (Int.castRingHom ℚ)) hPℚne (by omega) hIprime
  have hpositive :
      0 < affineLineJetWeight (salbergerCurveMonomialCount δ) := by
    have hs := salbergerCurveMonomialCount_two_le hδ
    have hweight :=
      two_mul_affineLineJetWeight (salbergerCurveMonomialCount δ)
    have hprod : 0 < salbergerCurveMonomialCount δ *
        (salbergerCurveMonomialCount δ - 1) :=
      Nat.mul_pos (by omega) (by omega)
    omega
  have hIzero : ∀ z ∈ points, ∀ f ∈ I,
      MvPolynomial.eval (rationalIntegralAffineChartPoint z) f = 0 := by
    intro z hz f hf
    let ev : MvPolynomial (Fin 3) ℚ →+* ℚ :=
      MvPolynomial.eval₂Hom (RingHom.id ℚ) (rationalIntegralAffineChartPoint z)
    have hgen : Pℚ ∈ RingHom.ker ev := by
      rw [RingHom.mem_ker]
      change MvPolynomial.eval (rationalIntegralAffineChartPoint z) Pℚ = 0
      rw [show MvPolynomial.eval (rationalIntegralAffineChartPoint z) Pℚ =
          (MvPolynomial.eval (integralAffineChartVector z) P : ℚ) by
        exact eval_map_intCast_eq_plane (integralAffineChartVector z) P]
      simp only [hPzero z hz, Int.cast_zero]
    have hspan : I ≤ RingHom.ker ev := by
      apply Ideal.span_le.mpr
      intro G hG
      simpa only [Set.mem_singleton_iff.mp hG] using hgen
    exact RingHom.mem_ker.mp (hspan hf)
  obtain ⟨F, hF⟩ := exists_planeCurveDegreeMonomialBlock_internal P hPhom hPne
  by_cases hnonempty : points.Nonempty
  · letI : Nonempty (Fin points.card) :=
      ⟨⟨0, Finset.card_pos.mpr hnonempty⟩⟩
    let y : Fin points.card → Fin 2 → ℤ :=
      fun j ↦ (points.equivFin.symm j).1
    have hyP : ∀ j, MvPolynomial.eval (planeCurveFirstChartPoint (y j)) P = 0 := by
      intro j
      simpa only [planeCurveFirstChartPoint, integralAffineChartVector] using
        hPzero (points.equivFin.symm j).1 (points.equivFin.symm j).2
    have hyz : ∀ j i, (p : ℤ) ∣ y j i - center i := by
      intro j i
      exact hsame (points.equivFin.symm j).1 (points.equivFin.symm j).2 i
    let disc : CurveNormalizationResidueDisc
        (Fin 3) (Fin points.card) p
        (affineLineJetWeight (salbergerCurveMonomialCount δ)) hpositive
        (fun j ↦ integralAffineChartVector (points.equivFin.symm j).1) := by
      simpa only [y, planeCurveFirstChartPoint, integralAffineChartVector] using
        planeCurveFirstChartResidueDiscAt p
          (affineLineJetWeight (salbergerCurveMonomialCount δ))
          hpprime hpositive P y center hyP hyz v hpartial
    have hlarge := salberger_curve_determinant_size_of_prime_threshold
      hδ hV hp
    exact card_curvePacket_le_degree_sq_of_residue_disc_of_block_internal
      I hIprime hIhomogeneous hIdegree F (by simpa only [I, Pℚ] using hF)
        points hIzero hbox hpositive disc hlarge
  · simp only [Finset.not_nonempty_iff_eq_empty] at hnonempty
    simp [hnonempty]

end

end TranslatedDepthSeven
