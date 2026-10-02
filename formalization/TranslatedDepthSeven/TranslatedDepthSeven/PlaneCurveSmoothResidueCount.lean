import TranslatedDepthSeven.SchwartzZippelResidueCount
import TranslatedDepthSeven.FiniteResiduePacket

/-!
# Elementary counting of smooth plane-curve reductions

Only Schwartz--Zippel is used.  The set of nonsingular zeros is empty if
the polynomial reduces to zero, so no good-reduction or primitive-content
assumption is needed for this bound.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

/-- The literal nonsingular zero set of a fixed integral plane equation
over `ZMod p`.  The value at a nonprime modulus is empty, so this can be
used as a total dependent family of finite sets. -/
def planeCurveSmoothResidues (f : MvPolynomial (Fin 2) ℤ) (p : ℕ) :
    Finset (Fin 2 → ZMod p) := by
  classical
  exact if hp : p.Prime then
    (mvPolynomialZeroSet p 2 hp (map (Int.castRingHom (ZMod p)) f)).filter
      (fun rho ↦ ∃ j : Fin 2,
        eval rho (map (Int.castRingHom (ZMod p)) (pderiv j f)) ≠ 0)
  else ∅

theorem mem_planeCurveSmoothResidues_iff
    (f : MvPolynomial (Fin 2) ℤ) {p : ℕ} (hp : p.Prime)
    (rho : Fin 2 → ZMod p) :
    rho ∈ planeCurveSmoothResidues f p ↔
      eval rho (map (Int.castRingHom (ZMod p)) f) = 0 ∧
      ∃ j : Fin 2,
        eval rho (map (Int.castRingHom (ZMod p)) (pderiv j f)) ≠ 0 := by
  classical
  simp only [planeCurveSmoothResidues, dif_pos hp, Finset.mem_filter,
    mem_mvPolynomialZeroSet_iff]

/-- Even at a prime with identically zero reduction, the number of
nonsingular residues is at most the degree times `p`. -/
theorem card_planeCurveSmoothResidues_le
    (f : MvPolynomial (Fin 2) ℤ) {p : ℕ} (hp : p.Prime) :
    (planeCurveSmoothResidues f p).card ≤ f.totalDegree * p := by
  classical
  by_cases hf : map (Int.castRingHom (ZMod p)) f = 0
  · have hempty : planeCurveSmoothResidues f p = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro rho hrho
      obtain ⟨j, hj⟩ := (mem_planeCurveSmoothResidues_iff f hp rho).mp hrho |>.2
      rw [← pderiv_map, hf, map_zero, map_zero] at hj
      exact hj rfl
    simp [hempty]
  · have hsub : planeCurveSmoothResidues f p ⊆
        mvPolynomialZeroSet p 2 hp (map (Int.castRingHom (ZMod p)) f) := by
      intro rho hrho
      exact (mem_mvPolynomialZeroSet_iff hp _ _).mpr
        ((mem_planeCurveSmoothResidues_iff f hp rho).mp hrho).1
    have hdegree : (map (Int.castRingHom (ZMod p)) f).totalDegree ≤
        f.totalDegree :=
      Finset.sup_mono (support_map_subset (Int.castRingHom (ZMod p)) f)
    have hcount := card_mvPolynomialZeroSet_le_degree_mul hp _ hf hdegree
    exact (Finset.card_le_card hsub).trans (by simpa using hcount)

/-- An actual integer zero with one derivative not divisible by `p`
reduces to the literal good-residue list. -/
theorem integralResidueVector_mem_planeCurveSmoothResidues
    (f : MvPolynomial (Fin 2) ℤ) {p : ℕ} (hp : p.Prime)
    (z : IntVector 2) (hzero : eval z f = 0)
    (j : Fin 2) (hderivative : ¬ (p : ℤ) ∣ eval z (pderiv j f)) :
    integralResidueVector z ∈ planeCurveSmoothResidues f p := by
  apply (mem_planeCurveSmoothResidues_iff f hp _).mpr
  have heval (g : MvPolynomial (Fin 2) ℤ) :
      eval (integralResidueVector z) (map (Int.castRingHom (ZMod p)) g) =
        (eval z g : ZMod p) := by
    rw [eval_map]
    exact (eval₂_comp (Int.castRingHom (ZMod p)) z g).symm
  refine ⟨?_, j, ?_⟩
  · rw [heval, hzero, Int.cast_zero]
  · rw [heval]
    exact fun h ↦ hderivative ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)

end

end TranslatedDepthSeven
