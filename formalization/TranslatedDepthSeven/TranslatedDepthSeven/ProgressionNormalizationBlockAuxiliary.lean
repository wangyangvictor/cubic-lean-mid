import TranslatedDepthSeven.ProgressionNormalizationBlockHypersurface
import TranslatedDepthSeven.ProgressionNormalizationBlockFixedSurface
import TranslatedDepthSeven.AuxiliaryFormFromEvaluationRank

/-! A proper auxiliary form in the fixed ideal's ambient ring, from literal
hypersurface packets and the exact two-radius determinant threshold. -/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000

theorem progressionNormalizationBlock_det_eq_zero_of_hypersurface
    {d : ℕ} (hd : 0 < d) (k t s pmod m D H b R : ℕ)
    (hcard : Fintype.card (Fin d × AffinePlaneMonomialIndex k) = affinePlaneMonomialCount t + s)
    (hE : 0 < affinePlaneMonomialWeight t + (t + 1) * s)
    (L : Fin 3 → MvPolynomial (Fin 4) ℤ)
    (hL : ∀ i, (L i).IsHomogeneous 1) (hL0 : L 0 = X 0)
    (G : Fin d → MvPolynomial (Fin 4) ℤ)
    (F : MvPolynomial (Fin 4) ℤ) (u : Fin 3 → ℤ)
    (y : Fin d × AffinePlaneMonomialIndex k → Fin 3 → ℤ)
    (hyF : ∀ j, MvPolynomial.eval (progressionHomogeneousPoint u m (y j)) F = 0)
    (hq : Squarefree pmod)
    (hlocal : ∀ p, p.Prime → p ∣ pmod → ¬ p ∣ m ∧
      ∃ (z : Fin 3 → ℤ) (v : Fin 3),
        (∀ j i, (p : ℤ) ∣ y j i - z i) ∧
        (MvPolynomial.eval (fun i => u i + (m : ℤ) * z i)
          (MvPolynomial.pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0)
    (hG : ∀ j i, (MvPolynomial.eval (progressionHomogeneousPoint u m (y j)) (G i)).natAbs ≤ D * H ^ b)
    (hparams : ∀ j i, (progressionParameterValues L (y j) i).natAbs ≤ R)
    (hlarge : (d * affinePlaneMonomialCount k).factorial *
      (D * H ^ b) ^ (d * affinePlaneMonomialCount k) *
        R ^ (d * affinePlaneMonomialWeight k) <
          pmod ^ (affinePlaneMonomialWeight t + (t + 1) * s)) :
    (Matrix.of (fun j i => progressionNormalizationBlockEntry L G u m k (y j) i)).det = 0 := by
  classical
  have hdiv : (pmod : ℤ) ^ (affinePlaneMonomialWeight t + (t + 1) * s) ∣
      (Matrix.of (fun j i => progressionNormalizationBlockEntry L G u m k (y j) i)).det := by
    apply squarefreePower_dvd_of_primePower_dvd hq
    intro p hp hpq
    obtain ⟨hpm, z, v, hyz, hzJ⟩ := hlocal p hp hpq
    exact progressionNormalizationBlock_det_dvd_of_hypersurface hd k t s p m hp hpm
      hcard hE L hL hL0 G F u y z hyF hyz v hzJ
  apply TangentMinors.eq_zero_of_dvd_of_natAbs_lt hdiv
  simpa using (progressionNormalizationBlock_det_natAbs_le L G u m k D H b R y hG hparams).trans_lt hlarge

/-- This endpoint constructs the proper homogeneous cut for a finite packet.
The independence hypothesis concerns the unmodified fixed block. The output
is not in the same original ideal, and vanishes at the original points
`(1,u+m*y)`. No transformed ideal is introduced. -/
theorem exists_progression_auxiliary_of_hypersurface_packets
    {d : ℕ} (hd : 0 < d) (b k t s D H R q m S : ℕ)
    (hm : m ≠ 0)
    (hcard : Fintype.card (Fin d × AffinePlaneMonomialIndex k) = affinePlaneMonomialCount t + s)
    (hE : 0 < affinePlaneMonomialWeight t + (t + 1) * s)
    (I : Ideal (MvPolynomial (Fin 4) ℚ))
    (L : Fin 3 → MvPolynomial (Fin 4) ℤ)
    (hL : ∀ i, (L i).IsHomogeneous 1) (hL0 : L 0 = X 0)
    (G : Fin d → MvPolynomial (Fin 4) ℤ) (hGhom : ∀ i, (G i).IsHomogeneous b)
    (hLI : LinearIndependent ℚ (fun p : Fin d × AffinePlaneMonomialIndex k =>
      Ideal.Quotient.mk I (MvPolynomial.map (Int.castRingHom ℚ)
        (normalizationSurfaceBlockForm L G k p))))
    (F : MvPolynomial (Fin 4) ℤ) (u : Fin 3 → ℤ) (y : Fin S → Fin 3 → ℤ)
    (hyF : ∀ j, MvPolynomial.eval (progressionHomogeneousPoint u m (y j)) F = 0)
    (hq : Squarefree q)
    (hlocal : ∀ p, p.Prime → p ∣ q → ¬ p ∣ m ∧
      ∃ (z : Fin 3 → ℤ) (v : Fin 3),
        (∀ j i, (p : ℤ) ∣ y j i - z i) ∧
        (MvPolynomial.eval (fun i => u i + (m : ℤ) * z i)
          (MvPolynomial.pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0)
    (hG : ∀ j i, (MvPolynomial.eval (progressionHomogeneousPoint u m (y j)) (G i)).natAbs ≤ D * H ^ b)
    (hparams : ∀ j i, (progressionParameterValues L (y j) i).natAbs ≤ R)
    (hlarge : (d * affinePlaneMonomialCount k).factorial *
      (D * H ^ b) ^ (d * affinePlaneMonomialCount k) *
        R ^ (d * affinePlaneMonomialWeight k) <
          q ^ (affinePlaneMonomialWeight t + (t + 1) * s)) :
    ∃ P : MvPolynomial (Fin 4) ℚ, P.IsHomogeneous (b + k) ∧ P ∉ I ∧
      ∀ j, MvPolynomial.eval (fun i => (progressionHomogeneousPoint u m (y j) i : ℚ)) P = 0 := by
  classical
  let ι := Fin d × AffinePlaneMonomialIndex k
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let FQ : Fin (Fintype.card ι) → MvPolynomial (Fin 4) ℚ :=
    fun i => progressionRationalBlockForm L G u m k (e.symm i)
  apply exists_auxiliaryHomogeneousPolynomial_of_all_evaluation_minors_eq_zero
    I FQ (fun j i => (progressionHomogeneousPoint u m (y j) i : ℚ))
  · exact (linearIndependent_progressionRationalBlockForm I L G u m k hm hLI).comp
      e.symm e.symm.injective
  · intro i
    exact progressionRationalBlockForm_isHomogeneous L hL G hGhom u m k (e.symm i)
  · intro cols _hcols
    let select : ι → Fin S := fun i => cols (e i)
    have hselected : ∀ p, p.Prime → p ∣ q → ¬ p ∣ m ∧
        ∃ (z : Fin 3 → ℤ) (v : Fin 3),
          (∀ j i, (p : ℤ) ∣ y (select j) i - z i) ∧
          (MvPolynomial.eval (fun i => u i + (m : ℤ) * z i)
            (MvPolynomial.pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0 := by
      intro p hp hpq
      obtain ⟨hpm, z, v, hyz, hzJ⟩ := hlocal p hp hpq
      exact ⟨hpm, z, v, fun j i => hyz (select j) i, hzJ⟩
    have hz := progressionNormalizationBlock_det_eq_zero_of_hypersurface hd k t s q m D H b R
      hcard hE L hL hL0 G F u (fun j => y (select j)) (fun j => hyF (select j))
      hq hselected (fun j i => hG (select j) i) (fun j i => hparams (select j) i) hlarge
    let Z : Matrix ι ι ℤ := Matrix.of (fun i j =>
      progressionNormalizationBlockEntry L G u m k (y (select j)) i)
    have hZ : Z.det = 0 := by
      change Z.transpose.det = 0 at hz
      simpa only [Matrix.det_transpose] using hz
    let Q : Matrix ι ι ℚ := Matrix.of (fun i j =>
      MvPolynomial.eval (fun a => (progressionHomogeneousPoint u m (y (select j)) a : ℚ))
        (progressionRationalBlockForm L G u m k i))
    have hQmap : Q = (Int.castRingHom ℚ).mapMatrix Z := by
      ext i j
      exact eval_progressionRationalBlockForm L hL hL0 G u m k hm (y (select j)) i
    have hQ : Q.det = 0 := by
      rw [hQmap, ← (Int.castRingHom ℚ).map_det, hZ, map_zero]
    have hreindex := (Matrix.det_submatrix_equiv_self e.symm Q).trans hQ
    simpa only [Q, FQ, Matrix.submatrix, Matrix.of_apply, select,
      Equiv.apply_symm_apply, id_eq] using hreindex

end
end TranslatedDepthSeven
