import TranslatedDepthSeven.FormallyEtaleSurfaceDeterminant
import TranslatedDepthSeven.NormalizationSurfaceBlockEvaluation
import TranslatedDepthSeven.SurfaceNormalizationDeterminantThreshold
import TranslatedDepthSeven.AuxiliaryFormFromEvaluationRank

/-!
# Actual residue discs and normalization-block determinants

The local data consists of actual ring maps from a formally etale chart to
`ZMod (p^E)`. Their compositions with the ambient polynomial map are the
reductions of the displayed integer points. All maps at one prime lie over
the same chart point. Different primes may use different charts. No
determinant divisibility or auxiliary-polynomial existence is an input.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial
open scoped BigOperators

universe u v w

/-- Literal chart and specialization data for one common residue disc.
The chart may be a principal localization: its values need only exist
modulo the prime power, not over the integers. -/
structure SurfaceNormalizationResidueDisc
    (σ : Type u) (ι : Type v) (p E : ℕ) (hE : 0 < E)
    (y : ι → σ → ℤ) where
  Chart : Type w
  [commRing : CommRing Chart]
  [algebra : Algebra BivariateIntPolynomial Chart]
  [formallyEtale : Algebra.FormallyEtale BivariateIntPolynomial Chart]
  ambient : MvPolynomial σ ℤ →+* Chart
  center : Fin 2 → ℤ
  parameters : ι → Fin 2 → ℤ
  congruent : ∀ j i, (p : ℤ) ∣ parameters j i - center i
  point : Chart →+* ZMod p
  point_base : point.comp (algebraMap BivariateIntPolynomial Chart) =
    evalBivariateIntPolynomialZMod p center
  specialization : ι → Chart →+* ZMod (p ^ E)
  specialization_base : ∀ j,
    (specialization j).comp (algebraMap BivariateIntPolynomial Chart) =
      evalBivariateIntPolynomialZMod (p ^ E) (parameters j)
  specialization_reduction : ∀ j,
    (zmodPrimePowerReduction p E hE).comp (specialization j) = point
  specialization_ambient : ∀ j,
    (specialization j).comp ambient =
      MvPolynomial.eval₂Hom (Int.castRingHom (ZMod (p ^ E)))
        (fun i => (y j i : ZMod (p ^ E)))

attribute [instance] SurfaceNormalizationResidueDisc.commRing
  SurfaceNormalizationResidueDisc.algebra SurfaceNormalizationResidueDisc.formallyEtale

/-- Restrict a common residue disc to any selected family of its points. -/
def SurfaceNormalizationResidueDisc.reindex
    {σ : Type u} {ι : Type v} {κ : Type*} {p E : ℕ} {hE : 0 < E}
    {y : ι → σ → ℤ}
    (disc : SurfaceNormalizationResidueDisc.{u,v,w} σ ι p E hE y)
    (f : κ → ι) :
    SurfaceNormalizationResidueDisc σ κ p E hE (fun j => y (f j)) where
  Chart := disc.Chart
  ambient := disc.ambient
  center := disc.center
  parameters j := disc.parameters (f j)
  congruent j := disc.congruent (f j)
  point := disc.point
  point_base := disc.point_base
  specialization j := disc.specialization (f j)
  specialization_base j := disc.specialization_base (f j)
  specialization_reduction j := disc.specialization_reduction (f j)
  specialization_ambient j := disc.specialization_ambient (f j)

/-- The actual modular chart maps imply local divisibility for arbitrary
ambient polynomial evaluations. Rows index forms and columns index points. -/
theorem SurfaceNormalizationResidueDisc.det_dvd
    {σ : Type u} {ι : Type v} [Fintype ι] [DecidableEq ι]
    (t s : ℕ) (hcard : Fintype.card ι = affinePlaneMonomialCount t + s)
    (hE : 0 < affinePlaneMonomialWeight t + (t + 1) * s)
    (p : ℕ) (y : ι → σ → ℤ)
    (disc : SurfaceNormalizationResidueDisc.{u,v,w} σ ι p
      (affinePlaneMonomialWeight t + (t + 1) * s) hE y)
    (F : ι → MvPolynomial σ ℤ) :
    (p : ℤ) ^ (affinePlaneMonomialWeight t + (t + 1) * s) ∣
      (Matrix.of (fun i j => MvPolynomial.eval (y j) (F i))).det := by
  apply formallyEtaleSurfaceIntegerEvaluations_det_dvd t s hcard hE p
    disc.center disc.parameters disc.congruent disc.point disc.point_base
    (fun i => disc.ambient (F i)) disc.specialization
    disc.specialization_base disc.specialization_reduction
    (Matrix.of (fun i j => MvPolynomial.eval (y j) (F i)))
  intro i j
  have h := RingHom.congr_fun (disc.specialization_ambient j) (F i)
  change disc.specialization j (disc.ambient (F i)) = _ at h
  rw [h]
  exact (MvPolynomial.eval₂_comp
    (Int.castRingHom (ZMod (p ^ (affinePlaneMonomialWeight t + (t + 1) * s))))
      (y j) (F i))

/-- Genuine residue-disc hypotheses supply the local divisibilities needed
by the sharp normalization-block comparison. -/
theorem normalizationSurfaceBlock_det_eq_zero_of_residue_discs
    {σ : Type u} (d b D k t s B q : ℕ)
    (hrows : d * affinePlaneMonomialCount k = affinePlaneMonomialCount t + s)
    (hE : 0 < affinePlaneMonomialWeight t + (t + 1) * s)
    (L : Fin 3 → MvPolynomial σ ℤ) (G : Fin d → MvPolynomial σ ℤ)
    (y : Fin d × AffinePlaneMonomialIndex k → σ → ℤ)
    (hq : Squarefree q)
    (hdisc : ∀ p, p.Prime → p ∣ q → Nonempty
      (SurfaceNormalizationResidueDisc.{u,0,w} σ
        (Fin d × AffinePlaneMonomialIndex k) p
          (affinePlaneMonomialWeight t + (t + 1) * s) hE y))
    (hG : ∀ v i, (MvPolynomial.eval (y v) (G i)).natAbs ≤ D * B ^ b)
    (hzero : ∀ v, MvPolynomial.eval (y v) (L 0) = 1)
    (hone : ∀ v, (MvPolynomial.eval (y v) (L 1)).natAbs ≤ B)
    (htwo : ∀ v, (MvPolynomial.eval (y v) (L 2)).natAbs ≤ B)
    (hlarge : (d * affinePlaneMonomialCount k).factorial *
      D ^ (d * affinePlaneMonomialCount k) *
      B ^ (b * (d * affinePlaneMonomialCount k) + d * affinePlaneMonomialWeight k) <
        q ^ (affinePlaneMonomialWeight t + (t + 1) * s)) :
    (Matrix.of (fun v i => MvPolynomial.eval (y v)
      (normalizationSurfaceBlockForm L G k i))).det = 0 := by
  classical
  apply det_normalizationSurfaceBlockEvaluation_eq_zero
    L G (fun _ => D * B ^ b) B k q
      (affinePlaneMonomialWeight t + (t + 1) * s) y hq
  · intro p hp hpq
    obtain ⟨disc⟩ := hdisc p hp hpq
    have hc : Fintype.card (Fin d × AffinePlaneMonomialIndex k) =
        affinePlaneMonomialCount t + s := by
      simpa only [Fintype.card_prod, Fintype.card_fin,
        card_affinePlaneMonomialIndex] using hrows
    have h := disc.det_dvd t s hc hE p y (normalizationSurfaceBlockForm L G k)
    change (p : ℤ) ^ (affinePlaneMonomialWeight t + (t + 1) * s) ∣
      (Matrix.of (fun v i => MvPolynomial.eval (y v)
        (normalizationSurfaceBlockForm L G k i))).transpose.det at h
    simpa only [Matrix.det_transpose] using h
  · exact hG
  · exact hzero
  · exact hone
  · exact htwo
  · simp only [Fintype.card_prod, Fintype.card_fin, card_affinePlaneMonomialIndex,
      Finset.prod_const, Finset.card_univ, mul_pow, ← pow_mul, ← mul_assoc]
    simpa only [mul_assoc, ← pow_add, Nat.mul_assoc] using hlarge

/-- A normalization block and a box threshold, chosen before every chart,
point family and modulus, force its evaluation determinant to vanish.
Each prime divisor of the squarefree modulus has one common, actual
formally-etale residue disc for all the displayed points. -/
theorem exists_normalizationSurfaceBlock_det_eq_zero_of_residue_discs
    {σ : Type u} (d b D : ℕ) (hd : 0 < d) (η : ℝ) (hη : 0 < η) :
    ∃ k t s : ℕ, ∃ B₀ : ℝ, 1 ≤ B₀ ∧
      ∃ hE : 0 < affinePlaneMonomialWeight t + (t + 1) * s,
      d * affinePlaneMonomialCount k = affinePlaneMonomialCount t + s ∧
      s < t + 2 ∧
      ∀ (L : Fin 3 → MvPolynomial σ ℤ) (G : Fin d → MvPolynomial σ ℤ)
        (B q : ℕ) (y : Fin d × AffinePlaneMonomialIndex k → σ → ℤ),
        B₀ ≤ (B : ℝ) → (B : ℝ) ^ (1 / Real.sqrt (d : ℝ) + η) ≤ q →
        Squarefree q →
        (∀ p, p.Prime → p ∣ q → Nonempty
          (SurfaceNormalizationResidueDisc.{u,0,w} σ
            (Fin d × AffinePlaneMonomialIndex k) p
              (affinePlaneMonomialWeight t + (t + 1) * s) hE y)) →
        (∀ v i, (MvPolynomial.eval (y v) (G i)).natAbs ≤ D * B ^ b) →
        (∀ v, MvPolynomial.eval (y v) (L 0) = 1) →
        (∀ v, (MvPolynomial.eval (y v) (L 1)).natAbs ≤ B) →
        (∀ v, (MvPolynomial.eval (y v) (L 2)).natAbs ≤ B) →
        (Matrix.of (fun v i => MvPolynomial.eval (y v)
          (normalizationSurfaceBlockForm L G k i))).det = 0 := by
  obtain ⟨k, t, s, B₀, hB₀, hrows, hs, hE, hbound⟩ :=
    exists_surfaceNormalization_determinant_threshold_nat d b D hd η hη
  refine ⟨k, t, s, B₀, hB₀, hE, hrows, hs, ?_⟩
  intro L G B q y hB hqsize hq hdisc hG hzero hone htwo
  exact normalizationSurfaceBlock_det_eq_zero_of_residue_discs
    d b D k t s B q hrows hE L G y hq hdisc hG hzero hone htwo
      (hbound B q hB hqsize)

end
end TranslatedDepthSeven
