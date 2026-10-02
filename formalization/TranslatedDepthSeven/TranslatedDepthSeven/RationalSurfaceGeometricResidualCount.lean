import TranslatedDepthSeven.GeometricProgressionChangedComponentCount
import TranslatedDepthSeven.ProjectiveHilbertCoefficientExtension
import TranslatedDepthSeven.CoefficientExtensionHomogeneousIdeal

/-!
# Geometric residual counts for rational surface auxiliaries

The source is a literal rational finite equation family whose coefficient
extension to the algebraic closure is prime. Rational auxiliary forms are
extended coefficientwise, and labels are selected from their actual geometric
minimal primes. Faithful flatness preserves properness of each auxiliary cut,
and the already proved coefficient-extension theorem preserves the source
dimension and degree. No geometric-component count is an input.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000

/-- Literal coefficientwise extension of a finite rational equation family. -/
def qbarSurfaceEquationFamily {σ : Type*} (E : Finset (MvPolynomial σ ℚ)) :
    Finset (MvPolynomial σ Qbar) := by
  classical
  exact E.image (MvPolynomial.map (algebraMap ℚ Qbar))

@[simp] theorem mem_qbarSurfaceEquationFamily
    {σ : Type*} (E : Finset (MvPolynomial σ ℚ)) (f : MvPolynomial σ Qbar) :
    f ∈ qbarSurfaceEquationFamily E ↔
      ∃ g ∈ E, MvPolynomial.map (algebraMap ℚ Qbar) g = f := by
  classical
  exact Finset.mem_image

theorem finiteEquationIdeal_qbarSurfaceEquationFamily
    {σ : Type*} (E : Finset (MvPolynomial σ ℚ)) :
    finiteEquationIdeal (qbarSurfaceEquationFamily E) =
      (finiteEquationIdeal E).map (MvPolynomial.map (algebraMap ℚ Qbar)) := by
  classical
  rw [finiteEquationIdeal, finiteEquationIdeal, Ideal.map_span]
  congr 1
  exact Finset.coe_image

/-- The actual extended source equations together with one rational auxiliary. -/
def qbarSurfaceCutEquationFamily {σ : Type*}
    (E : Finset (MvPolynomial σ ℚ)) (G : MvPolynomial σ ℚ) :
    Finset (MvPolynomial σ Qbar) :=
  finiteEquationFamilyUnion (qbarSurfaceEquationFamily E)
    {MvPolynomial.map (algebraMap ℚ Qbar) G}

/-- A proper rational auxiliary remains proper after extending coefficients. -/
theorem qbarMap_not_mem_extendedIdeal_of_not_mem
    {σ : Type*} (I : Ideal (MvPolynomial σ ℚ)) (G : MvPolynomial σ ℚ)
    (hG : G ∉ I) :
    MvPolynomial.map (algebraMap ℚ Qbar) G ∉
      I.map (MvPolynomial.map (algebraMap ℚ Qbar)) := by
  letI : Algebra (MvPolynomial σ ℚ) (MvPolynomial σ Qbar) :=
    MvPolynomial.algebraMvPolynomial
  have hcontract :
      (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).comap
        (MvPolynomial.map (algebraMap ℚ Qbar)) = I := by
    simpa only [MvPolynomial.algebraMap_apply] using
      (Ideal.comap_map_eq_self_of_faithfullyFlat I)
  intro h
  apply hG
  rw [← hcontract]
  exact h

theorem eval_qbarMap_progression
    {N : ℕ} (G : MvPolynomial (Fin (N + 1)) ℚ)
    (u : Fin N → ℤ) (m : ℕ) (z : Fin N → ℤ) :
    eval (fun i => (progressionHomogeneousPoint u m z i : Qbar))
      (MvPolynomial.map (algebraMap ℚ Qbar) G) =
      algebraMap ℚ Qbar (eval (fun i => (progressionHomogeneousPoint u m z i : ℚ)) G) := by
  simpa only [Function.comp_def, map_intCast] using
    (MvPolynomial.map_eval (algebraMap ℚ Qbar)
      (fun i => (progressionHomogeneousPoint u m z i : ℚ)) G).symm

/-- On an absolutely integral rational surface, residual progression points
where the actual geometric component label changes are bounded by the number
of occupied rational auxiliary-pair records times `(d e₁)(d e₂)`.
All base-change and component-degree steps are proved, rather than premises. -/
theorem card_rationalSurfaceProgression_changed_geometricCutPairRecords_le
    {N d e₁ e₂ m : ℕ} (hm : 0 < m)
    (sourceEquations : Finset (MvPolynomial (Fin (N + 1)) ℚ))
    (hgeometricPrime : ((finiteEquationIdeal sourceEquations).map
      (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime)
    (hhom : (finiteEquationIdeal sourceEquations).IsHomogeneous
      (homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hdegree : HasProjectiveDimensionDegree (finiteEquationIdeal sourceEquations) 2 d)
    (records : Finset (MvPolynomial (Fin (N + 1)) ℚ × MvPolynomial (Fin (N + 1)) ℚ))
    (record : (Fin N → ℤ) →
      MvPolynomial (Fin (N + 1)) ℚ × MvPolynomial (Fin (N + 1)) ℚ)
    (hforms : ∀ R ∈ records,
      R.1.IsHomogeneous e₁ ∧ R.1 ∉ finiteEquationIdeal sourceEquations ∧
      R.2.IsHomogeneous e₂ ∧ R.2 ∉ finiteEquationIdeal sourceEquations)
    (u : Fin N → ℤ) (S : Finset (Fin N → ℤ))
    (hrecord : ∀ z ∈ S, record z ∈ records)
    (hsource : ∀ z ∈ S,
      (fun i => (progressionHomogeneousPoint u m z i : ℚ)) ∈
        finiteAffineCommonZeroLocus sourceEquations)
    (hcut₁ : ∀ z ∈ S, eval
      (fun i => (progressionHomogeneousPoint u m z i : ℚ)) (record z).1 = 0)
    (hcut₂ : ∀ z ∈ S, eval
      (fun i => (progressionHomogeneousPoint u m z i : ℚ)) (record z).2 = 0)
    (hchanged : ∀ z ∈ S,
      selectedFiniteEquationComponent (qbarSurfaceCutEquationFamily sourceEquations (record z).1)
        (fun i => (progressionHomogeneousPoint u m z i : Qbar)) ≠
      selectedFiniteEquationComponent (qbarSurfaceCutEquationFamily sourceEquations (record z).2)
        (fun i => (progressionHomogeneousPoint u m z i : Qbar))) :
    S.card ≤ records.card * ((d * e₁) * (d * e₂)) := by
  classical
  let E := qbarSurfaceEquationFamily sourceEquations
  let pairMap := fun R : MvPolynomial (Fin (N + 1)) ℚ × MvPolynomial (Fin (N + 1)) ℚ =>
    (MvPolynomial.map (algebraMap ℚ Qbar) R.1, MvPolynomial.map (algebraMap ℚ Qbar) R.2)
  have hprimeE : (finiteEquationIdeal E).IsPrime := by
    rw [finiteEquationIdeal_qbarSurfaceEquationFamily]
    exact hgeometricPrime
  have hhomE : (finiteEquationIdeal E).IsHomogeneous
      (homogeneousSubmodule (Fin (N + 1)) Qbar) := by
    rw [finiteEquationIdeal_qbarSurfaceEquationFamily]
    exact isHomogeneous_map_mvPolynomialMap (algebraMap ℚ Qbar) _ hhom
  have hdegreeE : HasProjectiveDimensionDegree (finiteEquationIdeal E) 2 d := by
    rw [finiteEquationIdeal_qbarSurfaceEquationFamily]
    exact qbarHasProjectiveDimensionDegree_of_rational _ hdegree hgeometricPrime
  have hformsE (R) (hR : R ∈ records.image pairMap) :
      R.1.IsHomogeneous e₁ ∧ R.1 ∉ finiteEquationIdeal E ∧
      R.2.IsHomogeneous e₂ ∧ R.2 ∉ finiteEquationIdeal E := by
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hR
    obtain ⟨hh₁, hn₁, hh₂, hn₂⟩ := hforms T hT
    refine ⟨hh₁.map _, ?_, hh₂.map _, ?_⟩ <;>
      rw [finiteEquationIdeal_qbarSurfaceEquationFamily]
    · exact qbarMap_not_mem_extendedIdeal_of_not_mem _ _ hn₁
    · exact qbarMap_not_mem_extendedIdeal_of_not_mem _ _ hn₂
  have hsourceE (z) (hz : z ∈ S) :
      (fun i => (progressionHomogeneousPoint u m z i : Qbar)) ∈
        finiteAffineCommonZeroLocus E := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := (mem_qbarSurfaceEquationFamily sourceEquations f).mp hf
    rw [eval_qbarMap_progression, hsource z hz g hg, map_zero]
  have hcount := card_geometricSurfaceProgression_changed_cutPairRecords_le hm E
    hprimeE hhomE hdegreeE (records.image pairMap) (fun z => pairMap (record z)) hformsE
    u S (fun z hz => Finset.mem_image.mpr ⟨record z, hrecord z hz, rfl⟩) hsourceE
    (by
      intro z hz
      change eval _ (MvPolynomial.map (algebraMap ℚ Qbar) (record z).1) = 0
      rw [eval_qbarMap_progression, hcut₁ z hz, map_zero])
    (by
      intro z hz
      change eval _ (MvPolynomial.map (algebraMap ℚ Qbar) (record z).2) = 0
      rw [eval_qbarMap_progression, hcut₂ z hz, map_zero])
    hchanged
  exact hcount.trans (Nat.mul_le_mul_right _ Finset.card_image_le)

end

end TranslatedDepthSeven
