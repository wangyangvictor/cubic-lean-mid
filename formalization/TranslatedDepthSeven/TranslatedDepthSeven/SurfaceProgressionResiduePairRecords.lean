import TranslatedDepthSeven.RationalSurfaceGeometricResidualCount
import TranslatedDepthSeven.HypersurfaceProgressionOccupiedResidues
import TranslatedDepthSeven.RankSevenOccupiedResidueBound

/-!
# Actual auxiliary-pair records over occupied least-common-multiple residues

One auxiliary at each endpoint is determined by the displacement residue at
that endpoint. The set of pairs actually occurring is therefore the image of
the occupied residues modulo `lcm(q,r)` under the existing reduction maps.
This retains compatibility between the two residues; their moduli need not
be coprime. The existing literal progression zero-set and squarefree CRT
estimates then give surface-sized record bounds, including highly composite
squarefree moduli.
-/

namespace TranslatedDepthSeven

noncomputable section
open MvPolynomial Published
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 300000

/-- The pairs that actually occur, after applying the two residue-dependent
choices to the same integral point. -/
def residueDeterminedPairRecords {N q r : ℕ} {α β : Type*}
    (S : Finset (Fin N → ℤ))
    (left : (Fin N → ZMod q) → α) (right : (Fin N → ZMod r) → β) :
    Finset (α × β) := by
  classical
  exact S.image fun z =>
    (left (integralResidueVector z), right (integralResidueVector z))

@[simp] theorem mem_residueDeterminedPairRecords
    {N q r : ℕ} {α β : Type*} (S : Finset (Fin N → ℤ))
    (left : (Fin N → ZMod q) → α) (right : (Fin N → ZMod r) → β) (R : α × β) :
    R ∈ residueDeterminedPairRecords S left right ↔
      ∃ z ∈ S, (left (integralResidueVector z), right (integralResidueVector z)) = R := by
  classical
  exact Finset.mem_image

/-- The exact record set is the image of occupied lcm residues. This uses
the already proved reduction identity and does not require `q` and `r` to
be coprime or prime. -/
theorem residueDeterminedPairRecords_eq_image_occupied_lcm
    {N q r : ℕ} {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset (Fin N → ℤ))
    (left : (Fin N → ZMod q) → α) (right : (Fin N → ZMod r) → β) :
    residueDeterminedPairRecords S left right =
      (occupiedIntegralResidues (Nat.lcm q r) S).image (fun ρ =>
        (left (reduceResidueVector (Nat.dvd_lcm_left q r) ρ),
          right (reduceResidueVector (Nat.dvd_lcm_right q r) ρ))) := by
  classical
  ext R
  constructor
  · intro hR
    obtain ⟨z, hz, rfl⟩ := (mem_residueDeterminedPairRecords S left right R).mp hR
    apply Finset.mem_image.mpr
    refine ⟨integralResidueVector z, mem_occupiedIntegralResidues_iff.mpr ⟨z, hz, rfl⟩, ?_⟩
    simp only [reduceResidueVector_integralResidueVector]
  · intro hR
    obtain ⟨ρ, hρ, heq⟩ := Finset.mem_image.mp hR
    obtain ⟨z, hz, hres⟩ := mem_occupiedIntegralResidues_iff.mp hρ
    have hres' : (integralResidueVector z : Fin N → ZMod (Nat.lcm q r)) = ρ := hres
    rw [← hres'] at heq
    apply (mem_residueDeterminedPairRecords S left right R).mpr
    exact ⟨z, hz, by simpa only [reduceResidueVector_integralResidueVector] using heq⟩

theorem card_residueDeterminedPairRecords_le_occupied_lcm
    {N q r : ℕ} {α β : Type*} (S : Finset (Fin N → ℤ))
    (left : (Fin N → ZMod q) → α) (right : (Fin N → ZMod r) → β) :
    (residueDeterminedPairRecords S left right).card ≤
      (occupiedIntegralResidues (Nat.lcm q r) S).card := by
  classical
  rw [residueDeterminedPairRecords_eq_image_occupied_lcm]
  exact Finset.card_image_le

/-- A literal modular point count bounds the actual records. The original
equation is evaluated at `(1,u+m*z)`; injectivity of the progression modulo
the whole composite lcm follows from its two explicit coprimality hypotheses. -/
theorem card_residueDeterminedPairRecords_le_hypersurfaceReduction
    {q r m : ℕ} {α β : Type*}
    (F : MvPolynomial (Fin 4) ℤ) (hq : q ≠ 0) (hr : r ≠ 0)
    (hqm : Nat.Coprime q m) (hrm : Nat.Coprime r m)
    (u : Fin 3 → ℤ) (S : Finset (Fin 3 → ℤ))
    (left : (Fin 3 → ZMod q) → α) (right : (Fin 3 → ZMod r) → β)
    (hzero : ∀ z ∈ S, eval (progressionHomogeneousPoint u m z) F = 0) :
    (residueDeterminedPairRecords S left right).card ≤
      (integerPolynomialZeroSet (Nat.lcm q r) 3 (Nat.lcm_ne_zero hq hr)
        {surfaceHypersurfaceFirstChartDehomogenize F}).card := by
  have hLm : Nat.Coprime (Nat.lcm q r) m :=
    Nat.Coprime.of_dvd_left (Nat.lcm_dvd_mul q r) (hqm.mul_left hrm)
  have hcount := card_occupiedIntegralResidues_le_polynomialZeroSet_of_progression
    (surfaceHypersurfaceFirstChartDehomogenize F) (Nat.lcm_ne_zero hq hr) hLm u S
    (fun z hz => by rw [surfaceHypersurfaceFirstChart_eval]; exact hzero z hz)
  exact (card_residueDeterminedPairRecords_le_occupied_lcm S left right).trans hcount

/-- The existing squarefree CRT estimate gives the exact degree factor and
the square of the lcm, including shared prime factors and arbitrarily many
distinct prime factors. No bound on record cardinality is assumed. -/
theorem card_residueDeterminedPairRecords_le_squarefree_surface
    {q r m : ℕ} {α β : Type*}
    (F : MvPolynomial (Fin 4) ℤ) (hq : Squarefree q) (hr : Squarefree r)
    (hqm : Nat.Coprime q m) (hrm : Nat.Coprime r m)
    (u : Fin 3 → ℤ) (S : Finset (Fin 3 → ℤ))
    (left : (Fin 3 → ZMod q) → α) (right : (Fin 3 → ZMod r) → β)
    (hzero : ∀ z ∈ S, eval (progressionHomogeneousPoint u m z) F = 0)
    (hsmoothq : ∀ z ∈ S, ∀ p, p.Prime → p ∣ q → ∃ v,
      (eval (fun i => u i + (m : ℤ) * z i)
        (pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0)
    (hsmoothr : ∀ z ∈ S, ∀ p, p.Prime → p ∣ r → ∃ v,
      (eval (fun i => u i + (m : ℤ) * z i)
        (pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0) :
    (residueDeterminedPairRecords S left right).card ≤
      (surfaceHypersurfaceFirstChartDehomogenize F).totalDegree ^
          (Nat.lcm q r).primeFactors.card * (Nat.lcm q r) ^ 2 := by
  have hLm : Nat.Coprime (Nat.lcm q r) m :=
    Nat.Coprime.of_dvd_left (Nat.lcm_dvd_mul q r) (hqm.mul_left hrm)
  have hcount := card_occupiedHypersurfaceProgressionResidues_le_squarefree F
    (squarefree_lcm_of_squarefree hq hr) hLm u S hzero (by
      intro z hz p hp hpL
      rcases hp.dvd_or_dvd_of_dvd_lcm hpL with hpq | hpr
      · exact hsmoothq z hz p hp hpq
      · exact hsmoothr z hz p hp hpr)
  exact (card_residueDeterminedPairRecords_le_occupied_lcm S left right).trans hcount

/-- The actual rational auxiliary records connect the geometric residual
bound to the occupied lcm residues. Only values at occupied residues need be
proper homogeneous forms. The auxiliary forms and their two components are
selected from the displayed residue data. -/
theorem card_rationalSurfaceProgression_changed_residueAuxiliaries_le_occupied
    {d e₁ e₂ q r m : ℕ} (hm : 0 < m)
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    (hgeometricPrime : ((finiteEquationIdeal sourceEquations).map
      (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime)
    (hhom : (finiteEquationIdeal sourceEquations).IsHomogeneous
      (homogeneousSubmodule (Fin 4) ℚ))
    (hdegree : HasProjectiveDimensionDegree (finiteEquationIdeal sourceEquations) 2 d)
    (u : Fin 3 → ℤ) (S : Finset (Fin 3 → ℤ))
    (left : (Fin 3 → ZMod q) → MvPolynomial (Fin 4) ℚ)
    (right : (Fin 3 → ZMod r) → MvPolynomial (Fin 4) ℚ)
    (hleft : ∀ ρ ∈ occupiedIntegralResidues q S,
      (left ρ).IsHomogeneous e₁ ∧ left ρ ∉ finiteEquationIdeal sourceEquations)
    (hright : ∀ ρ ∈ occupiedIntegralResidues r S,
      (right ρ).IsHomogeneous e₂ ∧ right ρ ∉ finiteEquationIdeal sourceEquations)
    (hsource : ∀ z ∈ S,
      (fun i => (progressionHomogeneousPoint u m z i : ℚ)) ∈
        finiteAffineCommonZeroLocus sourceEquations)
    (hcut₁ : ∀ z ∈ S, eval (fun i => (progressionHomogeneousPoint u m z i : ℚ))
      (left (integralResidueVector z)) = 0)
    (hcut₂ : ∀ z ∈ S, eval (fun i => (progressionHomogeneousPoint u m z i : ℚ))
      (right (integralResidueVector z)) = 0)
    (hchanged : ∀ z ∈ S,
      selectedFiniteEquationComponent
        (qbarSurfaceCutEquationFamily sourceEquations (left (integralResidueVector z)))
        (fun i => (progressionHomogeneousPoint u m z i : Qbar)) ≠
      selectedFiniteEquationComponent
        (qbarSurfaceCutEquationFamily sourceEquations (right (integralResidueVector z)))
        (fun i => (progressionHomogeneousPoint u m z i : Qbar))) :
    S.card ≤ (occupiedIntegralResidues (Nat.lcm q r) S).card * ((d * e₁) * (d * e₂)) := by
  let records := residueDeterminedPairRecords S left right
  let record := fun z : Fin 3 → ℤ =>
    (left (integralResidueVector z), right (integralResidueVector z))
  have hforms (R) (hR : R ∈ records) :
      R.1.IsHomogeneous e₁ ∧ R.1 ∉ finiteEquationIdeal sourceEquations ∧
      R.2.IsHomogeneous e₂ ∧ R.2 ∉ finiteEquationIdeal sourceEquations := by
    obtain ⟨z, hz, rfl⟩ := (mem_residueDeterminedPairRecords S left right R).mp hR
    have hL := hleft _ (mem_occupiedIntegralResidues_iff.mpr ⟨z, hz, rfl⟩)
    have hR := hright _ (mem_occupiedIntegralResidues_iff.mpr ⟨z, hz, rfl⟩)
    exact ⟨hL.1, hL.2, hR.1, hR.2⟩
  have hcount := card_rationalSurfaceProgression_changed_geometricCutPairRecords_le hm
    sourceEquations hgeometricPrime hhom hdegree records record hforms u S
    (fun z hz => (mem_residueDeterminedPairRecords S left right _).mpr ⟨z, hz, rfl⟩)
    hsource hcut₁ hcut₂ hchanged
  exact hcount.trans (Nat.mul_le_mul_right _
    (card_residueDeterminedPairRecords_le_occupied_lcm S left right))

/-- Literal modular point-count version of the geometric residual bound.
The same original integral equation is retained through the progression
map and the lcm modulus. No record-count hypothesis is supplied. -/
theorem card_rationalSurfaceProgression_changed_residueAuxiliaries_le_reduction
    {d e₁ e₂ q r m : ℕ} (hm : 0 < m)
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    (hgeometricPrime : ((finiteEquationIdeal sourceEquations).map
      (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime)
    (hhom : (finiteEquationIdeal sourceEquations).IsHomogeneous
      (homogeneousSubmodule (Fin 4) ℚ))
    (hdegree : HasProjectiveDimensionDegree (finiteEquationIdeal sourceEquations) 2 d)
    (F : MvPolynomial (Fin 4) ℤ) (hq : q ≠ 0) (hr : r ≠ 0)
    (hqm : Nat.Coprime q m) (hrm : Nat.Coprime r m)
    (u : Fin 3 → ℤ) (S : Finset (Fin 3 → ℤ))
    (left : (Fin 3 → ZMod q) → MvPolynomial (Fin 4) ℚ)
    (right : (Fin 3 → ZMod r) → MvPolynomial (Fin 4) ℚ)
    (hleft : ∀ ρ ∈ occupiedIntegralResidues q S,
      (left ρ).IsHomogeneous e₁ ∧ left ρ ∉ finiteEquationIdeal sourceEquations)
    (hright : ∀ ρ ∈ occupiedIntegralResidues r S,
      (right ρ).IsHomogeneous e₂ ∧ right ρ ∉ finiteEquationIdeal sourceEquations)
    (hsource : ∀ z ∈ S,
      (fun i => (progressionHomogeneousPoint u m z i : ℚ)) ∈
        finiteAffineCommonZeroLocus sourceEquations)
    (hzero : ∀ z ∈ S, eval (progressionHomogeneousPoint u m z) F = 0)
    (hcut₁ : ∀ z ∈ S, eval (fun i => (progressionHomogeneousPoint u m z i : ℚ))
      (left (integralResidueVector z)) = 0)
    (hcut₂ : ∀ z ∈ S, eval (fun i => (progressionHomogeneousPoint u m z i : ℚ))
      (right (integralResidueVector z)) = 0)
    (hchanged : ∀ z ∈ S,
      selectedFiniteEquationComponent
        (qbarSurfaceCutEquationFamily sourceEquations (left (integralResidueVector z)))
        (fun i => (progressionHomogeneousPoint u m z i : Qbar)) ≠
      selectedFiniteEquationComponent
        (qbarSurfaceCutEquationFamily sourceEquations (right (integralResidueVector z)))
        (fun i => (progressionHomogeneousPoint u m z i : Qbar))) :
    S.card ≤ (integerPolynomialZeroSet (Nat.lcm q r) 3 (Nat.lcm_ne_zero hq hr)
      {surfaceHypersurfaceFirstChartDehomogenize F}).card * ((d * e₁) * (d * e₂)) := by
  have hcount := card_rationalSurfaceProgression_changed_residueAuxiliaries_le_occupied hm
    sourceEquations hgeometricPrime hhom hdegree u S left right hleft hright
    hsource hcut₁ hcut₂ hchanged
  have hLm : Nat.Coprime (Nat.lcm q r) m :=
    Nat.Coprime.of_dvd_left (Nat.lcm_dvd_mul q r) (hqm.mul_left hrm)
  have hresidue := card_occupiedIntegralResidues_le_polynomialZeroSet_of_progression
    (surfaceHypersurfaceFirstChartDehomogenize F) (Nat.lcm_ne_zero hq hr) hLm u S
    (fun z hz => by rw [surfaceHypersurfaceFirstChart_eval]; exact hzero z hz)
  exact hcount.trans (Nat.mul_le_mul_right _ hresidue)

/-- The complete surface residual bound with the internally proved
squarefree CRT count. The only loss per prime factor is the explicitly
displayed degree of the original first-chart equation. -/
theorem card_rationalSurfaceProgression_changed_residueAuxiliaries_le_squarefree
    {d e₁ e₂ q r m : ℕ} (hm : 0 < m)
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    (hgeometricPrime : ((finiteEquationIdeal sourceEquations).map
      (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime)
    (hhom : (finiteEquationIdeal sourceEquations).IsHomogeneous
      (homogeneousSubmodule (Fin 4) ℚ))
    (hdegree : HasProjectiveDimensionDegree (finiteEquationIdeal sourceEquations) 2 d)
    (F : MvPolynomial (Fin 4) ℤ) (hq : Squarefree q) (hr : Squarefree r)
    (hqm : Nat.Coprime q m) (hrm : Nat.Coprime r m)
    (u : Fin 3 → ℤ) (S : Finset (Fin 3 → ℤ))
    (left : (Fin 3 → ZMod q) → MvPolynomial (Fin 4) ℚ)
    (right : (Fin 3 → ZMod r) → MvPolynomial (Fin 4) ℚ)
    (hleft : ∀ ρ ∈ occupiedIntegralResidues q S,
      (left ρ).IsHomogeneous e₁ ∧ left ρ ∉ finiteEquationIdeal sourceEquations)
    (hright : ∀ ρ ∈ occupiedIntegralResidues r S,
      (right ρ).IsHomogeneous e₂ ∧ right ρ ∉ finiteEquationIdeal sourceEquations)
    (hsource : ∀ z ∈ S,
      (fun i => (progressionHomogeneousPoint u m z i : ℚ)) ∈
        finiteAffineCommonZeroLocus sourceEquations)
    (hzero : ∀ z ∈ S, eval (progressionHomogeneousPoint u m z) F = 0)
    (hsmoothq : ∀ z ∈ S, ∀ p, p.Prime → p ∣ q → ∃ v,
      (eval (fun i => u i + (m : ℤ) * z i)
        (pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0)
    (hsmoothr : ∀ z ∈ S, ∀ p, p.Prime → p ∣ r → ∃ v,
      (eval (fun i => u i + (m : ℤ) * z i)
        (pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0)
    (hcut₁ : ∀ z ∈ S, eval (fun i => (progressionHomogeneousPoint u m z i : ℚ))
      (left (integralResidueVector z)) = 0)
    (hcut₂ : ∀ z ∈ S, eval (fun i => (progressionHomogeneousPoint u m z i : ℚ))
      (right (integralResidueVector z)) = 0)
    (hchanged : ∀ z ∈ S,
      selectedFiniteEquationComponent
        (qbarSurfaceCutEquationFamily sourceEquations (left (integralResidueVector z)))
        (fun i => (progressionHomogeneousPoint u m z i : Qbar)) ≠
      selectedFiniteEquationComponent
        (qbarSurfaceCutEquationFamily sourceEquations (right (integralResidueVector z)))
        (fun i => (progressionHomogeneousPoint u m z i : Qbar))) :
    S.card ≤ ((surfaceHypersurfaceFirstChartDehomogenize F).totalDegree ^
      (Nat.lcm q r).primeFactors.card * (Nat.lcm q r) ^ 2) * ((d * e₁) * (d * e₂)) := by
  have hcount := card_rationalSurfaceProgression_changed_residueAuxiliaries_le_occupied hm
    sourceEquations hgeometricPrime hhom hdegree u S left right hleft hright
    hsource hcut₁ hcut₂ hchanged
  have hLm : Nat.Coprime (Nat.lcm q r) m :=
    Nat.Coprime.of_dvd_left (Nat.lcm_dvd_mul q r) (hqm.mul_left hrm)
  have hresidue := card_occupiedHypersurfaceProgressionResidues_le_squarefree F
    (squarefree_lcm_of_squarefree hq hr) hLm u S hzero (by
      intro z hz p hp hpL
      rcases hp.dvd_or_dvd_of_dvd_lcm hpL with hpq | hpr
      · exact hsmoothq z hz p hp hpq
      · exact hsmoothr z hz p hp hpr)
  exact hcount.trans (Nat.mul_le_mul_right _ hresidue)

end
end TranslatedDepthSeven
