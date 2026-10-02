import TranslatedDepthSeven.DepthSevenRankSevenPacketAssembly
import TranslatedDepthSeven.PrimeProjectiveSaturation
import TranslatedDepthSeven.SalbergerAffinePacketMembership
import TranslatedDepthSeven.TranslatedProjectiveConeJoin

/-!
# Actual projective surface components before the join projection

An occupied rank-seven packet supplies four homogeneous equations in the
projective closure of its normalized affine coordinates.  This file writes
the complete rational equation ideal in standard `Fin 14` coordinates: the
translated projective cone equations together with those four rows.  It
proves that every packet point `(1,z)` vanishes on that ideal and lies on an
actual rational minimal-prime component.  Such a component is automatically
homogeneous and prime, avoids the irrelevant ideal, and meets the standard
affine chart.  Thus only its Hilbert dimension and degree remain to qualify
it for the Salberger terminal theorem.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000

/-- Rename the translated-cone equations from `Option (Fin 13)` to
Salberger's standard homogeneous coordinates `Fin 14`, and adjoin the four
source-section row equations. -/
def rankSevenSourceSectionEquationFinset
    (x₀ : IntVector 13) (m : ℕ) (hm : 0 < m)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (A : Matrix (Fin 4) (Fin 14) ℚ) :
    Finset (MvPolynomial (Fin 14) ℚ) := by
  classical
  let hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  exact
    (translatedProjectiveConeLiftEquationFamily
      (fun i ↦ (x₀ i : ℚ)) (m : ℚ) hmQ equations).image
        (MvPolynomial.rename (finSuccEquiv 13).symm) ∪
      rationalMatrixRowLinearEquationFamily A

/-- The literal generated ideal of the normalized source section. -/
def rankSevenSourceSectionIdeal
    (x₀ : IntVector 13) (m : ℕ) (hm : 0 < m)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (A : Matrix (Fin 4) (Fin 14) ℚ) :
    Ideal (MvPolynomial (Fin 14) ℚ) :=
  finiteEquationIdeal
    (rankSevenSourceSectionEquationFinset x₀ m hm equations A)

/-- Every displayed source-section equation is homogeneous when every
original equation is homogeneous. -/
theorem rankSevenSourceSectionEquationFinset_each_isHomogeneous
    (x₀ : IntVector 13) {m : ℕ} (hm : 0 < m)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (A : Matrix (Fin 4) (Fin 14) ℚ)
    {g : MvPolynomial (Fin 14) ℚ}
    (hg : g ∈ rankSevenSourceSectionEquationFinset x₀ m hm equations A) :
    ∃ e : ℕ, g.IsHomogeneous e := by
  classical
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  let degree : MvPolynomial (Fin 13) ℤ → ℕ := fun f ↦
    if hf : f ∈ equations then Classical.choose (hhomogeneous f hf) else 0
  have hdegree : ∀ f ∈ equations, f.IsHomogeneous (degree f) := by
    intro f hf
    simp only [degree, dif_pos hf]
    exact Classical.choose_spec (hhomogeneous f hf)
  rw [rankSevenSourceSectionEquationFinset] at hg
  rcases Finset.mem_union.mp hg with hg | hg
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hg
    have hlift : ∀ f ∈ projectiveConeLiftEquationFamily equations,
        ∃ e : ℕ, f.IsHomogeneous e := by
      intro f hf
      obtain ⟨f₀, _hf₀, _heq, he⟩ :=
        projectiveConeLiftEquationFamily_each_isHomogeneous
          equations degree hdegree hf
      exact ⟨degree f₀, he⟩
    obtain ⟨e, he⟩ :=
      finiteFamilyHomogeneousAffineChange_each_isHomogeneous
        (fun i ↦ (x₀ i : ℚ)) (m : ℚ) hmQ
        (projectiveConeLiftEquationFamily equations) hlift hq
    exact ⟨e, he.rename_isHomogeneous⟩
  · obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hg
    exact ⟨1, rationalMatrixRowLinearPolynomial_isHomogeneous A i⟩

/-- The complete source-section ideal is homogeneous. -/
theorem rankSevenSourceSectionIdeal_isHomogeneous
    (x₀ : IntVector 13) {m : ℕ} (hm : 0 < m)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (A : Matrix (Fin 4) (Fin 14) ℚ) :
    (rankSevenSourceSectionIdeal x₀ m hm equations A).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 14) ℚ) := by
  apply Ideal.homogeneous_span
  intro g hg
  exact rankSevenSourceSectionEquationFinset_each_isHomogeneous
    x₀ hm equations hhomogeneous A hg

/-- Every actual packet point `(1,z)` vanishes on the complete rational
source-section ideal. -/
theorem integralAffineChartVector_mem_rankSevenSourceSectionIdeal
    (x₀ : IntVector 13) {m : ℕ} (hm : 0 < m)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (A : Matrix (Fin 4) (Fin 14) ℚ)
    (z : IntVector 13)
    (hzero : IntegralCommonZero equations (integralAffineMap x₀ z m))
    (hA : Matrix.mulVec A (rationalHomogeneousAffinePoint z) = 0) :
    ∀ g ∈ rankSevenSourceSectionIdeal x₀ m hm equations A,
      MvPolynomial.eval
        (fun i ↦ (integralAffineChartVector z i : ℚ)) g = 0 := by
  classical
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  let zQ : Fin 13 → ℚ := fun i ↦ (z i : ℚ)
  let yQ : Fin 13 → ℚ := fun i ↦ (x₀ i : ℚ)
  let degree : MvPolynomial (Fin 13) ℤ → ℕ := fun f ↦
    if hf : f ∈ equations then Classical.choose (hhomogeneous f hf) else 0
  have hdegree : ∀ f ∈ equations, f.IsHomogeneous (degree f) := by
    intro f hf
    simp only [degree, dif_pos hf]
    exact Classical.choose_spec (hhomogeneous f hf)
  have hlift : ∀ f ∈ projectiveConeLiftEquationFamily equations,
      ∃ e : ℕ, f.IsHomogeneous e := by
    intro f hf
    obtain ⟨f₀, _hf₀, _heq, he⟩ :=
      projectiveConeLiftEquationFamily_each_isHomogeneous
        equations degree hdegree hf
    exact ⟨degree f₀, he⟩
  have hcone : affineChartPoint zQ ∈
      finiteProjectiveCommonZeroLocus
        (translatedProjectiveConeLiftEquationFamily yQ (m : ℚ) hmQ
          equations) := by
    apply (projectiveAffineMap_mem_finiteProjectiveCommonZeroLocus_iff
      yQ (m : ℚ) hmQ (projectiveConeLiftEquationFamily equations)
      hlift
      (affineChartPoint zQ)).mp ?_
    rw [projectiveAffineMap_affineChartPoint]
    rw [finiteProjectiveCommonZeroLocus_projectiveConeLiftEquationFamily
      equations degree hdegree]
    unfold affineChartPoint
    apply (mk_mem_projectiveConeOverIntegralEquations_iff
      equations degree hdegree _ _).mpr
    intro f hf
    have hpoint : (fun i : Fin 13 ↦
        affineChartVector (fun i ↦ yQ i + (m : ℚ) * zQ i) (some i)) =
        fun i ↦ (integralAffineMap x₀ z m i : ℚ) := by
      funext i
      simp [affineChartVector, yQ, zQ, integralAffineMap]
    rw [hpoint, eval_map_intCast, hzero f hf, Int.cast_zero]
  change (fun i ↦ (integralAffineChartVector z i : ℚ)) ∈
    affineIdealZeroLocus (rankSevenSourceSectionIdeal x₀ m hm equations A)
  rw [rankSevenSourceSectionIdeal, affineIdealZeroLocus_finiteEquationIdeal]
  intro g hg
  rw [rankSevenSourceSectionEquationFinset] at hg
  rcases Finset.mem_union.mp hg with hg | hg
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨e, he⟩ :=
      finiteFamilyHomogeneousAffineChange_each_isHomogeneous
        yQ (m : ℚ) hmQ (projectiveConeLiftEquationFamily equations)
        hlift hq
    rw [MvPolynomial.eval_rename]
    have hqzero := hcone q hq
    unfold affineChartPoint at hqzero
    rw [mk_mem_homogeneousProjectiveHypersurface_iff q e he
      (affineChartVector zQ) (affineChartVector_ne_zero zQ)] at hqzero
    have hpoint :
        ((fun i ↦ (integralAffineChartVector z i : ℚ)) ∘
          (finSuccEquiv 13).symm) = affineChartVector zQ := by
      funext j
      cases j <;> simp [integralAffineChartVector,
        affineChartVector, zQ]
    rw [hpoint]
    simpa [MvPolynomial.aeval_def, MvPolynomial.eval₂_id] using hqzero
  · obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hg
    rw [eval_rationalMatrixRowLinearPolynomial]
    have hi := congrFun hA i
    simpa [integralAffineChartVector, rationalHomogeneousAffinePoint] using hi

/-- Every packet point lies on an actual rational projective component of
the source section.  The component already has all Salberger qualification
properties except an exact projective Hilbert dimension--degree statement. -/
theorem exists_rankSevenSourceSectionComponent_through_packetPoint
    (x₀ : IntVector 13) {m : ℕ} (hm : 0 < m)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (A : Matrix (Fin 4) (Fin 14) ℚ)
    (z : IntVector 13)
    (hzero : IntegralCommonZero equations (integralAffineMap x₀ z m))
    (hA : Matrix.mulVec A (rationalHomogeneousAffinePoint z) = 0) :
    ∃ I ∈ finiteMinimalPrimes
        (rankSevenSourceSectionIdeal x₀ m hm equations A),
      I.IsPrime ∧
      I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 14) ℚ) ∧
      MvPolynomial.X (0 : Fin 14) ∉ I ∧
      ¬ (Published.projectiveIrrelevantIdeal ℚ 13 ≤ I) ∧
      ∀ f ∈ I, MvPolynomial.eval
        (fun i ↦ (integralAffineChartVector z i : ℚ)) f = 0 := by
  let T : Ideal (MvPolynomial (Fin 14) ℚ) :=
    RingHom.ker (MvPolynomial.eval
      (fun i ↦ (integralAffineChartVector z i : ℚ)))
  letI : T.IsPrime := RingHom.ker_isPrime _
  have hJT : rankSevenSourceSectionIdeal x₀ m hm equations A ≤ T :=
    integralAffineChartVector_mem_rankSevenSourceSectionIdeal
      x₀ hm equations hhomogeneous A z hzero hA
  obtain ⟨I, hI, hIT⟩ := exists_finiteMinimalPrime_le hJT
  have hIprime := isPrime_of_mem_finiteMinimalPrimes hI
  have hIhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 14) ℚ) :=
    isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous
      (rankSevenSourceSectionIdeal_isHomogeneous
        x₀ hm equations hhomogeneous A)
      ((mem_finiteMinimalPrimes_iff _ _).mp hI)
  have hXzero : MvPolynomial.X (0 : Fin 14) ∉ I := by
    intro hX
    have := RingHom.mem_ker.mp (hIT hX)
    simp [integralAffineChartVector] at this
  have hirrelevant : ¬ Published.projectiveIrrelevantIdeal ℚ 13 ≤ I := by
    intro hle
    exact hXzero (hle (Ideal.subset_span ⟨0, rfl⟩))
  exact ⟨I, hI, hIprime, hIhomogeneous, hXzero, hirrelevant,
    fun f hf ↦ RingHom.mem_ker.mp (hIT hf)⟩

end

end TranslatedDepthSeven
