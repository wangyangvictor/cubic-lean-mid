import TranslatedDepthSeven.QbarDistinctCurveFirstChartBezoutInternal
import TranslatedDepthSeven.CertificateDeletedEquationComponentPartition
import TranslatedDepthSeven.ProgressionNormalizationBlockEvaluation
import TranslatedDepthSeven.ProperHomogeneousHypersurfaceCertificatesFieldInternal
import TranslatedDepthSeven.ProjectiveHilbertDegreeCertificationInternal

/-!
# Residual progression points where geometric curve labels change

The literal minimal-prime labels of two fixed equation families are used.
Every changed-label cell lies on two distinct projective curves, so the
internally proved first-chart Bezout theorem bounds it by the product of
their degrees.  Summing gives the product of the two component degree masses.
The result has arbitrary ambient dimension and arbitrary integral progression
center and positive modulus; it does not use the old rank-seven coordinates.

The component certificates below concern geometric prime ideals.  Producing
these certificates from a rational surface auxiliary family still requires
the rational-to-geometric component bridge; that bridge is not asserted here.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]

omit [IsAlgClosed K] in
/-- Positive progression scale makes the actual normalized homogeneous
coordinate vector injective, over any characteristic-zero field. -/
theorem geometricProgressionPoint_injective
    {N m : ℕ} (hm : 0 < m) (u : Fin N → ℤ) :
    Function.Injective (fun z : Fin N → ℤ =>
      fun i => (progressionHomogeneousPoint u m z i : K)) := by
  intro z w h
  funext i
  have hi := congrFun h i.succ
  simp only [progressionHomogeneousPoint, Fin.cases_succ] at hi
  have heq : u i + (m : ℤ) * z i = u i + (m : ℤ) * w i := by
    exact_mod_cast hi
  exact mul_left_cancel₀ (by exact_mod_cast hm.ne' : (m : ℤ) ≠ 0)
    (add_left_cancel heq)

/-- Two distinct actual geometric prime curves have at most the product
of their degrees many points in any integral progression, independently of
the box radius and of the progression center and positive modulus. -/
theorem card_geometricProgression_on_distinct_curves_le_degree_mul
    {N d e m : ℕ} (hm : 0 < m)
    (P Q : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hP : P.IsPrime) (hQ : Q.IsPrime)
    (hPhom : P.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K))
    (hQhom : Q.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K))
    (hPdegree : HasProjectiveDimensionDegree P 1 d)
    (hQdegree : HasProjectiveDimensionDegree Q 1 e)
    (hne : P ≠ Q) (u : Fin N → ℤ) (S : Finset (Fin N → ℤ))
    (hzero : ∀ z ∈ S,
      (fun i => (progressionHomogeneousPoint u m z i : K)) ∈
        affineIdealZeroLocus (P ⊔ Q)) :
    S.card ≤ d * e := by
  classical
  let J := ((P ⊔ Q) ⊔ Ideal.span
    ({X 0 - C 1} : Set (MvPolynomial (Fin (N + 1)) K))).radical
  let A := MvPolynomial (Fin (N + 1)) K ⧸ J
  let coord := fun z : Fin N → ℤ =>
    fun i => (progressionHomogeneousPoint u m z i : K)
  have hJzero (z : Fin N → ℤ) (hz : z ∈ S) :
      coord z ∈ affineIdealZeroLocus J := by
    have hker : (P ⊔ Q) ⊔ Ideal.span
        ({X 0 - C 1} : Set (MvPolynomial (Fin (N + 1)) K)) ≤
        RingHom.ker (MvPolynomial.eval (coord z)) := by
      apply sup_le
      · intro f hf
        exact hzero z hz f hf
      · apply Ideal.span_le.mpr
        intro f hf
        obtain rfl := Set.mem_singleton_iff.mp hf
        change eval (coord z) (X 0 - C 1) = 0
        simp [coord, progressionHomogeneousPoint]
    have hrad := (RingHom.ker_isPrime (MvPolynomial.eval (coord z))).radical_le_iff.mpr hker
    exact fun f hf => hrad hf
  obtain ⟨v, hv⟩ := exists_distinct_projectiveCurve_firstChart_spanningFamily
    P Q hP hQ hPhom hQhom hPdegree hQdegree hne
  let pointHom : {z // z ∈ S} → (A →ₐ[K] K) := fun z =>
    affineIdealPointToQuotientAlgHom J ⟨coord z.1, hJzero z.1 z.2⟩
  have hinjective : Function.Injective pointHom := by
    intro z w hzw
    apply Subtype.ext
    apply geometricProgressionPoint_injective (K := K) hm u
    have hp := (affineIdealZeroLocusEquivQuotientAlgHom J).injective hzw
    exact congrArg (fun x => x.1) hp
  letI : Module.Finite K A := Module.finite_def.mpr <|
    Submodule.fg_iff_exists_fin_generating_family.mpr ⟨d * e, v, hv⟩
  calc
    S.card = Nat.card {z // z ∈ S} := by simp
    _ ≤ Nat.card (A →ₐ[K] K) := Nat.card_le_card_of_injective pointHom hinjective
    _ ≤ Module.finrank K A := card_algHom_le_finrank K A K
    _ ≤ d * e := by simpa [A, J] using finrank_le_of_span_eq_top hv

/-- A fixed pair of unequal selected geometric curve labels is a residual
cell with the same exact degree-product bound.  The equations may depend on
the point: the selected component ideals themselves are fixed in the cell. -/
theorem card_geometricProgression_changed_component_cell_le
    {N d e m : ℕ} (hm : 0 < m)
    (equations₁ equations₂ : (Fin N → ℤ) →
      Finset (MvPolynomial (Fin (N + 1)) K))
    (P Q : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hP : P.IsPrime) (hQ : Q.IsPrime)
    (hPhom : P.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K))
    (hQhom : Q.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K))
    (hPdegree : HasProjectiveDimensionDegree P 1 d)
    (hQdegree : HasProjectiveDimensionDegree Q 1 e)
    (hne : P ≠ Q) (u : Fin N → ℤ) (S : Finset (Fin N → ℤ))
    (hlabel₁ : ∀ z ∈ S, selectedFiniteEquationComponent (equations₁ z)
      (fun i => (progressionHomogeneousPoint u m z i : K)) = some P)
    (hlabel₂ : ∀ z ∈ S, selectedFiniteEquationComponent (equations₂ z)
      (fun i => (progressionHomogeneousPoint u m z i : K)) = some Q) :
    S.card ≤ d * e := by
  apply card_geometricProgression_on_distinct_curves_le_degree_mul hm P Q
    hP hQ hPhom hQhom hPdegree hQdegree hne u S
  intro z hz
  exact mem_affineIdealZeroLocus_sup_of_two_selected_components
    (equations₁ z) (equations₂ z) _ (hlabel₁ z hz) (hlabel₂ z hz)

/-- Summing the actual unequal-component cells costs at most the product
of the two degree masses.  These are the literal finite minimal-prime lists,
not an assumed list of residual points. -/
theorem card_geometricProgression_changed_equationComponents_le
    {N m : ℕ} (hm : 0 < m)
    (equations₁ equations₂ : Finset (MvPolynomial (Fin (N + 1)) K))
    (degree₁ degree₂ : Ideal (MvPolynomial (Fin (N + 1)) K) → ℕ)
    (hcurve₁ : ∀ P ∈ finiteEquationMinimalPrimes equations₁,
      P.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K) ∧
        HasProjectiveDimensionDegree P 1 (degree₁ P))
    (hcurve₂ : ∀ Q ∈ finiteEquationMinimalPrimes equations₂,
      Q.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K) ∧
        HasProjectiveDimensionDegree Q 1 (degree₂ Q))
    (u : Fin N → ℤ) (S : Finset (Fin N → ℤ))
    (hzero₁ : ∀ z ∈ S,
      (fun i => (progressionHomogeneousPoint u m z i : K)) ∈
        finiteAffineCommonZeroLocus equations₁)
    (hzero₂ : ∀ z ∈ S,
      (fun i => (progressionHomogeneousPoint u m z i : K)) ∈
        finiteAffineCommonZeroLocus equations₂)
    (hchanged : ∀ z ∈ S,
      selectedFiniteEquationComponent equations₁
        (fun i => (progressionHomogeneousPoint u m z i : K)) ≠
      selectedFiniteEquationComponent equations₂
        (fun i => (progressionHomogeneousPoint u m z i : K))) :
    S.card ≤
      (∑ P ∈ finiteEquationMinimalPrimes equations₁, degree₁ P) *
      (∑ Q ∈ finiteEquationMinimalPrimes equations₂, degree₂ Q) := by
  classical
  let C₁ := finiteEquationMinimalPrimes equations₁
  let C₂ := finiteEquationMinimalPrimes equations₂
  let coord := fun z : Fin N → ℤ =>
    fun i => (progressionHomogeneousPoint u m z i : K)
  let cell := fun PQ : Ideal (MvPolynomial (Fin (N + 1)) K) ×
      Ideal (MvPolynomial (Fin (N + 1)) K) => S.filter fun z =>
    selectedFiniteEquationComponent equations₁ (coord z) = some PQ.1 ∧
    selectedFiniteEquationComponent equations₂ (coord z) = some PQ.2
  have hsub : S ⊆ (C₁ ×ˢ C₂).biUnion cell := by
    intro z hz
    have hnonempty₁ : selectedFiniteEquationComponent equations₁ (coord z) ≠ none := by
      intro h
      exact (selectedFiniteEquationComponent_eq_none_iff _ _).mp h (hzero₁ z hz)
    have hnonempty₂ : selectedFiniteEquationComponent equations₂ (coord z) ≠ none := by
      intro h
      exact (selectedFiniteEquationComponent_eq_none_iff _ _).mp h (hzero₂ z hz)
    obtain ⟨P, hP⟩ := Option.ne_none_iff_exists'.mp hnonempty₁
    obtain ⟨Q, hQ⟩ := Option.ne_none_iff_exists'.mp hnonempty₂
    apply Finset.mem_biUnion.mpr
    refine ⟨(P, Q), Finset.mem_product.mpr ?_, Finset.mem_filter.mpr ⟨hz, hP, hQ⟩⟩
    exact ⟨(selectedFiniteEquationComponent_spec _ _ hP).1,
      (selectedFiniteEquationComponent_spec _ _ hQ).1⟩
  have hcell (PQ) (hPQ : PQ ∈ C₁ ×ˢ C₂) :
      (cell PQ).card ≤ degree₁ PQ.1 * degree₂ PQ.2 := by
    obtain ⟨hP, hQ⟩ := Finset.mem_product.mp hPQ
    by_cases heq : PQ.1 = PQ.2
    · have hempty : cell PQ = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        obtain ⟨hzS, hzP, hzQ⟩ := Finset.mem_filter.mp hz
        exact hchanged z hzS (hzP.trans ((congrArg some heq).trans hzQ.symm))
      simp [hempty]
    · exact card_geometricProgression_changed_component_cell_le hm
        (fun _ => equations₁) (fun _ => equations₂) PQ.1 PQ.2
        (isPrime_of_mem_finiteMinimalPrimes hP) (isPrime_of_mem_finiteMinimalPrimes hQ)
        (hcurve₁ _ hP).1 (hcurve₂ _ hQ).1 (hcurve₁ _ hP).2 (hcurve₂ _ hQ).2
        heq u (cell PQ)
        (fun z hz => (Finset.mem_filter.mp hz).2.1)
        (fun z hz => (Finset.mem_filter.mp hz).2.2)
  calc
    S.card ≤ ((C₁ ×ˢ C₂).biUnion cell).card := Finset.card_le_card hsub
    _ ≤ ∑ PQ ∈ C₁ ×ˢ C₂, (cell PQ).card := Finset.card_biUnion_le
    _ ≤ ∑ PQ ∈ C₁ ×ˢ C₂, degree₁ PQ.1 * degree₂ PQ.2 := Finset.sum_le_sum hcell
    _ = (∑ P ∈ C₁, degree₁ P) * (∑ Q ∈ C₂, degree₂ Q) := by
      rw [Finset.sum_product]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]

/-- For two actual proper cuts of one geometric prime surface, the
component certificates and degree masses are constructed internally.  The
result counts exactly the points where the selected component changes;
points on a common persistent component are not claimed to be residual. -/
theorem card_geometricSurfaceProgression_changed_cuts_le
    {N d e₁ e₂ m : ℕ} (hm : 0 < m)
    (sourceEquations : Finset (MvPolynomial (Fin (N + 1)) K))
    (hprime : (finiteEquationIdeal sourceEquations).IsPrime)
    (hhom : (finiteEquationIdeal sourceEquations).IsHomogeneous
      (homogeneousSubmodule (Fin (N + 1)) K))
    (hdegree : HasProjectiveDimensionDegree (finiteEquationIdeal sourceEquations) 2 d)
    (G₁ G₂ : MvPolynomial (Fin (N + 1)) K)
    (hG₁hom : G₁.IsHomogeneous e₁) (hG₁not : G₁ ∉ finiteEquationIdeal sourceEquations)
    (hG₂hom : G₂.IsHomogeneous e₂) (hG₂not : G₂ ∉ finiteEquationIdeal sourceEquations)
    (u : Fin N → ℤ) (S : Finset (Fin N → ℤ))
    (hsource : ∀ z ∈ S,
      (fun i => (progressionHomogeneousPoint u m z i : K)) ∈
        finiteAffineCommonZeroLocus sourceEquations)
    (hcut₁ : ∀ z ∈ S, eval
      (fun i => (progressionHomogeneousPoint u m z i : K)) G₁ = 0)
    (hcut₂ : ∀ z ∈ S, eval
      (fun i => (progressionHomogeneousPoint u m z i : K)) G₂ = 0)
    (hchanged : ∀ z ∈ S,
      selectedFiniteEquationComponent (finiteEquationFamilyUnion sourceEquations {G₁})
        (fun i => (progressionHomogeneousPoint u m z i : K)) ≠
      selectedFiniteEquationComponent (finiteEquationFamilyUnion sourceEquations {G₂})
        (fun i => (progressionHomogeneousPoint u m z i : K))) :
    S.card ≤ (d * e₁) * (d * e₂) := by
  classical
  let I := finiteEquationIdeal sourceEquations
  let E₁ := finiteEquationFamilyUnion sourceEquations {G₁}
  let E₂ := finiteEquationFamilyUnion sourceEquations {G₂}
  have hid (G : MvPolynomial (Fin (N + 1)) K) :
      finiteEquationIdeal (finiteEquationFamilyUnion sourceEquations {G}) =
        I ⊔ Ideal.span ({G} : Set _) := by
    rw [finiteEquationIdeal_union]
    simp only [finiteEquationIdeal, Finset.coe_singleton, I]
  obtain ⟨degree₁, hdegree₁, hmass₁⟩ :=
    properHomogeneousHypersurface_componentDimensionDegreeMass_over_field
      (projectiveHilbertDegreeCertification_internal K) I G₁ hprime hhom hdegree hG₁hom hG₁not
  obtain ⟨degree₂, hdegree₂, hmass₂⟩ :=
    properHomogeneousHypersurface_componentDimensionDegreeMass_over_field
      (projectiveHilbertDegreeCertification_internal K) I G₂ hprime hhom hdegree hG₂hom hG₂not
  have hcutHom (G : MvPolynomial (Fin (N + 1)) K) (a : ℕ) (hG : G.IsHomogeneous a) :
      (I ⊔ Ideal.span ({G} : Set _)).IsHomogeneous
        (homogeneousSubmodule (Fin (N + 1)) K) := by
    apply hhom.sup
    apply Ideal.homogeneous_span
    intro f hf
    obtain rfl := Set.mem_singleton_iff.mp hf
    exact ⟨a, hG⟩
  have hcurve₁ (P) (hP : P ∈ finiteEquationMinimalPrimes E₁) :
      P.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K) ∧
        HasProjectiveDimensionDegree P 1 (degree₁ P) := by
    change P ∈ finiteMinimalPrimes (finiteEquationIdeal E₁) at hP
    rw [hid] at hP
    exact ⟨isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous
      (hcutHom G₁ e₁ hG₁hom) ((mem_finiteMinimalPrimes_iff _ _).mp hP), hdegree₁ P hP⟩
  have hcurve₂ (P) (hP : P ∈ finiteEquationMinimalPrimes E₂) :
      P.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K) ∧
        HasProjectiveDimensionDegree P 1 (degree₂ P) := by
    change P ∈ finiteMinimalPrimes (finiteEquationIdeal E₂) at hP
    rw [hid] at hP
    exact ⟨isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous
      (hcutHom G₂ e₂ hG₂hom) ((mem_finiteMinimalPrimes_iff _ _).mp hP), hdegree₂ P hP⟩
  have hzero₁ (z) (hz : z ∈ S) :
      (fun i => (progressionHomogeneousPoint u m z i : K)) ∈
        finiteAffineCommonZeroLocus E₁ := by
    rw [finiteAffineCommonZeroLocus_union]
    refine ⟨hsource z hz, ?_⟩
    intro f hf
    simpa only [Finset.mem_singleton.mp hf] using hcut₁ z hz
  have hzero₂ (z) (hz : z ∈ S) :
      (fun i => (progressionHomogeneousPoint u m z i : K)) ∈
        finiteAffineCommonZeroLocus E₂ := by
    rw [finiteAffineCommonZeroLocus_union]
    refine ⟨hsource z hz, ?_⟩
    intro f hf
    simpa only [Finset.mem_singleton.mp hf] using hcut₂ z hz
  have hcount := card_geometricProgression_changed_equationComponents_le hm E₁ E₂
    degree₁ degree₂ hcurve₁ hcurve₂ u S hzero₁ hzero₂ hchanged
  have hm₁ : (∑ P ∈ finiteEquationMinimalPrimes E₁, degree₁ P) ≤ d * e₁ := by
    simpa only [finiteEquationMinimalPrimes, E₁, hid] using hmass₁
  have hm₂ : (∑ P ∈ finiteEquationMinimalPrimes E₂, degree₂ P) ≤ d * e₂ := by
    simpa only [finiteEquationMinimalPrimes, E₂, hid] using hmass₂
  exact hcount.trans (Nat.mul_le_mul hm₁ hm₂)

/-- Residual points over a finite set of actual auxiliary-pair records.
Only occupied compatible pairs need be included, as in a common residue
class at the least common multiple of two adjacent reservoir moduli. -/
theorem card_geometricSurfaceProgression_changed_cutPairRecords_le
    {N d e₁ e₂ m : ℕ} (hm : 0 < m)
    (sourceEquations : Finset (MvPolynomial (Fin (N + 1)) K))
    (hprime : (finiteEquationIdeal sourceEquations).IsPrime)
    (hhom : (finiteEquationIdeal sourceEquations).IsHomogeneous
      (homogeneousSubmodule (Fin (N + 1)) K))
    (hdegree : HasProjectiveDimensionDegree (finiteEquationIdeal sourceEquations) 2 d)
    (records : Finset (MvPolynomial (Fin (N + 1)) K × MvPolynomial (Fin (N + 1)) K))
    (record : (Fin N → ℤ) →
      MvPolynomial (Fin (N + 1)) K × MvPolynomial (Fin (N + 1)) K)
    (hforms : ∀ R ∈ records,
      R.1.IsHomogeneous e₁ ∧ R.1 ∉ finiteEquationIdeal sourceEquations ∧
      R.2.IsHomogeneous e₂ ∧ R.2 ∉ finiteEquationIdeal sourceEquations)
    (u : Fin N → ℤ) (S : Finset (Fin N → ℤ))
    (hrecord : ∀ z ∈ S, record z ∈ records)
    (hsource : ∀ z ∈ S,
      (fun i => (progressionHomogeneousPoint u m z i : K)) ∈
        finiteAffineCommonZeroLocus sourceEquations)
    (hcut₁ : ∀ z ∈ S, eval
      (fun i => (progressionHomogeneousPoint u m z i : K)) (record z).1 = 0)
    (hcut₂ : ∀ z ∈ S, eval
      (fun i => (progressionHomogeneousPoint u m z i : K)) (record z).2 = 0)
    (hchanged : ∀ z ∈ S,
      selectedFiniteEquationComponent (finiteEquationFamilyUnion sourceEquations {(record z).1})
        (fun i => (progressionHomogeneousPoint u m z i : K)) ≠
      selectedFiniteEquationComponent (finiteEquationFamilyUnion sourceEquations {(record z).2})
        (fun i => (progressionHomogeneousPoint u m z i : K))) :
    S.card ≤ records.card * ((d * e₁) * (d * e₂)) := by
  classical
  let cell := fun R => S.filter fun z => record z = R
  have hsub : S ⊆ records.biUnion cell := by
    intro z hz
    exact Finset.mem_biUnion.mpr
      ⟨record z, hrecord z hz, Finset.mem_filter.mpr ⟨hz, rfl⟩⟩
  have hcell (R) (hR : R ∈ records) : (cell R).card ≤ (d * e₁) * (d * e₂) := by
    obtain ⟨hh₁, hn₁, hh₂, hn₂⟩ := hforms R hR
    apply card_geometricSurfaceProgression_changed_cuts_le hm sourceEquations
      hprime hhom hdegree R.1 R.2 hh₁ hn₁ hh₂ hn₂ u (cell R)
    · intro z hz
      exact hsource z (Finset.mem_filter.mp hz).1
    · intro z hz
      obtain ⟨hzS, heq⟩ := Finset.mem_filter.mp hz
      simpa only [heq] using hcut₁ z hzS
    · intro z hz
      obtain ⟨hzS, heq⟩ := Finset.mem_filter.mp hz
      simpa only [heq] using hcut₂ z hzS
    · intro z hz
      obtain ⟨hzS, heq⟩ := Finset.mem_filter.mp hz
      simpa only [heq] using hchanged z hzS
  calc
    S.card ≤ (records.biUnion cell).card := Finset.card_le_card hsub
    _ ≤ ∑ R ∈ records, (cell R).card := Finset.card_biUnion_le
    _ ≤ ∑ _R ∈ records, (d * e₁) * (d * e₂) := Finset.sum_le_sum hcell
    _ = records.card * ((d * e₁) * (d * e₂)) := by simp

end

end TranslatedDepthSeven
