import TranslatedDepthSeven.RankSevenStaticComponentPartition

/-!
# Static comparison of the actual rank-seven surface components

The selected component of a source section is retained as a label precisely
when its homogeneous Hilbert data have projective dimension two.  Thus
`none` is the literal node contribution (a non-surface selected component),
an edge has two distinct nonempty surface labels, and a persistent label is
one fixed projective surface component on every surviving modulus.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The selected source-section component, retained only when it has
projective dimension two. -/
def rankSevenStaticSurfaceLabel
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (z : IntVector 13) (q : ReservoirModulus P k) :
    Option (Ideal (MvPolynomial (Fin 14) ℚ)) :=
  match rankSevenStaticSelectedComponent
      p x₀ equations CF C denominator P k hP hlower z q with
  | none => none
  | some I =>
      if ∃ d : ℕ, HasProjectiveDimensionDegree I 2 d then some I else none

theorem rankSevenStaticSurfaceLabel_eq_some_iff
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (z : IntVector 13) (q : ReservoirModulus P k)
    (I : Ideal (MvPolynomial (Fin 14) ℚ)) :
    rankSevenStaticSurfaceLabel
        p x₀ equations CF C denominator P k hP hlower z q = some I ↔
      rankSevenStaticSelectedComponent
          p x₀ equations CF C denominator P k hP hlower z q = some I ∧
        ∃ d : ℕ, HasProjectiveDimensionDegree I 2 d := by
  unfold rankSevenStaticSurfaceLabel
  generalize hselected : rankSevenStaticSelectedComponent
    p x₀ equations CF C denominator P k hP hlower z q = o
  cases o with
  | none => simp
  | some J =>
      by_cases hJ : ∃ d : ℕ, HasProjectiveDimensionDegree J 2 d
      · simp only [hJ, ↓reduceIte]
        constructor
        · intro hsome
          have hJI := Option.some.inj hsome
          subst I
          exact ⟨rfl, hJ⟩
        · exact fun h ↦ h.1
      · simp only [hJ, ↓reduceIte]
        constructor
        · intro h
          exact Option.noConfusion h
        · rintro ⟨hsome, hI⟩
          have hJI := Option.some.inj hsome
          subst I
          exact (hJ hI).elim

theorem rankSevenStaticSurfaceLabel_eq_none_iff
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (z : IntVector 13) (q : ReservoirModulus P k) :
    rankSevenStaticSurfaceLabel
        p x₀ equations CF C denominator P k hP hlower z q = none ↔
      rankSevenStaticSelectedComponent
          p x₀ equations CF C denominator P k hP hlower z q = none ∨
        ∃ I : Ideal (MvPolynomial (Fin 14) ℚ),
          rankSevenStaticSelectedComponent
              p x₀ equations CF C denominator P k hP hlower z q = some I ∧
          ¬ ∃ d : ℕ, HasProjectiveDimensionDegree I 2 d := by
  unfold rankSevenStaticSurfaceLabel
  generalize hselected : rankSevenStaticSelectedComponent
    p x₀ equations CF C denominator P k hP hlower z q = o
  cases o with
  | none => simp
  | some I =>
      by_cases hI : ∃ d : ℕ, HasProjectiveDimensionDegree I 2 d
      · simp [hI]
      · simp only [hI, ↓reduceIte, Option.some_ne_none, false_or,
          true_iff]
        exact ⟨I, rfl, hI⟩

/-- A nonempty surface label is a uniquely displayed selected component
with projective dimension two and a positive projective degree. -/
theorem exists_surfaceComponent_of_rankSevenStaticSurfaceLabel_ne_none
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (z : IntVector 13) (q : ReservoirModulus P k)
    (hne : rankSevenStaticSurfaceLabel
      p x₀ equations CF C denominator P k hP hlower z q ≠ none) :
    ∃ I : Ideal (MvPolynomial (Fin 14) ℚ), ∃ d : ℕ,
      rankSevenStaticSurfaceLabel
          p x₀ equations CF C denominator P k hP hlower z q = some I ∧
      rankSevenStaticSelectedComponent
          p x₀ equations CF C denominator P k hP hlower z q = some I ∧
      HasProjectiveDimensionDegree I 2 d := by
  obtain ⟨I, hIlabel⟩ := Option.ne_none_iff_exists'.mp hne
  obtain ⟨hIselected, d, hId⟩ :=
    (rankSevenStaticSurfaceLabel_eq_some_iff
      p x₀ equations CF C denominator P k hP hlower z q I).mp hIlabel
  exact ⟨I, d, hIlabel, hIselected, hId⟩

/-- Across a nonempty unequal edge, the two labels are distinct actual
minimal-prime surface components, and the point lies on the zero locus of
their ideal supremum. -/
theorem exists_distinct_rankSevenSurfaceComponents_of_edge
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (z : IntVector 13) (q r : ReservoirModulus P k)
    (_hz : z ∈ depthSevenNormalizedJacobianChartCell
      p x₀ equations CF C)
    (_hqSurvives : survivesTwoCertificates q ((p.m : ℤ) * denominator)
      (MvPolynomial.eval (integralAffineMap x₀ z p.m) C.determinant))
    (_hrSurvives : survivesTwoCertificates r ((p.m : ℤ) * denominator)
      (MvPolynomial.eval (integralAffineMap x₀ z p.m) C.determinant))
    (_hqr : (modulusReservoirGraph P k hP).Adj q r)
    (hne : rankSevenStaticSurfaceLabel
        p x₀ equations CF C denominator P k hP hlower z q ≠
      rankSevenStaticSurfaceLabel
        p x₀ equations CF C denominator P k hP hlower z r)
    (hqne : rankSevenStaticSurfaceLabel
      p x₀ equations CF C denominator P k hP hlower z q ≠ none)
    (hrne : rankSevenStaticSurfaceLabel
      p x₀ equations CF C denominator P k hP hlower z r ≠ none) :
    ∃ Iq Ir : Ideal (MvPolynomial (Fin 14) ℚ), ∃ dq dr : ℕ,
      Iq ≠ Ir ∧
      rankSevenStaticSelectedComponent
          p x₀ equations CF C denominator P k hP hlower z q = some Iq ∧
      rankSevenStaticSelectedComponent
          p x₀ equations CF C denominator P k hP hlower z r = some Ir ∧
      HasProjectiveDimensionDegree Iq 2 dq ∧
      HasProjectiveDimensionDegree Ir 2 dr ∧
      (fun i ↦ (integralAffineChartVector z i : ℚ)) ∈
        affineIdealZeroLocus (Iq ⊔ Ir) := by
  obtain ⟨Iq, dq, hqLabel, hqSelected, hIq⟩ :=
    exists_surfaceComponent_of_rankSevenStaticSurfaceLabel_ne_none
      p x₀ equations CF C denominator P k hP hlower z q hqne
  obtain ⟨Ir, dr, hrLabel, hrSelected, hIr⟩ :=
    exists_surfaceComponent_of_rankSevenStaticSurfaceLabel_ne_none
      p x₀ equations CF C denominator P k hP hlower z r hrne
  have hdistinct : Iq ≠ Ir := by
    intro hEq
    apply hne
    rw [hqLabel, hrLabel, hEq]
  exact ⟨Iq, Ir, dq, dr, hdistinct, hqSelected, hrSelected,
    hIq, hIr,
    mem_affineIdealZeroLocus_sup_of_two_selected_components
      (rankSevenStaticSourceSectionEquations
        p x₀ equations CF C denominator P k hP hlower q z)
      (rankSevenStaticSourceSectionEquations
        p x₀ equations CF C denominator P k hP hlower r z)
      (fun i ↦ (integralAffineChartVector z i : ℚ))
      hqSelected hrSelected⟩

/-- Labels which actually occur on the certificate-deleted chart
reservoir. -/
def occurringRankSevenStaticSurfaceLabels
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1) :
    Finset (Option (Ideal (MvPolynomial (Fin 14) ℚ))) :=
  occurringCertificateDeletedLabels
    (depthSevenNormalizedJacobianChartCell p x₀ equations CF C)
    (fun _ ↦ (p.m : ℤ) * denominator)
    (fun z ↦ MvPolynomial.eval (integralAffineMap x₀ z p.m) C.determinant)
    (fun z q ↦ rankSevenStaticSurfaceLabel
      p x₀ equations CF C denominator P k hP hlower z q)

/-- Exact vertex--edge--persistent partition for the genuine surface labels
on one rank-seven chart.  Both endpoint labels in the edge term are required
to be nonempty. -/
theorem card_rankSevenChart_le_surfaceVertex_edge_persistent
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (H A : ℝ)
    (hsurvival : ∀ E₁ E₂ : ℤ, E₁ ≠ 0 → E₂ ≠ 0 →
      (E₁.natAbs : ℝ) ≤ H ^ A → (E₂.natAbs : ℝ) ≤ H ^ A →
      Nonempty (ReservoirModulus
        (certificateAllowedPrimesTwo P E₁ E₂) k) ∧
      (modulusReservoirGraph
        (certificateAllowedPrimesTwo P E₁ E₂) k
        (fun s hs ↦ hP s (Finset.mem_filter.mp hs).1)).Connected)
    (hfixedNe : (p.m : ℤ) * denominator ≠ 0)
    (hfixedSize : ((((p.m : ℤ) * denominator).natAbs : ℕ) : ℝ) ≤ H ^ A)
    (hdetNe : ∀ z ∈ depthSevenNormalizedJacobianChartCell
      p x₀ equations CF C,
      MvPolynomial.eval (integralAffineMap x₀ z p.m) C.determinant ≠ 0)
    (hdetSize : ∀ z ∈ depthSevenNormalizedJacobianChartCell
      p x₀ equations CF C,
      (((MvPolynomial.eval (integralAffineMap x₀ z p.m)
        C.determinant).natAbs : ℕ) : ℝ) ≤ H ^ A) :
    (depthSevenNormalizedJacobianChartCell p x₀ equations CF C).card ≤
      (∑ q : ReservoirModulus P k,
        ((depthSevenNormalizedJacobianChartCell p x₀ equations CF C).filter
          fun z ↦
            survivesTwoCertificates q ((p.m : ℤ) * denominator)
              (MvPolynomial.eval (integralAffineMap x₀ z p.m)
                C.determinant) ∧
            rankSevenStaticSurfaceLabel
              p x₀ equations CF C denominator P k hP hlower z q = none).card) +
      (∑ q : ReservoirModulus P k, ∑ r : ReservoirModulus P k,
        ((depthSevenNormalizedJacobianChartCell p x₀ equations CF C).filter
          fun z ↦
            survivesTwoCertificates q ((p.m : ℤ) * denominator)
              (MvPolynomial.eval (integralAffineMap x₀ z p.m)
                C.determinant) ∧
            survivesTwoCertificates r ((p.m : ℤ) * denominator)
              (MvPolynomial.eval (integralAffineMap x₀ z p.m)
                C.determinant) ∧
            (modulusReservoirGraph P k hP).Adj q r ∧
            rankSevenStaticSurfaceLabel
                p x₀ equations CF C denominator P k hP hlower z q ≠
              rankSevenStaticSurfaceLabel
                p x₀ equations CF C denominator P k hP hlower z r ∧
            rankSevenStaticSurfaceLabel
                p x₀ equations CF C denominator P k hP hlower z q ≠ none ∧
            rankSevenStaticSurfaceLabel
                p x₀ equations CF C denominator P k hP hlower z r ≠ none).card) +
      (∑ o ∈ occurringRankSevenStaticSurfaceLabels
          p x₀ equations CF C denominator P k hP hlower,
        ((depthSevenNormalizedJacobianChartCell p x₀ equations CF C).filter
          fun z ↦ o ≠ none ∧ ∀ q : ReservoirModulus P k,
            survivesTwoCertificates q ((p.m : ℤ) * denominator)
              (MvPolynomial.eval (integralAffineMap x₀ z p.m)
                C.determinant) →
            rankSevenStaticSurfaceLabel
              p x₀ equations CF C denominator P k hP hlower z q = o).card) := by
  let X := depthSevenNormalizedJacobianChartCell p x₀ equations CF C
  let D₁ : IntVector 13 → ℤ := fun _ ↦ (p.m : ℤ) * denominator
  let D₂ : IntVector 13 → ℤ := fun z ↦
    MvPolynomial.eval (integralAffineMap x₀ z p.m) C.determinant
  let label : IntVector 13 → ReservoirModulus P k →
      Option (Ideal (MvPolynomial (Fin 14) ℚ)) := fun z q ↦
    rankSevenStaticSurfaceLabel
      p x₀ equations CF C denominator P k hP hlower z q
  have hconnected : ∀ z ∈ X,
      (modulusReservoirGraph
        (certificateAllowedPrimesTwo P (D₁ z) (D₂ z)) k
        (fun s hs ↦ hP s (Finset.mem_filter.mp hs).1)).Connected := by
    intro z hz
    exact (hsurvival (D₁ z) (D₂ z)
      (hfixedNe) (hdetNe z hz)
      (hfixedSize) (hdetSize z hz)).2
  have hpartition := card_le_sum_certificateDeleted_reservoir_nonemptyEdges
    hP X D₁ D₂ label hconnected
  simpa only [X, D₁, D₂, label,
    occurringRankSevenStaticSurfaceLabels] using hpartition

end

end TranslatedDepthSeven
