import TranslatedDepthSeven.HomogeneousIdealBridge

/-!
# Finite homogeneous generators of a homogeneous polynomial ideal

For a homogeneous ideal in a polynomial ring over a field, this file makes
the usual Noetherian argument literal.  We first choose a finite ordinary
generating family and then replace every generator by its finitely many
homogeneous components.  The resulting finite family generates the same
ideal, and every member comes with its degree.

This is purely commutative algebra.  It introduces no geometric or counting
hypothesis.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

universe u v

variable {K : Type u} [Field K] {σ : Type v} [Fintype σ]

local instance finiteGeneratorsMvPolynomialGradedAlgebra :
    GradedAlgebra (MvPolynomial.homogeneousSubmodule σ K) :=
  MvPolynomial.gradedAlgebra

/-- A homogeneous ideal in a finite-variable polynomial ring has a finite
generating family consisting of homogeneous polynomials.  The degree of each
chosen generator is displayed in the conclusion. -/
theorem exists_fin_homogeneous_generating_family
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K)) :
    ∃ N : ℕ, ∃ f : Fin N → MvPolynomial σ K, ∃ degree : Fin N → ℕ,
      (∀ i, (f i).IsHomogeneous (degree i)) ∧
      Ideal.span (Set.range f) = I := by
  classical
  have hIfg : I.FG := IsNoetherian.noetherian I
  obtain ⟨M, g, hg⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp hIfg
  let D : ℕ := Finset.univ.sup fun i : Fin M ↦ (g i).totalDegree
  let ι := Fin M × Fin (D + 1)
  let f₀ : ι → MvPolynomial σ K := fun ik ↦
    homogeneousComponent ik.2.1 (g ik.1)
  let degree₀ : ι → ℕ := fun ik ↦ ik.2.1
  have hf₀Hom (ik : ι) : (f₀ ik).IsHomogeneous (degree₀ ik) :=
    homogeneousComponent_isHomogeneous _ _
  have hf₀Mem (ik : ι) : f₀ ik ∈ I := by
    have hgI : g ik.1 ∈ I := by
      rw [← hg]
      exact Ideal.subset_span ⟨ik.1, rfl⟩
    have hcomponent := hI ik.2.1 hgI
    rw [← DirectSum.Decomposition.decompose'_eq] at hcomponent
    rw [MvPolynomial.decomposition.decompose'_apply] at hcomponent
    exact hcomponent
  have hspan₀ : Ideal.span (Set.range f₀) = I := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨ik, rfl⟩
      exact hf₀Mem ik
    · rw [← hg]
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      rw [← MvPolynomial.sum_homogeneousComponent (g i)]
      apply Ideal.sum_mem
      intro k hk
      apply Ideal.subset_span
      have hiD : (g i).totalDegree ≤ D :=
        Finset.le_sup (f := fun j : Fin M ↦ (g j).totalDegree)
          (Finset.mem_univ i)
      let k' : Fin (D + 1) := ⟨k,
        Nat.lt_succ_iff.mpr
          ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)).trans hiD)⟩
      exact ⟨(i, k'), rfl⟩
  let e := Fintype.equivFin ι
  let f : Fin (Fintype.card ι) → MvPolynomial σ K :=
    fun i ↦ f₀ (e.symm i)
  let degree : Fin (Fintype.card ι) → ℕ :=
    fun i ↦ degree₀ (e.symm i)
  refine ⟨Fintype.card ι, f, degree, ?_, ?_⟩
  · intro i
    exact hf₀Hom (e.symm i)
  · have hrange : Set.range f = Set.range f₀ := by
      apply Set.ext
      intro a
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨e.symm i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨e i, by simp only [f, Equiv.symm_apply_apply]⟩
    rw [hrange]
    exact hspan₀

/-- Finset form of `exists_fin_homogeneous_generating_family`. -/
theorem exists_finite_homogeneous_generators
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K)) :
    ∃ equations : Finset (MvPolynomial σ K),
      (∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d) ∧
      finiteEquationIdeal equations = I := by
  classical
  obtain ⟨N, f, degree, hfHom, hfSpan⟩ :=
    exists_fin_homogeneous_generating_family I hI
  let equations : Finset (MvPolynomial σ K) := Finset.univ.image f
  refine ⟨equations, ?_, ?_⟩
  · intro g hg
    change g ∈ Finset.univ.image f at hg
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hg
    exact ⟨degree i, hfHom i⟩
  · rw [finiteEquationIdeal]
    have hcoe : (equations : Set (MvPolynomial σ K)) = Set.range f := by
      ext g
      simp [equations]
    rw [hcoe]
    exact hfSpan

end

end TranslatedDepthSeven
