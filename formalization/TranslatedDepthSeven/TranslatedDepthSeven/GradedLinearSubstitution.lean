import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Homogeneous components under linear substitution

Substitution of homogeneous linear forms is a graded homomorphism: it
commutes with every homogeneous-component projection.  This elementary fact
is the key algebraic device for extracting degree-one preimages from an
arbitrary surjectivity statement, without introducing a Hilbert scheme or a
graded-quotient interface.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

universe u v w

local instance standardMvPolynomialGradedAlgebra
    {R : Type u} {ι : Type v} [CommSemiring R] :
    GradedAlgebra (MvPolynomial.homogeneousSubmodule ι R) :=
  MvPolynomial.gradedAlgebra

/-- Evaluating a multivariate polynomial at homogeneous linear forms
commutes with projection to degree `m`. -/
theorem homogeneousComponent_aeval_linear
    {K : Type u} {τ : Type v} {σ : Type w} [Field K]
    (L : τ → MvPolynomial σ K)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (m : ℕ) (P : MvPolynomial τ K) :
    homogeneousComponent m (aeval L P) =
      aeval L (homogeneousComponent m P) := by
  classical
  calc
    homogeneousComponent m (aeval L P) =
        homogeneousComponent m
          (aeval L
            (∑ i ∈ Finset.range (P.totalDegree + 1),
              homogeneousComponent i P)) := by
      rw [sum_homogeneousComponent]
    _ = ∑ i ∈ Finset.range (P.totalDegree + 1),
          homogeneousComponent m
            (aeval L (homogeneousComponent i P)) := by
      simp only [map_sum]
    _ = ∑ i ∈ Finset.range (P.totalDegree + 1),
          if m = i then aeval L (homogeneousComponent i P) else 0 := by
      apply Finset.sum_congr rfl
      intro i _hi
      have hi :
          (aeval L (homogeneousComponent i P)).IsHomogeneous i := by
        simpa only [one_mul] using
          (homogeneousComponent_isHomogeneous i P).aeval L hL
      exact homogeneousComponent_of_mem hi
    _ = aeval L (homogeneousComponent m P) := by
      by_cases hm : m < P.totalDegree + 1
      · simp [hm]
      · have hdegree : P.totalDegree < m := by omega
        rw [homogeneousComponent_eq_zero m P hdegree]
        simp [hm]

/-- Membership in a homogeneous ideal may be tested degree by degree, in
the concrete standard grading of a multivariate polynomial ring. -/
theorem homogeneousComponent_mem_of_mem_homogeneousIdeal
    {K : Type u} {σ : Type w} [Field K]
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    {P : MvPolynomial σ K} (hP : P ∈ I) (m : ℕ) :
    homogeneousComponent m P ∈ I := by
  have hm :=
    (Ideal.IsHomogeneous.mem_iff
      (MvPolynomial.homogeneousSubmodule σ K) hI).mp hP m
  change
    (MvPolynomial.decomposition.decompose' P m : MvPolynomial σ K) ∈ I at hm
  simpa only [MvPolynomial.decomposition.decompose'_apply] using hm

/-- A surjective quotient map defined by homogeneous linear substitutions
has homogeneous preimages in every degree.  Thus an arbitrary ring-theoretic
surjectivity witness can be replaced by a witness in the required graded
piece. -/
theorem exists_homogeneous_preimage_of_surjective_linear_quotient
    {K : Type u} {τ : Type v} {σ : Type w} [Field K]
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    (L : τ → MvPolynomial σ K)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (hsurjective : Function.Surjective
      ((Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval L)))
    (m : ℕ) (f : MvPolynomial σ K) (hf : f.IsHomogeneous m) :
    ∃ P : MvPolynomial τ K,
      P.IsHomogeneous m ∧
        (Ideal.Quotient.mkₐ K I)
            (MvPolynomial.aeval L P) =
          (Ideal.Quotient.mkₐ K I) f := by
  obtain ⟨Q, hQ⟩ := hsurjective ((Ideal.Quotient.mkₐ K I) f)
  have hsub : MvPolynomial.aeval L Q - f ∈ I := by
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
    simpa only [AlgHom.coe_comp, Function.comp_apply,
      Ideal.Quotient.mkₐ_eq_mk] using hQ
  have hcomponent :
      homogeneousComponent m (MvPolynomial.aeval L Q - f) ∈ I :=
    homogeneousComponent_mem_of_mem_homogeneousIdeal I hI hsub m
  let P : MvPolynomial τ K := homogeneousComponent m Q
  have hP : P.IsHomogeneous m := homogeneousComponent_isHomogeneous m Q
  refine ⟨P, hP, ?_⟩
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  have hfcomponent : homogeneousComponent m f = f := by
    simpa only [if_pos] using
      (homogeneousComponent_of_mem (m := m) (n := m) hf)
  simpa only [map_sub, homogeneousComponent_aeval_linear L hL,
    hfcomponent, P] using hcomponent

/-- Under the same surjectivity hypothesis, every ambient coordinate class
lies in the `K`-linear span of the selected linear normalization classes.
This is the concrete degree-one consequence of graded surjectivity. -/
theorem quotient_X_mem_span_linear_images_of_surjective
    {K : Type u} {τ : Type v} {σ : Type w} [Field K]
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    (L : τ → MvPolynomial σ K)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (hsurjective : Function.Surjective
      ((Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval L)))
    (i : σ) :
    (Ideal.Quotient.mkₐ K I) (MvPolynomial.X i) ∈
      Submodule.span K
        (Set.range fun j ↦ (Ideal.Quotient.mkₐ K I) (L j)) := by
  obtain ⟨P, hP, hPeval⟩ :=
    exists_homogeneous_preimage_of_surjective_linear_quotient
      I hI L hL hsurjective 1 (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X K i)
  have hPspan :
      P ∈ Submodule.span K
        (Set.range (MvPolynomial.X : τ → MvPolynomial τ K)) := by
    rw [← MvPolynomial.homogeneousSubmodule_one_eq_span_X]
    exact hP
  have hEvalSpan :
      MvPolynomial.aeval L P ∈
        Submodule.span K (Set.range L) := by
    refine Submodule.span_induction
      (p := fun Q (_ : Q ∈ Submodule.span K
        (Set.range (MvPolynomial.X : τ → MvPolynomial τ K))) ↦
          MvPolynomial.aeval L Q ∈ Submodule.span K (Set.range L))
      ?gen ?zero ?add ?smul hPspan
    · rintro _ ⟨j, rfl⟩
      simpa using
        (Submodule.subset_span (R := K) (s := Set.range L)
          (Set.mem_range_self j))
    · simp
    · intro Q₁ Q₂ _ _ hQ₁ hQ₂
      simpa using (Submodule.span K (Set.range L)).add_mem hQ₁ hQ₂
    · intro a Q _ hQ
      simpa using (Submodule.span K (Set.range L)).smul_mem a hQ
  let q : MvPolynomial σ K →ₗ[K] (MvPolynomial σ K ⧸ I) :=
    (Ideal.Quotient.mkₐ K I).toLinearMap
  have hQuotientSpan :
      q (MvPolynomial.aeval L P) ∈
        Submodule.span K (Set.range fun j ↦ q (L j)) := by
    have hmap :
        q (MvPolynomial.aeval L P) ∈
          Submodule.map q (Submodule.span K (Set.range L)) :=
      Submodule.mem_map_of_mem hEvalSpan
    rw [Submodule.map_span] at hmap
    have hrange :
        q '' Set.range L = Set.range (fun j ↦ q (L j)) := by
      ext x
      constructor
      · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
        exact ⟨j, rfl⟩
      · rintro ⟨j, rfl⟩
        exact ⟨L j, ⟨j, rfl⟩, rfl⟩
    simpa only [hrange] using hmap
  rw [← hPeval]
  exact hQuotientSpan

end

end TranslatedDepthSeven
