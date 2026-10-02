import TranslatedDepthSeven.ProjectiveDegreeOneSpan

/-!
# Homogeneous Hilbert growth under finite linear normalization

Injectivity of the polynomial normalization gives the lower bound. Taking
the degree-`n` part of an expression in finitely many homogeneous module
generators gives the upper bound. No projective dimension or degree
certificate is used: these inequalities are intended to identify the
degree of the independently constructed eventual Hilbert polynomial.
-/

namespace TranslatedDepthSeven

noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

theorem quotientDecomposeLinearMap_normalizationData_apply
    {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    (D : HomogeneousLinearNormalizationData I)
    (p : MvPolynomial (Fin D.parameterCount) K) (n : ℕ) :
    ((quotientDecomposeLinearMap K σ I hI (D.hom p)) n :
      MvPolynomial σ K ⧸ I) = D.hom (homogeneousComponent n p) := by
  change ((quotientDecomposeLinearMap K σ I hI
    (Ideal.Quotient.mk I (aeval D.forms p))) n : MvPolynomial σ K ⧸ I) = _
  rw [quotientDecomposeLinearMap_mk_apply,
    homogeneousComponent_aeval_linear D.forms D.forms_isHomogeneous]
  rfl

theorem quotientDecomposeLinearMap_normalizationData_mul_apply
    {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    (D : HomogeneousLinearNormalizationData I)
    (p : MvPolynomial (Fin D.parameterCount) K) {e : ℕ}
    {x : MvPolynomial σ K ⧸ I}
    (hx : x ∈ quotientHomogeneousComponent K σ I e) (n : ℕ) :
    ((quotientDecomposeLinearMap K σ I hI (D.hom p * x)) (n + e) :
      MvPolynomial σ K ⧸ I) = D.hom (homogeneousComponent n p) * x := by
  let H := fun n ↦ quotientHomogeneousComponent K σ I n
  letI : GradedAlgebra H := quotientGradedAlgebra K σ I hI
  change ((DirectSum.decompose H (D.hom p * x) (n + e) : H (n + e)) :
    MvPolynomial σ K ⧸ I) = _
  rw [DirectSum.coe_decompose_mul_add_of_right_mem H hx]
  change ((quotientDecomposeLinearMap K σ I hI (D.hom p)) n :
    MvPolynomial σ K ⧸ I) * x = _
  rw [quotientDecomposeLinearMap_normalizationData_apply]

/-- The normalizing polynomial algebra injects into each corresponding
homogeneous piece of the quotient. -/
theorem normalizationData_homogeneousHilbert_lower
    {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    (D : HomogeneousLinearNormalizationData I) (n : ℕ) :
    (D.parameterCount + n - 1).choose n ≤
      Module.finrank K (quotientHomogeneousComponent K σ I n) := by
  let f : homogeneousSubmodule (Fin D.parameterCount) K n →ₗ[K]
      quotientHomogeneousComponent K σ I n :=
    (D.hom.toLinearMap.comp (homogeneousSubmodule (Fin D.parameterCount) K n).subtype).codRestrict
      _ (fun p ↦ normalizationData_hom_mem_homogeneousComponent I D p.2)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact D.hom_injective (congrArg Subtype.val hxy)
  simpa only [finrank_mvPolynomial_homogeneousSubmodule_fin] using
    f.finrank_le_finrank_of_injective hf

/-- Taking homogeneous parts of a finite module-generating family gives
the exact upper bound by a sum of shifted polynomial Hilbert functions. -/
theorem normalizationData_homogeneousHilbert_upper_sum
    {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    (D : HomogeneousLinearNormalizationData I)
    {N : ℕ} (t : Fin N → MvPolynomial σ K ⧸ I) (degree : Fin N → ℕ)
    (ht : ∀ i, t i ∈ quotientHomogeneousComponent K σ I (degree i))
    (hspan :
      letI : Algebra (MvPolynomial (Fin D.parameterCount) K) (MvPolynomial σ K ⧸ I) :=
        D.hom.toRingHom.toAlgebra
      Submodule.span (MvPolynomial (Fin D.parameterCount) K) (Set.range t) = ⊤)
    (n : ℕ) (hn : ∀ i, degree i ≤ n) :
    Module.finrank K (quotientHomogeneousComponent K σ I n) ≤
      ∑ i, (D.parameterCount + (n - degree i) - 1).choose (n - degree i) := by
  classical
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial σ K ⧸ I
  letI : Algebra B A := D.hom.toRingHom.toAlgebra
  let H := fun n ↦ quotientHomogeneousComponent K σ I n
  letI : GradedAlgebra H := quotientGradedAlgebra K σ I hI
  let P := fun i : Fin N ↦ homogeneousSubmodule (Fin D.parameterCount) K (n - degree i)
  let f : (∀ i, P i) →ₗ[K] H n :=
    { toFun := fun b ↦ ⟨∑ i, D.hom (b i) * t i, by
        apply Submodule.sum_mem
        intro i _
        have hm := (quotientHomogeneousComponent_gradedMonoid K σ I).mul_mem
          (normalizationData_hom_mem_homogeneousComponent I D (b i).2) (ht i)
        simpa only [Nat.sub_add_cancel (hn i)] using hm⟩
      map_add' := by
        intro b c
        apply Subtype.ext
        change ∑ i, D.hom ((b i : B) + (c i : B)) * t i = _
        simp only [map_add, add_mul, Finset.sum_add_distrib]
        rfl
      map_smul' := by
        intro a b
        apply Subtype.ext
        change ∑ i, D.hom (a • (b i : B)) * t i = a • ∑ i, D.hom (b i) * t i
        simp only [map_smul, smul_mul_assoc, Finset.smul_sum]
    }
  have hf : Function.Surjective f := by
    intro x
    have hxspan : (x : A) ∈ Submodule.span B (Set.range t) := by rw [hspan]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun B).mp hxspan
    let b : ∀ i, P i := fun i ↦ ⟨homogeneousComponent (n - degree i) (c i),
      homogeneousComponent_mem _ _⟩
    refine ⟨b, Subtype.ext ?_⟩
    have hcn : ∑ i, D.hom (c i) * t i = (x : A) := by
      simpa only [Algebra.smul_def] using hc
    calc
      (f b : A) = ∑ i, D.hom (homogeneousComponent (n - degree i) (c i)) * t i := rfl
      _ = ∑ i, ((quotientDecomposeLinearMap K σ I hI (D.hom (c i) * t i)) n : A) := by
        apply Finset.sum_congr rfl
        intro i _
        have hh := quotientDecomposeLinearMap_normalizationData_mul_apply
          I hI D (c i) (ht i) (n - degree i)
        have heq : n - degree i + degree i = n := Nat.sub_add_cancel (hn i)
        rw [heq] at hh
        exact hh.symm
      _ = ((quotientDecomposeLinearMap K σ I hI
          (∑ i, D.hom (c i) * t i)) n : A) := by
        rw [map_sum, DFinsupp.finset_sum_apply]
        exact (map_sum (H n).subtype _ _).symm
      _ = (x : A) := by
        rw [hcn]
        exact DirectSum.decompose_of_mem_same H x.2
  have hfin := LinearMap.finrank_range_le f
  rw [LinearMap.range_eq_top.mpr hf, finrank_top] at hfin
  rw [Module.finrank_pi_fintype K] at hfin
  simpa only [P, finrank_mvPolynomial_homogeneousSubmodule_fin] using hfin

/-- The binomial Hilbert function of a positive-dimensional polynomial
algebra is nondecreasing. -/
theorem normalization_binomial_mono (r : ℕ) (hr : 0 < r) {a b : ℕ} (hab : a ≤ b) :
    (r + a - 1).choose a ≤ (r + b - 1).choose b := by
  rw [← Nat.choose_symm (by omega : a ≤ r + a - 1),
    ← Nat.choose_symm (by omega : b ≤ r + b - 1)]
  have ha : r + a - 1 - a = r - 1 := by omega
  have hb : r + b - 1 - b = r - 1 := by omega
  rw [ha, hb]
  exact Nat.choose_le_choose _ (by omega)

/-- Eventual two-sided polynomial growth, using only a concrete finite
injective homogeneous linear normalization and quotient homogeneity. -/
theorem normalizationData_exists_homogeneousHilbert_squeeze
    {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    (D : HomogeneousLinearNormalizationData I) (hr : 0 < D.parameterCount) :
    ∃ C n₀ : ℕ, ∀ n ≥ n₀,
      (D.parameterCount + n - 1).choose n ≤
        Module.finrank K (quotientHomogeneousComponent K σ I n) ∧
      Module.finrank K (quotientHomogeneousComponent K σ I n) ≤
        C * (D.parameterCount + n - 1).choose n := by
  classical
  obtain ⟨N, t, degree, ht, hspan⟩ :=
    exists_homogeneous_generators_of_finite_normalizationData K σ I D
  refine ⟨N, Finset.univ.sup degree, ?_⟩
  intro n hn
  refine ⟨normalizationData_homogeneousHilbert_lower I D n, ?_⟩
  calc
    Module.finrank K (quotientHomogeneousComponent K σ I n) ≤
        ∑ i, (D.parameterCount + (n - degree i) - 1).choose (n - degree i) :=
      normalizationData_homogeneousHilbert_upper_sum I hI D t degree ht hspan n
        (fun i ↦ (Finset.le_sup (f := degree) (Finset.mem_univ i)).trans hn)
    _ ≤ ∑ _i : Fin N, (D.parameterCount + n - 1).choose n := by
      apply Finset.sum_le_sum
      intro i _
      exact normalization_binomial_mono D.parameterCount hr (Nat.sub_le n (degree i))
    _ = N * (D.parameterCount + n - 1).choose n := by simp

end
end TranslatedDepthSeven
