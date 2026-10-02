import TranslatedDepthSeven.IntegralSurfaceNormalizationBlock
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-! Independence of fixed-ideal blocks after the normalized progression
parameter change. The ideal and the auxiliary forms are unchanged. -/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000

theorem affinePlaneMonomialExponent_surjective_degree (k : ℕ)
    (d : Fin 3 →₀ ℕ) (hd : Finsupp.degree d = k) :
    ∃ u : AffinePlaneMonomialIndex k, affinePlaneMonomialExponent k u = d := by
  have hs : d 0 + d 1 + d 2 = k := by
    simpa [Finsupp.degree_eq_sum, Finsupp.sum_fintype, Fin.sum_univ_three] using hd
  let u : AffinePlaneMonomialIndex k :=
    ⟨⟨d 1 + d 2, by omega⟩, ⟨d 1, by change d 1 < d 1 + d 2 + 1; omega⟩⟩
  refine ⟨u, ?_⟩
  ext i
  fin_cases i <;> simp [affinePlaneMonomialExponent, u] <;> omega

theorem homogeneous_mem_span_affinePlaneMonomials
    (k : ℕ) (P : MvPolynomial (Fin 3) ℚ) (hP : P.IsHomogeneous k) :
    P ∈ Submodule.span ℚ (Set.range (affinePlaneHomogeneousMonomial ℚ k)) := by
  classical
  rw [P.as_sum]
  apply Submodule.sum_mem
  intro d hd
  obtain ⟨u, hu⟩ := affinePlaneMonomialExponent_surjective_degree k d
    (by simpa only [Finsupp.degree_eq_weight_one] using hP (MvPolynomial.mem_support_iff.mp hd))
  have he : MvPolynomial.monomial d (P.coeff d) =
      P.coeff d • affinePlaneHomogeneousMonomial ℚ k u := by
    rw [affinePlaneHomogeneousMonomial, hu, MvPolynomial.smul_monomial]
    simp
  rw [he]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨u, rfl⟩)

theorem quotient_mul_homogeneous_mem_normalizationBlockSpan
    {σ : Type*} {d : ℕ} (I : Ideal (MvPolynomial σ ℚ))
    (L : Fin 3 → MvPolynomial σ ℚ) (G : Fin d → MvPolynomial σ ℚ)
    (k : ℕ) (i : Fin d) (P : MvPolynomial (Fin 3) ℚ) (hP : P.IsHomogeneous k) :
    Ideal.Quotient.mk I (G i * MvPolynomial.aeval L P) ∈
      Submodule.span ℚ (Set.range (fun p : Fin d × AffinePlaneMonomialIndex k =>
        Ideal.Quotient.mk I (normalizationSurfaceBlockForm L G k p))) := by
  have hp := homogeneous_mem_span_affinePlaneMonomials k P hP
  clear hP
  induction hp using Submodule.span_induction with
  | mem P hP =>
      obtain ⟨u, rfl⟩ := hP
      exact Submodule.subset_span ⟨(i,u), rfl⟩
  | zero => simp
  | add P Q hP hQ ihP ihQ =>
      simpa only [map_add, mul_add] using Submodule.add_mem _ ihP ihQ
  | smul a P hP ih =>
      simpa only [map_smul, mul_smul_comm] using Submodule.smul_mem _ a ih

/-- An invertible homogeneous change of the three parameter variables
preserves independence of a complete block at its displayed degree. -/
theorem linearIndependent_normalizationBlock_parameter_change
    {σ : Type*} {d : ℕ} (I : Ideal (MvPolynomial σ ℚ))
    (L : Fin 3 → MvPolynomial σ ℚ) (G : Fin d → MvPolynomial σ ℚ)
    (k : ℕ) (β : MvPolynomial (Fin 3) ℚ ≃ₐ[ℚ] MvPolynomial (Fin 3) ℚ)
    (hβ : ∀ P, P.IsHomogeneous k → (β.symm P).IsHomogeneous k)
    (hLI : LinearIndependent ℚ (fun p : Fin d × AffinePlaneMonomialIndex k =>
      Ideal.Quotient.mk I (normalizationSurfaceBlockForm L G k p))) :
    LinearIndependent ℚ (fun p : Fin d × AffinePlaneMonomialIndex k =>
      Ideal.Quotient.mk I (normalizationSurfaceBlockForm
        (fun i => MvPolynomial.aeval L (β (MvPolynomial.X i))) G k p)) := by
  classical
  let L' := fun i => MvPolynomial.aeval L (β (MvPolynomial.X i))
  have hcomp : MvPolynomial.aeval L' = (MvPolynomial.aeval L).comp β.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [L']
  have hle : Submodule.span ℚ (Set.range (fun p : Fin d × AffinePlaneMonomialIndex k =>
        Ideal.Quotient.mk I (normalizationSurfaceBlockForm L G k p))) ≤
      Submodule.span ℚ (Set.range (fun p : Fin d × AffinePlaneMonomialIndex k =>
        Ideal.Quotient.mk I (normalizationSurfaceBlockForm L' G k p))) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p,rfl⟩
    have h := quotient_mul_homogeneous_mem_normalizationBlockSpan I L' G k p.1
      (β.symm (affinePlaneHomogeneousMonomial ℚ k p.2))
      (hβ _ (affinePlaneHomogeneousMonomial_isHomogeneous ℚ k p.2))
    simpa only [hcomp, AlgHom.comp_apply, AlgEquiv.coe_algHom,
      AlgEquiv.apply_symm_apply, normalizationSurfaceBlockForm] using h
  haveI : Module.Finite ℚ (Submodule.span ℚ (Set.range
      (fun p : Fin d × AffinePlaneMonomialIndex k =>
        Ideal.Quotient.mk I (normalizationSurfaceBlockForm L' G k p)))) :=
    Module.Finite.span_of_finite ℚ (Set.finite_range _)
  apply linearIndependent_iff_card_le_finrank_span.mpr
  rw [linearIndependent_iff_card_eq_finrank_span.mp hLI]
  exact Submodule.finrank_mono hle

def progressionParameterForms (c : Fin 2 → ℚ) (m : ℚ) :
    Fin 3 → MvPolynomial (Fin 3) ℚ :=
  ![X 0, C m⁻¹ * (X 1 - C (c 0) * X 0), C m⁻¹ * (X 2 - C (c 1) * X 0)]

def progressionParameterInverseForms (c : Fin 2 → ℚ) (m : ℚ) :
    Fin 3 → MvPolynomial (Fin 3) ℚ :=
  ![X 0, C m * X 1 + C (c 0) * X 0, C m * X 2 + C (c 1) * X 0]

def progressionParameterAlgEquiv (c : Fin 2 → ℚ) (m : ℚ) (hm : m ≠ 0) :
    MvPolynomial (Fin 3) ℚ ≃ₐ[ℚ] MvPolynomial (Fin 3) ℚ :=
  AlgEquiv.ofAlgHom (MvPolynomial.aeval (progressionParameterForms c m))
    (MvPolynomial.aeval (progressionParameterInverseForms c m))
    (by
      ext i
      fin_cases i <;> simp [progressionParameterForms, progressionParameterInverseForms,
        mul_sub, hm])
    (by
      ext i
      fin_cases i <;> simp [progressionParameterForms, progressionParameterInverseForms,
        mul_add, mul_sub, hm])

theorem progressionParameterAlgEquiv_symm_isHomogeneous
    (c : Fin 2 → ℚ) (m : ℚ) (hm : m ≠ 0)
    {P : MvPolynomial (Fin 3) ℚ} {k : ℕ} (hP : P.IsHomogeneous k) :
    ((progressionParameterAlgEquiv c m hm).symm P).IsHomogeneous k := by
  change (MvPolynomial.aeval (progressionParameterInverseForms c m) P).IsHomogeneous k
  have hforms : ∀ i, (progressionParameterInverseForms c m i).IsHomogeneous 1 := by
    intro i
    fin_cases i
    · exact MvPolynomial.isHomogeneous_X ℚ 0
    · exact (MvPolynomial.isHomogeneous_C_mul_X m 1).add
        (MvPolynomial.isHomogeneous_C_mul_X (c 0) 0)
    · exact (MvPolynomial.isHomogeneous_C_mul_X m 2).add
        (MvPolynomial.isHomogeneous_C_mul_X (c 1) 0)
  simpa only [one_mul] using hP.aeval _ hforms

/-- The fixed ideal and fixed auxiliary family retain block independence
after subtracting the center and dividing the two parameters by `m`. -/
theorem linearIndependent_normalizedProgressionBlock
    {σ : Type*} {d : ℕ} (I : Ideal (MvPolynomial σ ℚ))
    (L : Fin 3 → MvPolynomial σ ℚ) (G : Fin d → MvPolynomial σ ℚ)
    (c : Fin 2 → ℚ) (m : ℚ) (hm : m ≠ 0) (k : ℕ)
    (hLI : LinearIndependent ℚ (fun p : Fin d × AffinePlaneMonomialIndex k =>
      Ideal.Quotient.mk I (normalizationSurfaceBlockForm L G k p))) :
    LinearIndependent ℚ (fun p : Fin d × AffinePlaneMonomialIndex k =>
      Ideal.Quotient.mk I (normalizationSurfaceBlockForm
        ![L 0, C m⁻¹ * (L 1 - C (c 0) * L 0),
          C m⁻¹ * (L 2 - C (c 1) * L 0)] G k p)) := by
  have h := linearIndependent_normalizationBlock_parameter_change I L G k
    (progressionParameterAlgEquiv c m hm)
    (fun P hP => progressionParameterAlgEquiv_symm_isHomogeneous c m hm hP) hLI
  have he : (fun i => MvPolynomial.aeval L ((progressionParameterAlgEquiv c m hm) (X i))) =
      ![L 0, C m⁻¹ * (L 1 - C (c 0) * L 0), C m⁻¹ * (L 2 - C (c 1) * L 0)] := by
    funext i
    fin_cases i <;> simp [progressionParameterAlgEquiv, progressionParameterForms]
  rwa [he] at h

end
end TranslatedDepthSeven
