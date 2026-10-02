import CubicTenVariables.HomogeneousFamilyDeterminant
import CubicTenVariables.HomogeneousFiniteCutDimension
import CubicTenVariables.ProperHomogeneousNormalization

/-! Closedness of the actual large-fiber parameter locus for a finite
family homogeneous of positive fiber degrees. At every small fiber, a
linear normalization and a square coefficient determinant give an actual
principal neighborhood of small fibers. No proper-morphism or spreading
result is assumed. -/

noncomputable section
namespace CubicTenVariables.HomogeneousFamilyBadLocus
open MvPolynomial HessianTheorem11 TranslatedDepthSeven
open HomogeneousPowerCertificates HomogeneousFiniteCutDimension

attribute [local instance] MvPolynomial.gradedAlgebra

variable {m n : ℕ} {ι : Type*}

/-- Actual specialization of the parameter coefficients, retaining the fiber variables. -/
def specialized (f : ι → MvPolynomial (Fin n) (GeometricPolynomial m))
    (v : GeometricPoint m) (j : ι) : GeometricPolynomial n := map (eval v) (f j)

def fiberIdeal (f : ι → MvPolynomial (Fin n) (GeometricPolynomial m))
    (v : GeometricPoint m) : Ideal (GeometricPolynomial n) :=
  Ideal.span (Set.range (specialized f v))

/-- Literal common zeros of the finite equations at the parameter. -/
def fiber (f : ι → MvPolynomial (Fin n) (GeometricPolynomial m))
    (v : GeometricPoint m) : Set (GeometricPoint n) :=
  {x | ∀ j, eval x (specialized f v j) = 0}

theorem fiber_eq_zeroLocus (f : ι → MvPolynomial (Fin n) (GeometricPolynomial m))
    (v : GeometricPoint m) : fiber f v = zeroLocus GeometricField (fiberIdeal f v) := by
  ext x
  rw [fiberIdeal, zeroLocus_span]
  change (∀ j, eval x (specialized f v j)=0) ↔
    ∀ g ∈ Set.range (specialized f v), eval x g=0
  simp only [Set.forall_mem_range]

theorem fiber_closed (f : ι → MvPolynomial (Fin n) (GeometricPolynomial m))
    (v : GeometricPoint m) : AlgebraicallyClosedSet (fiber f v) := by
  rw [fiber_eq_zeroLocus]
  exact algebraicallyClosedSet_zeroLocus _

theorem fiberIdeal_homogeneous
    (f : ι → MvPolynomial (Fin n) (GeometricPolynomial m)) (e : ι → ℕ)
    (hf : ∀ j, (f j).IsHomogeneous (e j)) (v : GeometricPoint m) :
    (fiberIdeal f v).IsHomogeneous (homogeneousSubmodule (Fin n) GeometricField) := by
  apply Ideal.homogeneous_span
  rintro _ ⟨j,rfl⟩
  exact ⟨e j, (hf j).map (eval v)⟩

theorem fiber_cone
    (f : ι → MvPolynomial (Fin n) (GeometricPolynomial m)) (e : ι → ℕ)
    (hf : ∀ j, (f j).IsHomogeneous (e j)) (v : GeometricPoint m) :
    IsAffineCone (fiber f v) := by
  rw [fiber_eq_zeroLocus]
  exact zeroLocus_cone_of_homogeneous _ (fiberIdeal_homogeneous f e hf v)

theorem origin_mem_fiber
    (f : ι → MvPolynomial (Fin n) (GeometricPolynomial m)) (e : ι → ℕ)
    (hf : ∀ j, (f j).IsHomogeneous (e j)) (he : ∀ j, 0<e j)
    (v : GeometricPoint m) : (0 : GeometricPoint n) ∈ fiber f v := by
  intro j
  exact LocalCubicNormalForm.eval_zero_positive_homogeneous _
    ((hf j).map (eval v)) (he j).ne'

theorem fiberIdeal_ne_top
    (f : ι → MvPolynomial (Fin n) (GeometricPolynomial m)) (e : ι → ℕ)
    (hf : ∀ j, (f j).IsHomogeneous (e j)) (he : ∀ j, 0<e j)
    (v : GeometricPoint m) : fiberIdeal f v ≠ ⊤ := by
  intro htop
  have h0 := origin_mem_fiber f e hf he v
  rw [fiber_eq_zeroLocus, htop, zeroLocus_top] at h0
  exact h0

theorem fiber_dimension_eq_quotient
    (f : ι → MvPolynomial (Fin n) (GeometricPolynomial m))
    (v : GeometricPoint m) :
    affineDimension (fiber f v) = ringKrullDim (GeometricPolynomial n ⧸ fiberIdeal f v) := by
  rw [fiber_eq_zeroLocus, affineDimension, vanishingIdeal_zeroLocus_eq_radical,
    UnconditionalCutDimension.quotient_radical_dimension]

@[simp] theorem map_eval_map_C (v : GeometricPoint m) (P : GeometricPolynomial n) :
    map (eval v) (map (C : GeometricField →+* GeometricPolynomial m) P) = P := by
  ext s
  simp only [coeff_map, eval_C]

variable [Fintype ι]

/-- Small fibers persist on an actual principal neighborhood. The same
linear cuts and determinant work for every future parameter in that open. -/
theorem exists_small_fiber_neighborhood
    (f : ι → MvPolynomial (Fin n) (GeometricPolynomial m)) (e : ι → ℕ)
    (hf : ∀ j, (f j).IsHomogeneous (e j)) (he : ∀ j, 0<e j)
    (t : ℕ) (v₀ : GeometricPoint m)
    (hsmall : affineDimension (fiber f v₀) < ((t+1 : ℕ) : Dimension)) :
    ∃ D : GeometricPolynomial m, eval v₀ D=1 ∧
      ∀ v : GeometricPoint m, eval v D≠0 → affineDimension (fiber f v) ≤ (t : Dimension) := by
  classical
  let I := fiberIdeal f v₀
  have hproper : I ≠ ⊤ := fiberIdeal_ne_top f e hf he v₀
  have hhom := fiberIdeal_homogeneous f e hf v₀
  obtain ⟨L⟩ := ProperHomogeneousNormalization.exists_homogeneousLinearNormalizationData
    n I hproper hhom
  letI : Nontrivial (GeometricPolynomial n ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hproper
  have hs : L.parameterCount ≤ t := by
    apply Nat.le_of_lt_succ
    apply normalization_parameter_lt_of_ringKrullDim_lt_nat
      L.hom L.hom_injective L.hom_finite.to_isIntegral
    rwa [← fiber_dimension_eq_quotient]
  let fcut : ι ⊕ Fin L.parameterCount →
      MvPolynomial (Fin n) (GeometricPolynomial m) :=
    Sum.elim f (fun i => map C (L.forms i))
  let ecut : ι ⊕ Fin L.parameterCount → ℕ := Sum.elim e (fun _ => 1)
  have hcutHom : ∀ j, (fcut j).IsHomogeneous (ecut j) := by
    intro j
    cases j with
    | inl j => exact hf j
    | inr j => exact (L.forms_isHomogeneous j).map C
  have hcutEq (v : GeometricPoint m) :
      fiberIdeal fcut v = fiberIdeal f v ⊔ Ideal.span (Set.range L.forms) := by
    have hfun : specialized fcut v = Sum.elim (specialized f v) L.forms := by
      funext j
      cases j with
      | inl j => rfl
      | inr j => exact map_eval_map_C v (L.forms j)
    rw [fiberIdeal, hfun, Set.Sum.elim_range, Ideal.span_union]
    rfl
  have hfinite : Module.Finite GeometricField
      (GeometricPolynomial n ⧸ fiberIdeal fcut v₀) := by
    rw [hcutEq]
    exact finite_cut_quotient I L
  letI : Module.Finite GeometricField (MvPolynomial (Fin n) GeometricField ⧸
      Ideal.span (Set.range (fun j => map (eval v₀) (fcut j)))) := hfinite
  obtain ⟨D,hD,hopen⟩ :=
    HomogeneousFamilyDeterminant.exists_principal_neighborhood_of_finite_quotient
      fcut ecut hcutHom v₀
  refine ⟨D,hD,?_⟩
  intro v hv
  obtain ⟨_,horigin⟩ := hopen v hv
  have hdim : affineDimension (fiber f v) ≤ (L.parameterCount : Dimension) := by
    apply dimension_le_of_linear_cuts_at_origin _ (fiber_closed f v)
      (fiber_cone f e hf v) L.forms L.forms_isHomogeneous
    intro x hx hL
    apply horigin x
    intro j
    cases j with
    | inl j => exact hx j
    | inr j =>
      change eval x (map (eval v) (map C (L.forms j))) = 0
      rw [map_eval_map_C]
      exact hL j
  exact hdim.trans (by exact_mod_cast hs)

/-- Actual large-fiber parameters, before taking any closure. -/
def badParameters
    (f : ι → MvPolynomial (Fin n) (GeometricPolynomial m)) (t : ℕ) :
    Set (GeometricPoint m) :=
  {v | ((t+1 : ℕ) : Dimension) ≤ affineDimension (fiber f v)}

/-- The actual bad-parameter locus is algebraically closed. In particular,
its geometric closure adds no parameters, rational or otherwise. -/
theorem badParameters_closed
    (f : ι → MvPolynomial (Fin n) (GeometricPolynomial m)) (e : ι → ℕ)
    (hf : ∀ j, (f j).IsHomogeneous (e j)) (he : ∀ j, 0<e j) (t : ℕ) :
    AlgebraicallyClosedSet (badParameters f t) := by
  apply le_antisymm _ (subset_geometricClosure _)
  intro v hv
  by_contra hbad
  have hsmall : affineDimension (fiber f v) < ((t+1 : ℕ) : Dimension) :=
    lt_of_not_ge hbad
  obtain ⟨D,hD,hopen⟩ := exists_small_fiber_neighborhood f e hf he t v hsmall
  have hvan : D ∈ vanishingIdeal GeometricField (badParameters f t) := by
    intro w hw
    change eval w D=0
    by_contra hnonzero
    have hle : ((t+1 : ℕ) : Dimension) ≤ (t : Dimension) := hw.trans (hopen w hnonzero)
    exact (not_le_of_gt (by exact_mod_cast Nat.lt_succ_self t)) hle
  have hz := hv D hvan
  change eval v D=0 at hz
  rw [hD] at hz
  exact one_ne_zero hz

end CubicTenVariables.HomogeneousFamilyBadLocus
