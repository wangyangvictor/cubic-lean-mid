import TranslatedDepthSeven.HomogeneousNormalizationAwayFromPointInternal
import TranslatedDepthSeven.FiniteIntegralMonicRelationInternal
import TranslatedDepthSeven.MonicHomogeneousComponentSeparatorInternal
import TranslatedDepthSeven.HomogeneousNormalizationDegreeBoundInternal

/-!
# A degree-bounded equation separating an exterior affine-chart point

Choose linear normalization parameters vanishing at the exterior point.
A monic relation for `X_0` has degree at most the generic rank, hence at
most the projective degree.  Its homogeneous component of that degree
belongs to the original ideal and takes value one at the point.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
open scoped nonZeroDivisors

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

/-- The pointed normalization in consecutively indexed coordinates. -/
theorem exists_homogeneousLinearNormalization_vanishing_at_firstChartPoint
    {K : Type*} [Field K] [Infinite K] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hIprime : I.IsPrime)
    (hIhom : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K))
    (x : Fin (N + 1) → K) (hx0 : x 0 = 1)
    (hexterior : ∃ f ∈ I, eval x f ≠ 0) :
    ∃ D : HomogeneousLinearNormalizationData I,
      ∀ i, eval x (D.forms i) = 0 := by
  let e : Fin (N + 1) ≃ Option (Fin N) := _root_.finSuccEquiv N
  let E := MvPolynomial.renameEquiv K e
  let J := I.map E
  let c : Fin N → K := fun i ↦ x i.succ
  have hpoint : affineChartVector c ∘ e = x := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [e, affineChartVector, hx0]
    · simp [e, c, affineChartVector]
  have hpointBack : x ∘ e.symm = affineChartVector c := by
    rw [← hpoint, Function.comp_assoc, e.self_comp_symm, Function.comp_id]
  have heval (f : MvPolynomial (Fin (N + 1)) K) :
      eval (affineChartVector c) (E f) = eval x f := by
    change eval (affineChartVector c) (MvPolynomial.rename e f) = _
    rw [MvPolynomial.eval_rename, hpoint]
  letI : I.IsPrime := hIprime
  have hJprime : J.IsPrime := by dsimp only [J, E]; infer_instance
  have hJhom : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Option (Fin N)) K) :=
    map_renameEquiv_isHomogeneous e I hIhom
  have hJexterior : ∃ f ∈ J, eval (affineChartVector c) f ≠ 0 := by
    obtain ⟨f, hf, hfx⟩ := hexterior
    exact ⟨E f, Ideal.mem_map_of_mem E hf, by simpa only [heval] using hfx⟩
  obtain ⟨D, hDzero⟩ :=
    exists_homogeneousLinearNormalization_vanishing_at_affinePoint J hJprime hJhom c hJexterior
  refine ⟨D.renameEquiv e I, ?_⟩
  intro i
  change eval x (MvPolynomial.rename e.symm (D.forms i)) = 0
  rw [MvPolynomial.eval_rename, hpointBack]
  exact hDzero i

/-- A homogeneous equation of degree at most the projective degree
separates any specified exterior point on the first affine chart. -/
theorem exists_homogeneous_projectiveDegree_separator_at_firstChartPoint
    {K : Type*} [Field K] [CharZero K] {N r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hIprime : I.IsPrime)
    (hIhom : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K))
    (hdegree : HasProjectiveDimensionDegree I r d)
    (x : Fin (N + 1) → K) (hx0 : x 0 = 1)
    (hexterior : ∃ f ∈ I, eval x f ≠ 0) :
    ∃ (k : ℕ) (G : MvPolynomial (Fin (N + 1)) K),
      k ≤ d ∧ G.IsHomogeneous k ∧ G ∈ I ∧ eval x G = 1 := by
  obtain ⟨D, hDzero⟩ :=
    exists_homogeneousLinearNormalization_vanishing_at_firstChartPoint I hIprime hIhom x hx0 hexterior
  letI : I.IsPrime := hIprime
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial (Fin (N + 1)) K ⧸ I
  letI : Algebra B A := D.hom.toRingHom.toAlgebra
  letI : FaithfulSMul B A :=
    (faithfulSMul_iff_algebraMap_injective B A).mpr D.hom_injective
  haveI : Module.Finite B A := D.hom_finite
  let mk := Ideal.Quotient.mkₐ K I
  let xA : A := mk (X (0 : Fin (N + 1)))
  obtain ⟨p, hpmonic, hpdegree, hproot⟩ :=
    exists_monic_annihilator_natDegree_le_localized_rank (B := B) xA
  have hdegreebound : Module.finrank (FractionRing B)
      (LocalizedModule (nonZeroDivisors B) A) ≤ d :=
    (homogeneousLinearNormalization_genericRank_le_projectiveDegree I hIprime D hdegree).2
  let l : Option (Fin D.parameterCount) → MvPolynomial (Fin (N + 1)) K :=
    fun i ↦ i.elim (X 0) D.forms
  have hl : ∀ i, (l i).IsHomogeneous 1 := by
    intro i
    cases i with
    | none => exact isHomogeneous_X K 0
    | some i => exact D.forms_isHomogeneous i
  let F := aeval l ((optionEquivLeft K (Fin D.parameterCount)).symm p)
  have hcomposition : mk.comp (aeval l) =
      ((Polynomial.aeval xA).restrictScalars K).comp
        (optionEquivLeft K (Fin D.parameterCount)).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | none =>
        simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
        change mk (X 0) = Polynomial.aeval xA
          ((optionEquivLeft K (Fin D.parameterCount)) (X none))
        rw [optionEquivLeft_X_none, Polynomial.aeval_X]
    | some i =>
        simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
        change mk (D.forms i) = Polynomial.aeval xA
          ((optionEquivLeft K (Fin D.parameterCount)) (X (some i)))
        rw [optionEquivLeft_X_some, Polynomial.aeval_C]
        change mk (D.forms i) = D.hom (X i)
        simp [HomogeneousLinearNormalizationData.hom, mk]
  have hFmem : F ∈ I := by
    apply (Ideal.Quotient.eq_zero_iff_mem).1
    have h := DFunLike.congr_fun hcomposition
      ((optionEquivLeft K (Fin D.parameterCount)).symm p)
    change mk F = Polynomial.aeval xA
      ((optionEquivLeft K (Fin D.parameterCount))
        ((optionEquivLeft K (Fin D.parameterCount)).symm p)) at h
    rw [AlgEquiv.apply_symm_apply, hproot] at h
    exact h
  let G := homogeneousComponent p.natDegree F
  have hGmem : G ∈ I := by
    have h := hIhom p.natDegree hFmem
    change (MvPolynomial.decomposition.decompose' F p.natDegree :
      MvPolynomial (Fin (N + 1)) K) ∈ I at h
    simpa only [MvPolynomial.decomposition.decompose'_apply] using h
  refine ⟨p.natDegree, G, hpdegree.trans hdegreebound,
    homogeneousComponent_isHomogeneous p.natDegree F, hGmem, ?_⟩
  exact eval_homogeneousComponent_monic_linear_substitution p hpmonic l hl x
    (by simpa [l] using hx0) (fun i ↦ hDzero i)

end

end TranslatedDepthSeven
