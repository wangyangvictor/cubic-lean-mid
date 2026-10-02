import TranslatedDepthSeven.HomogeneousConeStandardChart
import CubicTenVariables.GenericNormalParameterRecovery
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-! Concrete transcendence-degree bounds for generic linear-section avoidance.
The homogeneous source ideal need not be prime: the line through a tested
point supplies the prime quotient used in the dimension argument. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000
noncomputable section

namespace CubicTenVariables.GenericNormalAvoidance
open MvPolynomial TranslatedDepthSeven Algebra
open scoped IntermediateField.algebraAdjoinAdjoin
attribute [local instance] MvPolynomial.gradedAlgebra
universe u

private theorem scalingKernel_isHomogeneous
    {k Ω σ : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (D : MvPolynomial σ k →ₐ[k] Ω) :
    (RingHom.ker (homogeneousScalingHom D).toRingHom).IsHomogeneous
      (homogeneousSubmodule σ k) := by
  intro d f hf
  rw [← DirectSum.Decomposition.decompose'_eq,
    MvPolynomial.decomposition.decompose'_apply]
  change homogeneousScalingHom D (homogeneousComponent d f) = 0
  change homogeneousScalingHom D f = 0 at hf
  have hc := congrArg (fun p : Polynomial Ω ↦ p.coeff d) hf
  dsimp only at hc
  rw [homogeneousScalingHom_coeff, Polynomial.coeff_zero] at hc
  rw [homogeneousScalingHom_apply_of_isHomogeneous D _ (homogeneousComponent_isHomogeneous d f),
    hc, Polynomial.C_0, zero_mul]

private theorem homogeneousIdeal_le_scalingKernel
    {k Ω σ : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k))
    (D : MvPolynomial σ k →ₐ[k] Ω) (hD : ∀ f ∈ I, D f = 0) :
    I ≤ RingHom.ker (homogeneousScalingHom D).toRingHom := by
  intro f hf
  change homogeneousScalingHom D f = 0
  apply Polynomial.ext
  intro d
  rw [homogeneousScalingHom_coeff, Polynomial.coeff_zero]
  apply hD
  have h := hI d hf
  rw [← DirectSum.Decomposition.decompose'_eq,
    MvPolynomial.decomposition.decompose'_apply] at h
  exact h

private theorem scalingKernel_le_evaluationKernel
    {k Ω σ : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (D : MvPolynomial σ k →ₐ[k] Ω) :
    RingHom.ker (homogeneousScalingHom D).toRingHom ≤ RingHom.ker D.toRingHom := by
  have he : ((Polynomial.aeval (1 : Ω)).restrictScalars k).comp
      (homogeneousScalingHom D) = D := by
    ext i
    simp [homogeneousScalingHom]
  intro f hf
  change homogeneousScalingHom D f = 0 at hf
  change D f = 0
  rw [← he]
  change (Polynomial.aeval (1 : Ω)) (homogeneousScalingHom D f) = 0
  rw [hf, map_zero]

/-- Normalizing a nonzero coordinate to one removes one transcendence
parameter. This uses the actual homogeneous ideal and its Krull dimension,
without assuming that the whole cone is irreducible or reduced. -/
theorem trdeg_normalizedPointCoordinates_le
    {k Ω : Type u} [Field k] [CharZero k] [Field Ω] [Algebra k Ω]
    {n r : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) k))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) k))
    (hdim : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ I) ≤
      ((r + 1 : ℕ) : WithBot ℕ∞))
    (x : Fin (n + 1) → Ω) (hx₀ : x 0 = 1)
    (hx : ∀ f ∈ I, aeval x f = 0) :
    Algebra.trdeg k (IntermediateField.adjoin k (Set.range (fun i : Fin n ↦ x i.succ))) ≤
      (r : Cardinal) := by
  classical
  let D : MvPolynomial (Fin (n + 1)) k →ₐ[k] Ω := aeval x
  let P := RingHom.ker (homogeneousScalingHom D).toRingHom
  have hP : P.IsPrime := RingHom.ker_isPrime _
  letI : P.IsPrime := hP
  have hPhom : P.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) k) :=
    scalingKernel_isHomogeneous D
  have hIP : I ≤ P := homogeneousIdeal_le_scalingKernel I hI D hx
  have hPX : X (0 : Fin (n + 1)) ∉ P := by
    intro h
    change homogeneousScalingHom D (X 0) = 0 at h
    simp [homogeneousScalingHom, D, hx₀] at h
  have hdimP : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ P) ≤
      ((r + 1 : ℕ) : WithBot ℕ∞) :=
    (ringKrullDim_le_of_surjective (Ideal.Quotient.factor hIP)
      (Ideal.Quotient.factor_surjective hIP)).trans hdim
  obtain ⟨s, _hs, _g, _hg, _hgfinite, hsTrdeg⟩ :=
    exists_finite_injective_normalization_of_primeAffine_with_trdeg P
  have hsDim := ringKrullDim_eq_nat_of_primeAffine_trdeg_eq k P hP hsTrdeg
  have hsle : s ≤ r + 1 := by
    rw [hsDim] at hdimP
    exact_mod_cast hdimP
  obtain ⟨q, hqs, hqDim⟩ := exists_standardAffineChart_dimension P hPhom hP hPX hsDim
  have hqr : q ≤ r := by omega
  let J := P.map (standardDehomogenizationHom k n)
  have hJ : J.IsPrime := by
    obtain ⟨hhom, hprime, hnone⟩ := finSuccRename_homogeneousPrime_avoids_none P hPhom hP hPX
    have h := map_multivariateDehomogenization_isPrime
      (P.map (renameEquiv k (_root_.finSuccEquiv n))) hhom hprime hnone
    rwa [map_standardDehomogenizationHom_finSuccRename] at h
  have hJtrdeg : Algebra.trdeg k (MvPolynomial (Fin n) k ⧸ J) = (q : Cardinal) :=
    trdeg_eq_nat_of_primeAffine_ringKrullDim_eq k J hJ hqDim
  let y : Fin n → Ω := fun i ↦ x i.succ
  have heval : (aeval y).toRingHom.comp (standardDehomogenizationHom k n) = D.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [standardDehomogenizationHom, D]
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp [standardDehomogenizationHom, D, hx₀]
      · simp [standardDehomogenizationHom, D, y]
  have hJker : J ≤ RingHom.ker (aeval y).toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    change P ≤ RingHom.ker ((aeval y).toRingHom.comp (standardDehomogenizationHom k n))
    rw [heval]
    exact scalingKernel_le_evaluationKernel D
  let A := Algebra.adjoin k (Set.range y)
  let f : MvPolynomial (Fin n) k →ₐ[k] A := (aeval y).codRestrict A (by
    intro p
    dsimp only [A]
    rw [Algebra.adjoin_range_eq_range_aeval]
    exact ⟨p, rfl⟩)
  have hf : Function.Surjective f := by
    intro a
    have ha : (a : Ω) ∈ (aeval y : MvPolynomial (Fin n) k →ₐ[k] Ω).range := by
      simpa only [A, Algebra.adjoin_range_eq_range_aeval] using a.property
    obtain ⟨p, hp⟩ := ha
    exact ⟨p, Subtype.ext hp⟩
  have hkill : ∀ p ∈ J, f p = 0 := by
    intro p hp
    apply Subtype.ext
    exact hJker hp
  let fQ := Ideal.Quotient.liftₐ J f hkill
  have hfQ : Function.Surjective fQ := by
    intro a
    obtain ⟨p, hp⟩ := hf a
    exact ⟨Ideal.Quotient.mk J p, hp⟩
  have hA : Algebra.trdeg k A ≤ (q : Cardinal) :=
    (trdeg_le_of_surjective fQ hfQ).trans_eq hJtrdeg
  have hfield : Algebra.trdeg k (IntermediateField.adjoin k (Set.range y)) =
      Algebra.trdeg k A := by
    have h := trdeg_add_eq k A (A := IntermediateField.adjoin k (Set.range y))
    simpa only [trdeg_eq_zero, add_zero] using h.symm
  rw [hfield]
  exact hA.trans (by exact_mod_cast hqr)


private theorem homogeneousIdeal_aeval_smul_zero
    {k Ω σ : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k))
    (x : σ → Ω) (hx : ∀ f ∈ I, aeval x f = 0) (c : Ω) :
    ∀ f ∈ I, aeval (c • x) f = 0 := by
  have he : ((Polynomial.aeval c).restrictScalars k).comp
      (homogeneousScalingHom (aeval x)) = aeval (c • x) := by
    ext i
    simp [homogeneousScalingHom, Pi.smul_apply, smul_eq_mul]
    exact mul_comm _ _
  intro f hf
  have hz : homogeneousScalingHom (aeval x) f = 0 :=
    homogeneousIdeal_le_scalingKernel I hI (aeval x) hx hf
  rw [← he]
  change (Polynomial.aeval c) (homogeneousScalingHom (aeval x) f) = 0
  rw [hz, map_zero]

/-- Five algebraically independent linear equations avoid every nonzero
point of a homogeneous ten-variable cone of dimension at most five.
The ideal can be reducible and nonreduced. All equations and parameters
are the displayed polynomial and field elements. -/
theorem genericNormal_avoids_small_homogeneousCone
    {k Ω : Type u} [Field k] [CharZero k] [Field Ω] [Algebra k Ω]
    (ι : MvPolynomial (Fin 50) k →ₐ[k] Ω) (hι : Function.Injective ι)
    (I : Ideal (MvPolynomial (Fin 10) k))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin 10) k))
    (hdim : ringKrullDim (MvPolynomial (Fin 10) k ⧸ I) ≤ 5)
    (x : Fin 10 → Ω) (hxI : ∀ f ∈ I, aeval x f = 0)
    (hrows : Matrix.mulVec
      (fun r : Fin 5 ↦ fun i : Fin 10 ↦ ι (X (finProdFinEquiv (r, i)))) x = 0) :
    x = 0 := by
  classical
  by_contra hx
  have hex : ∃ j : Fin 10, x j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  obtain ⟨j, hj⟩ := hex
  let e : Fin 10 ≃ Fin 10 := Equiv.swap j 0
  let z : Fin 10 → Ω := fun i ↦ (x j)⁻¹ * x (e.symm i)
  have hz₀ : z 0 = 1 := by simp [z, e, hj]
  have hzcomp : z ∘ e = (x j)⁻¹ • x := by
    ext i
    simp [z]
  let I' := I.map (renameEquiv k e)
  have hI'hom : I'.IsHomogeneous (homogeneousSubmodule (Fin 10) k) :=
    map_renameEquiv_isHomogeneous e I hI
  have hI'dim : ringKrullDim (MvPolynomial (Fin 10) k ⧸ I') ≤ (5 : WithBot ℕ∞) :=
    (ringKrullDim_eq_of_ringEquiv (renameQuotientAlgEquiv k e I).toRingEquiv).symm.trans_le hdim
  have hzI : ∀ f ∈ I', aeval z f = 0 := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective (renameEquiv k e) (renameEquiv k e).surjective).mp hf
    rw [renameEquiv_apply, aeval_rename, hzcomp]
    exact homogeneousIdeal_aeval_smul_zero I hI x hxI (x j)⁻¹ g hg
  let Γ : Matrix (Fin 5) (Fin 10) Ω := fun a i ↦ ι (X (finProdFinEquiv (a, i)))
  let Γ' := Γ.submatrix id e.symm
  have hΓz : Γ'.mulVec z = 0 := by
    change (Γ.submatrix id e.symm).mulVec z = 0
    rw [Matrix.submatrix_mulVec_equiv]
    change Γ.mulVec (z ∘ e) = 0
    rw [hzcomp, Matrix.mulVec_smul, show Γ.mulVec x = 0 from hrows, smul_zero]
  let y : Fin 9 → Ω := fun i ↦ z i.succ
  let P := IntermediateField.adjoin k (Set.range y)
  have hPdim : Algebra.trdeg k P ≤ (4 : Cardinal) :=
    trdeg_normalizedPointCoordinates_le (n := 9) (r := 4) I' hI'hom hI'dim z hz₀ hzI
  let remaining : Fin 45 → Ω := fun a ↦
    Γ' ((finProdFinEquiv : Fin 5 × Fin 9 ≃ Fin 45).symm a).1
      ((finProdFinEquiv : Fin 5 × Fin 9 ≃ Fin 45).symm a).2.succ
  let T := IntermediateField.adjoin P (Set.range remaining)
  have hTdim : Algebra.trdeg P T ≤ (45 : Cardinal) :=
    GenericNormalParameterRecovery.trdeg_adjoin_fin_le remaining
  have hzP (i : Fin 10) : z i ∈ P := by
    refine Fin.cases ?_ (fun a ↦ ?_) i
    · rw [hz₀]
      exact P.one_mem
    · exact IntermediateField.subset_adjoin k _ (Set.mem_range_self a)
  have hzT (i : Fin 10) : z i ∈ T :=
    T.algebraMap_mem (⟨z i, hzP i⟩ : P)
  have hremaining (a : Fin 5) (i : Fin 10) (hi : i ≠ 0) : Γ' a i ∈ T := by
    obtain ⟨b, rfl⟩ := Fin.eq_succ_of_ne_zero hi
    apply IntermediateField.subset_adjoin P _
    exact ⟨finProdFinEquiv (a, b), by simp [remaining]⟩
  have hcoeff' := GenericNormalParameterRecovery.all_coefficients_mem T z Γ' 0
    (by rw [hz₀]; exact one_ne_zero) hzT hremaining
    (fun a ↦ congrFun hΓz a)
  have hcoeff (a : Fin 50) : ι (X a) ∈ T := by
    obtain ⟨⟨r, i⟩, rfl⟩ := (finProdFinEquiv : Fin 5 × Fin 10 ≃ Fin 50).surjective a
    simpa [Γ', Γ] using hcoeff' r (e i)
  let ψ : MvPolynomial (Fin 50) k →ₐ[k] T := aeval fun a ↦ ⟨ι (X a), hcoeff a⟩
  have hcomp : (T.val.restrictScalars k).comp ψ = ι := by
    ext a
    simp [ψ]
  have hψ : Function.Injective ψ := by
    intro f g hfg
    apply hι
    have h := congrArg (fun a : T ↦ (a : Ω)) hfg
    change ((T.val.restrictScalars k).comp ψ) f = ((T.val.restrictScalars k).comp ψ) g at h
    simpa only [hcomp] using h
  have hlower : (50 : Cardinal) ≤ Algebra.trdeg k T := by
    simpa using trdeg_le_of_injective ψ hψ
  have hupper : Algebra.trdeg k T ≤ (49 : Cardinal) := by
    calc
      Algebra.trdeg k T = Algebra.trdeg k P + Algebra.trdeg P T :=
        (trdeg_add_eq k P (A := T)).symm
      _ ≤ (4 : Cardinal) + 45 := add_le_add hPdim hTdim
      _ = 49 := by norm_num
  have hfalse := hlower.trans hupper
  norm_num at hfalse

end CubicTenVariables.GenericNormalAvoidance
