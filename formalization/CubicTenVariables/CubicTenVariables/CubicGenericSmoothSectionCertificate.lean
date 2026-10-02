import CubicTenVariables.CubicJacobianSectionReduction
import CubicTenVariables.PolynomialMatrixRankSpreading
import CubicTenVariables.GenericNormalTupleRank

/-! # A fixed-equation polynomial certificate for smooth linear sections

The final premise is a literal generic augmented-Jacobian rank condition,
over an algebraically closed field containing the integral parameter ring.
Generic normal rank is proved by a displayed minor. Polynomial rank
spreading produces a single nonzero
integer parameter polynomial. Every tuple where it stays nonzero satisfies
the existing geometric Jacobian predicate, including over the algebraic
closure of the specialized coefficient field. No degree bound or generic
smoothness theorem is assumed to have been proved here.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace CubicTenVariables.CubicGenericSmoothSectionCertificate
open MvPolynomial ProjectiveLinearSectionJacobian ProjectiveLinearSectionVariance
open CubicJacobianSectionReduction PolynomialMatrixRankSpreading

abbrev ParameterRing := MvPolynomial (Fin 50) ℤ

/-- The fifty actual coefficients of the five ordered normal rows. -/
def genericNormal : Matrix (Fin 5) (Fin 10) ParameterRing :=
  fun j i ↦ X (finProdFinEquiv (j, i))

private def normalPolynomialMatrix :
    Matrix (Fin 5) (Fin 10) (MvPolynomial (Fin 10) ParameterRing) :=
  fun j i ↦ C (genericNormal j i)

private def sectionEquations (F : MvPolynomial (Fin 10) ℤ) :
    Fin 6 → MvPolynomial (Fin 10) ParameterRing :=
  Fin.cons (MvPolynomial.map C F)
    (fun j ↦ ∑ i, C (genericNormal j i) * X i)

private def augmentedPolynomialMatrix (F : MvPolynomial (Fin 10) ℤ) :
    Matrix (Fin 6) (Fin 10) (MvPolynomial (Fin 10) ParameterRing) :=
  Fin.cons (fun i ↦ pderiv i (MvPolynomial.map C F)) normalPolynomialMatrix

private theorem evaluated_normal {K : Type*} [Field K]
    (ρ : ParameterRing →+* K) (x : Fin 10 → K) :
    evaluatedMatrix ρ x normalPolynomialMatrix = genericNormal.map ρ := by
  ext j i
  exact eval₂Hom_C ρ x (genericNormal j i)

private theorem evaluated_augmented {K : Type*} [Field K]
    (ρ : ParameterRing →+* K) (x : Fin 10 → K) (F : MvPolynomial (Fin 10) ℤ) :
    evaluatedMatrix ρ x (augmentedPolynomialMatrix F) =
      augmentedSectionJacobian (MvPolynomial.map (ρ.comp C) F) (genericNormal.map ρ) x := by
  ext j i
  refine Fin.cases ?_ (fun j ↦ ?_) j
  · simp [evaluatedMatrix, augmentedPolynomialMatrix, augmentedSectionJacobian,
      pderiv_map, eval_map]
  · simp [evaluatedMatrix, augmentedPolynomialMatrix, augmentedSectionJacobian,
      normalPolynomialMatrix, Matrix.map]

private theorem evaluated_equations_iff {K : Type*} [Field K]
    (ρ : ParameterRing →+* K) (x : Fin 10 → K) (F : MvPolynomial (Fin 10) ℤ) :
    (∀ e, eval₂Hom ρ x (sectionEquations F e) = 0) ↔
      eval x (MvPolynomial.map (ρ.comp C) F) = 0 ∧ (genericNormal.map ρ).mulVec x = 0 := by
  have hfirst : eval₂Hom ρ x (sectionEquations F 0) =
      eval x (MvPolynomial.map (ρ.comp C) F) := by
    simp [sectionEquations, eval_map]
  have hrow (j : Fin 5) : eval₂Hom ρ x (sectionEquations F j.succ) =
      (genericNormal.map ρ).mulVec x j := by
    simp [sectionEquations, Matrix.mulVec, dotProduct, Matrix.map]
  constructor
  · intro h
    refine ⟨hfirst ▸ h 0, ?_⟩
    ext j
    exact (hrow j).symm.trans (h j.succ)
  · rintro ⟨hF, hγ⟩ e
    refine Fin.cases ?_ (fun j ↦ ?_) e
    · exact hfirst.trans hF
    · exact (hrow j).trans (congrFun hγ j)

/-- Generic normal and Jacobian ranks spread to every field specialization
on one actual nonzero principal open of the integral parameter space. -/
theorem exists_nonzero_rank_certificate
    {Ω : Type*} [Field Ω] [IsAlgClosed Ω]
    (F : MvPolynomial (Fin 10) ℤ) (ι : ParameterRing →+* Ω)
    (hι : Function.Injective ι) (hrank : (genericNormal.map ι).rank = 5)
    (hjac : ∀ x : Fin 10 → Ω, x ≠ 0 →
      eval x (MvPolynomial.map (ι.comp C) F) = 0 →
      (genericNormal.map ι).mulVec x = 0 →
      (augmentedSectionJacobian (MvPolynomial.map (ι.comp C) F)
        (genericNormal.map ι) x).rank = 6) :
    ∃ Δ : ParameterRing, Δ ≠ 0 ∧
      ∀ (K : Type*) [Field K] (ρ : ParameterRing →+* K), ρ Δ ≠ 0 →
        (genericNormal.map ρ).rank = 5 ∧
        ∀ x : Fin 10 → K, x ≠ 0 →
          eval x (MvPolynomial.map (ρ.comp C) F) = 0 →
          (genericNormal.map ρ).mulVec x = 0 →
          (augmentedSectionJacobian (MvPolynomial.map (ρ.comp C) F)
            (genericNormal.map ρ) x).rank = 6 := by
  classical
  let noEquations : Fin 0 → MvPolynomial (Fin 10) ParameterRing := Fin.elim0
  obtain ⟨s₀, hs₀, hnormal⟩ := PolynomialMatrixRankSpreading.exists_nonzero_open
    ι hι noEquations 1 normalPolynomialMatrix (by
      intro x _ _
      simpa only [evaluated_normal, Fintype.card_fin] using hrank)
  have hchart (j : Fin 10) := PolynomialMatrixRankSpreading.exists_nonzero_open
    ι hι (sectionEquations F) (X j) (augmentedPolynomialMatrix F) (by
      intro x hG hX
      obtain ⟨hF, hγ⟩ := (evaluated_equations_iff ι x F).mp hG
      have hxj : x j ≠ 0 := by simpa only [eval₂Hom_X'] using hX
      have hx : x ≠ 0 := by intro hz; apply hxj; simp [hz]
      simpa only [evaluated_augmented, Fintype.card_fin] using hjac x hx hF hγ)
  choose s hs hgood using hchart
  refine ⟨s₀ * ∏ j, s j, mul_ne_zero hs₀ (Finset.prod_ne_zero_iff.mpr (fun j _ ↦ hs j)), ?_⟩
  intro K _ ρ hΔ
  have hprod : ρ s₀ * ∏ j, ρ (s j) ≠ 0 := by simpa only [map_mul, map_prod] using hΔ
  have hnormalρ := hnormal K ρ (mul_ne_zero_iff.mp hprod).1 (fun _ ↦ 0)
    (fun e ↦ Fin.elim0 e) (by simp)
  refine ⟨by simpa only [evaluated_normal, Fintype.card_fin] using hnormalρ, ?_⟩
  intro x hx hF hγ
  have hj : ∃ j : Fin 10, x j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  obtain ⟨j, hxj⟩ := hj
  have hsj : ρ (s j) ≠ 0 := Finset.prod_ne_zero_iff.mp
    (mul_ne_zero_iff.mp hprod).2 j (Finset.mem_univ j)
  have hg := hgood j K ρ hsj x ((evaluated_equations_iff ρ x F).mpr ⟨hF, hγ⟩)
    (by simpa only [eval₂Hom_X'] using hxj)
  simpa only [evaluated_augmented, Fintype.card_fin] using hg

/-- Evaluating the fifty coefficient variables recovers the supplied
ordered tuple, with exactly the existing flattening convention. -/
theorem genericNormal_specialize {K : Type*} [Field K]
    (γ : Fin 5 → Fin 10 → K) :
    genericNormal.map (eval₂Hom (Int.castRingHom K) (normalTupleCoordinates γ)) = γ := by
  ext j i
  simp [genericNormal, Matrix.map, normalTupleCoordinates]

/-- The specialized certificate guarantees the literal existing geometric
Jacobian predicate. Its one nonzero polynomial depends on the fixed
integer equation; no uniform elimination-degree estimate is asserted. -/
theorem exists_nonzero_goodJacobian_certificate
    {Ω : Type*} [Field Ω] [IsAlgClosed Ω]
    (F : MvPolynomial (Fin 10) ℤ) (ι : ParameterRing →+* Ω)
    (hι : Function.Injective ι)
    (hjac : ∀ x : Fin 10 → Ω, x ≠ 0 →
      eval x (MvPolynomial.map (ι.comp C) F) = 0 →
      (genericNormal.map ι).mulVec x = 0 →
      (augmentedSectionJacobian (MvPolynomial.map (ι.comp C) F)
        (genericNormal.map ι) x).rank = 6) :
    ∃ Δ : MvPolynomial (Fin 50) ℤ, Δ ≠ 0 ∧
      ∀ (K : Type) [Field K] (γ : Fin 5 → Fin 10 → K),
        eval (normalTupleCoordinates γ) (MvPolynomial.map (Int.castRingHom K) Δ) ≠ 0 →
        GoodJacobianTuple (MvPolynomial.map (Int.castRingHom K) F) γ := by
  have hrank : (genericNormal.map ι).rank = 5 :=
    GenericNormalTupleRank.rank_map_genericNormalMatrix (k := 5) (n := 10) ι hι (by decide)
  obtain ⟨Δ, hΔ, hgood⟩ := exists_nonzero_rank_certificate F ι hι hrank hjac
  refine ⟨Δ, hΔ, ?_⟩
  intro K _ γ hγ
  let ρ : ParameterRing →+* K := eval₂Hom (Int.castRingHom K) (normalTupleCoordinates γ)
  have hρ : ρ Δ ≠ 0 := by simpa only [eval_map] using hγ
  have hΓ : genericNormal.map ρ = γ := genericNormal_specialize γ
  have hnormal := (hgood K ρ hρ).1
  refine ⟨by simpa only [hΓ] using hnormal, ?_⟩
  intro x hx hF hrows
  let ρbar : ParameterRing →+* AlgebraicClosure K := (algebraMap K (AlgebraicClosure K)).comp ρ
  have hρbar : ρbar Δ ≠ 0 :=
    (map_ne_zero_iff (algebraMap K (AlgebraicClosure K))
      (algebraMap K (AlgebraicClosure K)).injective).mpr hρ
  have hΓbar : genericNormal.map ρbar =
      Matrix.map γ (algebraMap K (AlgebraicClosure K)) := by
    rw [← hΓ]
    ext j i
    rfl
  have hFbar : MvPolynomial.map (ρbar.comp C) F =
      MvPolynomial.map (algebraMap K (AlgebraicClosure K))
        (MvPolynomial.map (Int.castRingHom K) F) := by
    rw [MvPolynomial.map_map]
    exact congrArg (fun ψ : ℤ →+* AlgebraicClosure K ↦ MvPolynomial.map ψ F)
      (Subsingleton.elim _ _)
  have h := (hgood (AlgebraicClosure K) ρbar hρbar).2 x hx
    (by simpa only [hFbar] using hF) (by simpa only [hΓbar] using hrows)
  simpa only [hFbar, hΓbar] using h

end CubicTenVariables.CubicGenericSmoothSectionCertificate
