import TranslatedDepthSeven.DepthSevenJacobianExceptionalLocus
import TranslatedDepthSeven.HomogeneousLinearElimination
import TranslatedDepthSeven.AffineZeroLocusQuotientPoints
import TranslatedDepthSeven.ExplicitLineContribution
import TranslatedDepthSeven.StrictRootTheorem
import TranslatedDepthSeven.CharacteristicPolynomialHeight
import TranslatedDepthSeven.IntegralHomogeneousIdealModel
import TranslatedDepthSeven.HomogeneousMinimalComponents
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Integral box counts from a homogeneous linear normalization

A finite homogeneous linear normalization gives a completely elementary
integral-point bound.  After clearing the rational coefficients of its
degree-one forms, their values on an integral box lie in an integral box of
the same dimension.  Module-finiteness bounds every fibre over `ℚ`, not
only fibres over finite fields.

The resulting bound is uniform over every affine congruence rescaling
`x = x₀ + m z`: equality of the normalization forms on two displacement
vectors is equivalent to equality on their affine images.  The constants
depend on the fixed normalization, while the power of the displacement box
does not depend on `x₀` or `m`.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 200000

local instance classicalDecidablePred {A : Type*} (p : A → Prop) :
    DecidablePred p := Classical.decPred p

universe u v w

/-- A homogeneous polynomial of degree zero is its constant coefficient. -/
theorem eq_C_coeff_zero_of_isHomogeneous_zero
    {R : Type u} {N : ℕ} [CommSemiring R]
    {f : MvPolynomial (Fin N) R} (hf : f.IsHomogeneous 0) :
    f = MvPolynomial.C (f.coeff 0) := by
  apply MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
  exact (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin N)).mpr hf

/-- Evaluation of a degree-one homogeneous polynomial is additive in the
point and commutes with scalar multiplication of the point. -/
theorem eval_add_smul_of_isHomogeneous_one
    {R : Type u} {N : ℕ} [CommRing R]
    (f : MvPolynomial (Fin N) R) (hf : f.IsHomogeneous 1)
    (x z : Fin N → R) (a : R) :
    MvPolynomial.eval (fun i ↦ x i + a * z i) f =
      MvPolynomial.eval x f + a * MvPolynomial.eval z f := by
  have heuler : ∑ i : Fin N, X i * pderiv i f = f := by
    simpa using hf.sum_X_mul_pderiv
  have hderiv : ∀ i : Fin N,
      pderiv i f = C ((pderiv i f).coeff 0) := by
    intro i
    apply eq_C_coeff_zero_of_isHomogeneous_zero
    simpa using hf.pderiv (i := i)
  have heulerC :
      ∑ i : Fin N, X i * C ((pderiv i f).coeff 0) = f := by
    calc
      ∑ i : Fin N, X i * C ((pderiv i f).coeff 0) =
          ∑ i : Fin N, X i * pderiv i f := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact congrArg (fun q ↦ X i * q) (hderiv i).symm
      _ = f := heuler
  have heval (y : Fin N → R) :
      MvPolynomial.eval y f =
        ∑ i : Fin N, y i * (pderiv i f).coeff 0 := by
    calc
      MvPolynomial.eval y f =
          MvPolynomial.eval y
            (∑ i : Fin N, X i * C ((pderiv i f).coeff 0)) :=
        congrArg (MvPolynomial.eval y) heulerC.symm
      _ = ∑ i : Fin N, y i * (pderiv i f).coeff 0 := by
        simp only [map_sum, map_mul, eval_X, eval_C]
  rw [heval, heval, heval]
  simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

/-- Rational evaluation of a cleared polynomial is the common denominator
times evaluation of the original polynomial. -/
theorem intCast_eval_clearRationalMvPolynomial
    {N : ℕ} (f : MvPolynomial (Fin N) ℚ) (z : Fin N → ℤ) :
    ((MvPolynomial.eval z (clearRationalMvPolynomial f) : ℤ) : ℚ) =
      (mvPolynomialRationalCommonDenominator f : ℚ) *
        MvPolynomial.eval (fun i ↦ (z i : ℚ)) f := by
  calc
    ((MvPolynomial.eval z (clearRationalMvPolynomial f) : ℤ) : ℚ) =
        MvPolynomial.eval (fun i ↦ (z i : ℚ))
          (MvPolynomial.map (Int.castRingHom ℚ)
            (clearRationalMvPolynomial f)) := by
      simpa [Function.comp_def] using
        (MvPolynomial.map_eval (Int.castRingHom ℚ) z
          (clearRationalMvPolynomial f))
    _ = MvPolynomial.eval (fun i ↦ (z i : ℚ))
          (C (mvPolynomialRationalCommonDenominator f : ℚ) * f) := by
      rw [map_clearRationalMvPolynomial]
    _ = (mvPolynomialRationalCommonDenominator f : ℚ) *
          MvPolynomial.eval (fun i ↦ (z i : ℚ)) f := by simp

/-- Clearing denominators does not change equality of the evaluations of a
fixed rational polynomial. -/
theorem eval_clearRationalMvPolynomial_eq_iff
    {N : ℕ} (f : MvPolynomial (Fin N) ℚ) (z z' : Fin N → ℤ) :
    MvPolynomial.eval z (clearRationalMvPolynomial f) =
        MvPolynomial.eval z' (clearRationalMvPolynomial f) ↔
      MvPolynomial.eval (fun i ↦ (z i : ℚ)) f =
        MvPolynomial.eval (fun i ↦ (z' i : ℚ)) f := by
  have hD : (mvPolynomialRationalCommonDenominator f : ℚ) ≠ 0 := by
    exact_mod_cast (mvPolynomialRationalCommonDenominator_pos f).ne'
  constructor
  · intro h
    have hcast := congrArg (fun a : ℤ ↦ (a : ℚ)) h
    change ((MvPolynomial.eval z (clearRationalMvPolynomial f) : ℤ) : ℚ) =
      ((MvPolynomial.eval z' (clearRationalMvPolynomial f) : ℤ) : ℚ) at hcast
    rw [intCast_eval_clearRationalMvPolynomial,
      intCast_eval_clearRationalMvPolynomial] at hcast
    exact mul_left_cancel₀ hD hcast
  · intro h
    have hcast :
        ((MvPolynomial.eval z (clearRationalMvPolynomial f) : ℤ) : ℚ) =
          ((MvPolynomial.eval z' (clearRationalMvPolynomial f) : ℤ) : ℚ) := by
      rw [intCast_eval_clearRationalMvPolynomial,
        intCast_eval_clearRationalMvPolynomial, h]
    exact_mod_cast hcast

/-- The literal integral projection attached to the rational degree-one
forms of a homogeneous linear normalization. -/
def integralHomogeneousLinearNormalizationProjection
    {N : ℕ} {I : Ideal (MvPolynomial (Fin N) ℚ)}
    (D : HomogeneousLinearNormalizationData I)
    (z : IntVector N) : IntVector D.parameterCount :=
  fun i ↦ MvPolynomial.eval z (clearRationalMvPolynomial (D.forms i))

/-- A fixed coefficient constant controlling every cleared normalization
form. -/
def homogeneousLinearNormalizationProjectionConstant
    {N : ℕ} {I : Ideal (MvPolynomial (Fin N) ℚ)}
    (D : HomogeneousLinearNormalizationData I) : ℕ :=
  Finset.univ.sup fun i : Fin D.parameterCount ↦
    (clearRationalMvPolynomial (D.forms i)).support.card *
      mvPolynomialCoefficientNatAbsMax
        (clearRationalMvPolynomial (D.forms i))

/-- The integral normalization projection of a box of radius `T` lies in a
box whose radius is a fixed constant times `max 1 T`. -/
theorem integralHomogeneousLinearNormalizationProjection_coordinate_le
    {N : ℕ} {I : Ideal (MvPolynomial (Fin N) ℚ)}
    (D : HomogeneousLinearNormalizationData I)
    (z : IntVector N) (T : ℕ) (hz : ∀ j, (z j).natAbs ≤ T)
    (i : Fin D.parameterCount) :
    (integralHomogeneousLinearNormalizationProjection D z i).natAbs ≤
      homogeneousLinearNormalizationProjectionConstant D * max 1 T := by
  let g : MvPolynomial (Fin N) ℤ :=
    clearRationalMvPolynomial (D.forms i)
  have hcoeff : ∀ m ∈ g.support,
      (g.coeff m).natAbs ≤ mvPolynomialCoefficientNatAbsMax g := by
    intro m hm
    exact coeff_natAbs_le_mvPolynomialCoefficientNatAbsMax g hm
  have hdegree : g.totalDegree ≤ 1 := by
    exact (clearRationalMvPolynomial_isHomogeneous
      (D.forms_isHomogeneous i)).totalDegree_le
  have heval := eval_natAbs_le_support_mul_coeff_mul_pow_generic
    g z hcoeff hdegree hz
  have hconstant : g.support.card * mvPolynomialCoefficientNatAbsMax g ≤
      homogeneousLinearNormalizationProjectionConstant D := by
    exact Finset.le_sup (s := Finset.univ)
      (f := fun i : Fin D.parameterCount ↦
        (clearRationalMvPolynomial (D.forms i)).support.card *
          mvPolynomialCoefficientNatAbsMax
            (clearRationalMvPolynomial (D.forms i))) (Finset.mem_univ i)
  change (MvPolynomial.eval z g).natAbs ≤ _
  have heval' : (MvPolynomial.eval z g).natAbs ≤
      g.support.card * mvPolynomialCoefficientNatAbsMax g * max 1 T := by
    simpa using heval
  exact heval'.trans (Nat.mul_le_mul_right (max 1 T) hconstant)

/-- Distinct algebra homomorphisms from a finite-dimensional algebra to an
arbitrary field are linearly independent; hence a displayed spanning family
bounds their number.  No finiteness assumption on the target field is used. -/
theorem natCard_algHom_over_base_le_of_span_fin_anyField
    (B : Type u) (K : Type v) (A : Type w) (D : ℕ)
    [CommRing B] [Field K] [CommRing A]
    [Algebra B K] [Algebra B A]
    (s : Fin D → A)
    (hs : Submodule.span B (Set.range s) = ⊤) :
    Nat.card (A →ₐ[B] K) ≤ D := by
  letI : Module.Finite B A := Module.finite_def.mpr <|
    Submodule.fg_iff_exists_fin_generating_family.mpr ⟨D, s, hs⟩
  letI : Module.Finite K (K ⊗[B] A) := Module.Finite.base_change B K A
  calc
    Nat.card (A →ₐ[B] K) ≤ Nat.card ((K ⊗[B] A) →ₐ[K] K) :=
      Nat.card_le_card_of_injective _
        (baseChangeLiftAlgHom_injective B K A)
    _ ≤ Module.finrank K (K ⊗[B] A) :=
      card_algHom_le_finrank K (K ⊗[B] A) K
    _ ≤ D := finrank_scalarFibre_le_of_span_fin B K A D s hs

/-- Arbitrary-field version of the restriction-fibre estimate for one
displayed finite module-generating family. -/
theorem natCard_restrictionFibre_le_of_span_fin_anyField
    (k : Type u) (B : Type v) (A : Type w) (K : Type*) (D : ℕ)
    [CommSemiring k] [CommRing B] [CommRing A] [Field K]
    [Algebra k B] [Algebra k A] [Algebra k K]
    (g : B →ₐ[k] A) (phi : B →ₐ[k] K) (s : Fin D → A)
    (hs :
      letI : Algebra B A := g.toRingHom.toAlgebra
      Submodule.span B (Set.range s) = ⊤) :
    Nat.card {psi : A →ₐ[k] K // psi.comp g = phi} ≤ D := by
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : Algebra B K := phi.toRingHom.toAlgebra
  rw [Nat.card_congr (restrictionFibreAlgHomEquiv k B A K g phi)]
  exact natCard_algHom_over_base_le_of_span_fin_anyField B K A D s hs

/-- A homogeneous linear normalization has a single finite bound for every
fibre of restriction on rational points.  The bound is the size of one
displayed module-generating family. -/
theorem exists_uniform_restrictionFibre_bound_of_homogeneousLinearNormalization
    {N : ℕ} {I : Ideal (MvPolynomial (Fin N) ℚ)}
    (D : HomogeneousLinearNormalizationData I) :
    ∃ E : ℕ, ∀ phi : MvPolynomial (Fin D.parameterCount) ℚ →ₐ[ℚ] ℚ,
      Nat.card {psi : (MvPolynomial (Fin N) ℚ ⧸ I) →ₐ[ℚ] ℚ //
        psi.comp D.hom = phi} ≤ E := by
  let B := MvPolynomial (Fin D.parameterCount) ℚ
  let A := MvPolynomial (Fin N) ℚ ⧸ I
  let g : B →ₐ[ℚ] A := D.hom
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : Module.Finite B A := D.hom_finite
  obtain ⟨E, s, hs⟩ := Module.Finite.exists_fin (R := B) (M := A)
  refine ⟨E, fun phi ↦ ?_⟩
  exact natCard_restrictionFibre_le_of_span_fin_anyField
    ℚ B A ℚ E g phi s hs

/-- A degree-one homogeneous form is affine-linear along the literal
integral rescaling `x₀ + m z`, with no constant term in the displacement. -/
theorem eval_integralAffineMap_of_isHomogeneous_one
    {N : ℕ} (f : MvPolynomial (Fin N) ℚ)
    (hf : f.IsHomogeneous 1) (x₀ z : IntVector N) (m : ℕ) :
    MvPolynomial.eval
        (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) f =
      MvPolynomial.eval (fun i ↦ (x₀ i : ℚ)) f +
        (m : ℚ) * MvPolynomial.eval (fun i ↦ (z i : ℚ)) f := by
  simpa [integralAffineMap, Nat.cast_ofNat] using
    eval_add_smul_of_isHomogeneous_one f hf
      (fun i ↦ (x₀ i : ℚ)) (fun i ↦ (z i : ℚ)) (m : ℚ)

/-- Equality of the integral normalization projections of two displacement
vectors implies equality of the restricted rational points after every
common affine rescaling. -/
theorem quotientPoint_comp_normalization_eq_of_integralProjection_eq
    {N : ℕ} {I : Ideal (MvPolynomial (Fin N) ℚ)}
    (D : HomogeneousLinearNormalizationData I)
    (x₀ z z' : IntVector N) (m : ℕ)
    (hz : (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
      affineIdealZeroLocus I)
    (hz' : (fun i ↦ (integralAffineMap x₀ z' m i : ℚ)) ∈
      affineIdealZeroLocus I)
    (hprojection :
      integralHomogeneousLinearNormalizationProjection D z =
        integralHomogeneousLinearNormalizationProjection D z') :
    (affineIdealPointToQuotientAlgHom I ⟨_, hz⟩).comp D.hom =
      (affineIdealPointToQuotientAlgHom I ⟨_, hz'⟩).comp D.hom := by
  apply MvPolynomial.algHom_ext
  intro i
  have hcleared :
      MvPolynomial.eval z
          (clearRationalMvPolynomial (D.forms i)) =
        MvPolynomial.eval z'
          (clearRationalMvPolynomial (D.forms i)) := by
    exact congrFun hprojection i
  have hforms :
      MvPolynomial.eval (fun j ↦ (z j : ℚ)) (D.forms i) =
        MvPolynomial.eval (fun j ↦ (z' j : ℚ)) (D.forms i) :=
    (eval_clearRationalMvPolynomial_eq_iff (D.forms i) z z').mp hcleared
  simp only [AlgHom.comp_apply, HomogeneousLinearNormalizationData.hom,
    MvPolynomial.aeval_X, Ideal.Quotient.mkₐ_eq_mk,
    affineIdealPointToQuotientAlgHom_apply_mk]
  change MvPolynomial.eval
      (fun j ↦ (integralAffineMap x₀ z m j : ℚ)) (D.forms i) =
    MvPolynomial.eval
      (fun j ↦ (integralAffineMap x₀ z' m j : ℚ)) (D.forms i)
  rw [eval_integralAffineMap_of_isHomogeneous_one
      (D.forms i) (D.forms_isHomogeneous i),
    eval_integralAffineMap_of_isHomogeneous_one
      (D.forms i) (D.forms_isHomogeneous i), hforms]

/-- Evaluation on the quotient remembers the original integral
displacement whenever the affine scale is positive. -/
theorem quotientPoint_of_integralAffineMap_injective
    {N : ℕ} (I : Ideal (MvPolynomial (Fin N) ℚ))
    (x₀ : IntVector N) {m : ℕ} (hm : 0 < m)
    (z z' : IntVector N)
    (hz : (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
      affineIdealZeroLocus I)
    (hz' : (fun i ↦ (integralAffineMap x₀ z' m i : ℚ)) ∈
      affineIdealZeroLocus I)
    (heval : affineIdealPointToQuotientAlgHom I ⟨_, hz⟩ =
      affineIdealPointToQuotientAlgHom I ⟨_, hz'⟩) :
    z = z' := by
  have hpoint :
      (⟨(fun i ↦ (integralAffineMap x₀ z m i : ℚ)), hz⟩ :
        {y : Fin N → ℚ // y ∈ affineIdealZeroLocus I}) =
      ⟨(fun i ↦ (integralAffineMap x₀ z' m i : ℚ)), hz'⟩ := by
    exact (affineIdealZeroLocusEquivQuotientAlgHom I).injective heval
  have hmap : integralAffineMap x₀ z m = integralAffineMap x₀ z' m := by
    funext i
    have hi := congrFun (congrArg Subtype.val hpoint) i
    change ((integralAffineMap x₀ z m i : ℤ) : ℚ) =
      ((integralAffineMap x₀ z' m i : ℤ) : ℚ) at hi
    exact_mod_cast hi
  exact integralAffineMap_injective hm x₀ hmap

/-- Every fibre of the integral normalization projection, restricted to
displacements whose affine images lie on the fixed ideal, has cardinality
bounded by the module-theoretic restriction-fibre constant. -/
theorem integralNormalizationProjection_fibre_card_le
    {N : ℕ} {I : Ideal (MvPolynomial (Fin N) ℚ)}
    (D : HomogeneousLinearNormalizationData I) (E : ℕ)
    (hE : ∀ phi : MvPolynomial (Fin D.parameterCount) ℚ →ₐ[ℚ] ℚ,
      Nat.card {psi : (MvPolynomial (Fin N) ℚ ⧸ I) →ₐ[ℚ] ℚ //
        psi.comp D.hom = phi} ≤ E)
    (points : Finset (IntVector N)) (x₀ : IntVector N)
    {m : ℕ} (hm : 0 < m)
    (hzero : ∀ z ∈ points,
      (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
        affineIdealZeroLocus I)
    (v : IntVector D.parameterCount) :
    (points.filter fun z ↦
      integralHomogeneousLinearNormalizationProjection D z = v).card ≤ E := by
  classical
  let S := points.filter fun z ↦
    integralHomogeneousLinearNormalizationProjection D z = v
  by_cases hS : S.Nonempty
  · obtain ⟨z₁, hz₁⟩ := hS
    have hz₁points : z₁ ∈ points := (Finset.mem_filter.mp hz₁).1
    have hz₁projection :
        integralHomogeneousLinearNormalizationProjection D z₁ = v :=
      (Finset.mem_filter.mp hz₁).2
    let pointHom (z : IntVector N) (hz : z ∈ points) :
        (MvPolynomial (Fin N) ℚ ⧸ I) →ₐ[ℚ] ℚ :=
      affineIdealPointToQuotientAlgHom I
        ⟨(fun i ↦ (integralAffineMap x₀ z m i : ℚ)), hzero z hz⟩
    let phi : MvPolynomial (Fin D.parameterCount) ℚ →ₐ[ℚ] ℚ :=
      (pointHom z₁ hz₁points).comp D.hom
    let fibre := {psi : (MvPolynomial (Fin N) ℚ ⧸ I) →ₐ[ℚ] ℚ //
      psi.comp D.hom = phi}
    let embed : S → fibre := fun z ↦
      ⟨pointHom z.1 (Finset.mem_filter.mp z.2).1,
        quotientPoint_comp_normalization_eq_of_integralProjection_eq
          D x₀ z.1 z₁ m
          (hzero z.1 (Finset.mem_filter.mp z.2).1)
          (hzero z₁ hz₁points)
          ((Finset.mem_filter.mp z.2).2.trans hz₁projection.symm)⟩
    have hembed : Function.Injective embed := by
      intro z z' hzz'
      apply Subtype.ext
      apply quotientPoint_of_integralAffineMap_injective I x₀ hm
        z.1 z'.1
        (hzero z.1 (Finset.mem_filter.mp z.2).1)
        (hzero z'.1 (Finset.mem_filter.mp z'.2).1)
      exact congrArg Subtype.val hzz'
    let B := MvPolynomial (Fin D.parameterCount) ℚ
    let A := MvPolynomial (Fin N) ℚ ⧸ I
    let g : B →ₐ[ℚ] A := D.hom
    let algBA : Algebra B A := g.toRingHom.toAlgebra
    letI : Algebra B A := algBA
    letI : Module B A := algBA.toModule
    let finiteBA : Module.Finite B A := D.hom_finite
    letI : Module.Finite B A := finiteBA
    let algBQ : Algebra B ℚ := phi.toRingHom.toAlgebra
    letI : Algebra B ℚ := algBQ
    letI : Module B ℚ := algBQ.toModule
    letI : Module.Finite ℚ (ℚ ⊗[B] A) :=
      @Module.Finite.base_change B ℚ A _ _ algBQ _ algBA.toModule finiteBA
    letI : Finite ((ℚ ⊗[B] A) →ₐ[ℚ] ℚ) := by infer_instance
    letI : Finite (A →ₐ[B] ℚ) :=
      Finite.of_injective (baseChangeLiftAlgHom B ℚ A)
        (baseChangeLiftAlgHom_injective B ℚ A)
    letI : Finite fibre :=
      Finite.of_equiv (A →ₐ[B] ℚ)
        (restrictionFibreAlgHomEquiv ℚ B A ℚ g phi).symm
    have hcard : Nat.card S ≤ Nat.card fibre :=
      Nat.card_le_card_of_injective embed hembed
    calc
      S.card = Nat.card S := by simp [Nat.card_eq_fintype_card]
      _ ≤ Nat.card fibre := hcard
      _ ≤ E := hE phi
  · simp only [Finset.not_nonempty_iff_eq_empty] at hS
    simp [S, hS]

/-- Elementary translated-box count furnished by a homogeneous linear
normalization.  The constant is independent of the translation `x₀`, the
positive scale `m`, the finite point set, and its box radius `T`. -/
theorem exists_card_le_of_homogeneousLinearNormalization
    {N : ℕ} {I : Ideal (MvPolynomial (Fin N) ℚ)}
    (D : HomogeneousLinearNormalizationData I) :
    ∃ E : ℕ, ∀ (points : Finset (IntVector N)) (x₀ : IntVector N)
      (m T : ℕ), 0 < m →
      (∀ z ∈ points, ∀ i, (z i).natAbs ≤ T) →
      (∀ z ∈ points,
        (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
          affineIdealZeroLocus I) →
      points.card ≤
        (2 * (homogeneousLinearNormalizationProjectionConstant D * max 1 T) + 1) ^
            D.parameterCount * E := by
  obtain ⟨E, hE⟩ :=
    exists_uniform_restrictionFibre_bound_of_homogeneousLinearNormalization D
  refine ⟨E, ?_⟩
  intro points x₀ m T hm hbox hzero
  apply finiteSet_card_le_fibre_mul_integerBox points
    (integralHomogeneousLinearNormalizationProjection D)
    (homogeneousLinearNormalizationProjectionConstant D * max 1 T) E
  · intro z hz i
    exact integralHomogeneousLinearNormalizationProjection_coordinate_le
      D z T (hbox z hz) i
  · intro v
    exact integralNormalizationProjection_fibre_card_le
      D E hE points x₀ hm hzero v

/-- If the normalization uses at most four parameters, its elementary box
count is `O(T⁴)`, uniformly in the translation and positive affine scale.
This is stronger than the `O(T^(4+ε))` estimate needed in the analytic
application. -/
theorem exists_card_le_mul_fourthPower_of_parameterCount_le_four
    {N : ℕ} {I : Ideal (MvPolynomial (Fin N) ℚ)}
    (D : HomogeneousLinearNormalizationData I)
    (hparameters : D.parameterCount ≤ 4) :
    ∃ K : ℕ, ∀ (points : Finset (IntVector N)) (x₀ : IntVector N)
      (m T : ℕ), 0 < m → 1 ≤ T →
      (∀ z ∈ points, ∀ i, (z i).natAbs ≤ T) →
      (∀ z ∈ points,
        (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
          affineIdealZeroLocus I) →
      points.card ≤ K * T ^ 4 := by
  obtain ⟨E, hcount⟩ := exists_card_le_of_homogeneousLinearNormalization D
  let C := homogeneousLinearNormalizationProjectionConstant D
  refine ⟨(2 * C + 1) ^ 4 * E, ?_⟩
  intro points x₀ m T hm hT hbox hzero
  have hraw := hcount points x₀ m T hm hbox hzero
  rw [max_eq_right hT] at hraw
  have hbase : 2 * (C * T) + 1 ≤ (2 * C + 1) * T := by
    calc
      2 * (C * T) + 1 ≤ 2 * (C * T) + T :=
        Nat.add_le_add_left hT (2 * (C * T))
      _ = (2 * C + 1) * T := by ring
  calc
    points.card ≤ (2 * (C * T) + 1) ^ D.parameterCount * E := hraw
    _ ≤ ((2 * C + 1) * T) ^ D.parameterCount * E :=
      Nat.mul_le_mul_right E
        (Nat.pow_le_pow_left hbase D.parameterCount)
    _ ≤ ((2 * C + 1) * T) ^ 4 * E :=
      Nat.mul_le_mul_right E
        (Nat.pow_le_pow_right (by positivity) hparameters)
    _ = ((2 * C + 1) ^ 4 * E) * T ^ 4 := by ring

/-- General exponent form of the same elementary count. -/
theorem exists_card_le_mul_power_of_parameterCount_le
    {N e : ℕ} {I : Ideal (MvPolynomial (Fin N) ℚ)}
    (D : HomogeneousLinearNormalizationData I)
    (hparameters : D.parameterCount ≤ e) :
    ∃ K : ℕ, ∀ (points : Finset (IntVector N)) (x₀ : IntVector N)
      (m T : ℕ), 0 < m → 1 ≤ T →
      (∀ z ∈ points, ∀ i, (z i).natAbs ≤ T) →
      (∀ z ∈ points,
        (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
          affineIdealZeroLocus I) →
      points.card ≤ K * T ^ e := by
  obtain ⟨E, hcount⟩ := exists_card_le_of_homogeneousLinearNormalization D
  let C := homogeneousLinearNormalizationProjectionConstant D
  refine ⟨(2 * C + 1) ^ e * E, ?_⟩
  intro points x₀ m T hm hT hbox hzero
  have hraw := hcount points x₀ m T hm hbox hzero
  rw [max_eq_right hT] at hraw
  have hbase : 2 * (C * T) + 1 ≤ (2 * C + 1) * T := by
    calc
      2 * (C * T) + 1 ≤ 2 * (C * T) + T :=
        Nat.add_le_add_left hT (2 * (C * T))
      _ = (2 * C + 1) * T := by ring
  calc
    points.card ≤ (2 * (C * T) + 1) ^ D.parameterCount * E := hraw
    _ ≤ ((2 * C + 1) * T) ^ D.parameterCount * E :=
      Nat.mul_le_mul_right E
        (Nat.pow_le_pow_left hbase D.parameterCount)
    _ ≤ ((2 * C + 1) * T) ^ e * E :=
      Nat.mul_le_mul_right E
        (Nat.pow_le_pow_right (by positivity) hparameters)
    _ = ((2 * C + 1) ^ e * E) * T ^ e := by
      rw [mul_pow]
      ac_rfl

/-- A finite injective normalization has fewer than `d` parameters whenever
the target ring has Krull dimension strictly below the natural number `d`.
This variant avoids choosing an equality witness for that dimension. -/
theorem normalization_parameter_lt_of_ringKrullDim_lt_nat
    {k : Type u} [Field k] {s d : ℕ} {A : Type v}
    [CommRing A] [Nontrivial A] [Algebra k A]
    (g : MvPolynomial (Fin s) k →ₐ[k] A)
    (hinjective : Function.Injective g) (hintegral : g.IsIntegral)
    (hdim : ringKrullDim A < d) :
    s < d := by
  letI : Algebra (MvPolynomial (Fin s) k) A :=
    g.toRingHom.toAlgebra
  letI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A :=
    ⟨hintegral⟩
  have hdimension :
      ringKrullDim A = ringKrullDim (MvPolynomial (Fin s) k) :=
    ringKrullDim_eq_of_isIntegral_injective hinjective
  have hlower :=
    ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial
      (R := k) (Fin s)
  simp only [ringKrullDim_eq_zero_of_field, zero_add, Nat.card_fin] at hlower
  rw [← hdimension] at hlower
  have hstrict := lt_of_le_of_lt hlower hdim
  exact_mod_cast hstrict

/-! ## Homogeneity and finite components of the Jacobian exceptional locus -/

/-- A square polynomial matrix whose entries in row `i` all have degree
`d i` has homogeneous determinant of degree `∑ i, d i`. -/
theorem matrix_det_isHomogeneous_of_row_isHomogeneous
    {k : Type u} [CommRing k] {N r : ℕ}
    (M : Matrix (Fin r) (Fin r) (MvPolynomial (Fin N) k))
    (d : Fin r → ℕ)
    (hM : ∀ i j, (M i j).IsHomogeneous (d i)) :
    M.det.IsHomogeneous (∑ i, d i) := by
  classical
  rw [Matrix.det_apply]
  apply IsHomogeneous.sum Finset.univ _ _
  intro σ _hσ
  have hp : (∏ i, M (σ i) i).IsHomogeneous (∑ i, d (σ i)) := by
    exact IsHomogeneous.prod Finset.univ (fun i ↦ M (σ i) i)
      (fun i ↦ d (σ i)) (fun i _hi ↦ hM (σ i) i)
  rw [Equiv.sum_comp σ d] at hp
  simpa only [Units.smul_def] using
    (homogeneousSubmodule (Fin N) k (∑ i, d i)).toAddSubgroup.zsmul_mem
      hp (↑(Equiv.Perm.sign σ) : ℤ)

/-- Every displayed Jacobian minor of a finite homogeneous equation family
is itself homogeneous; the row degrees may be different. -/
theorem finiteEquationJacobianMinor_exists_isHomogeneous
    {k : Type u} [Field k] {N r : ℕ}
    (equations : Finset (MvPolynomial (Fin N) k))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    (rows : Fin r → {f // f ∈ equations}) (cols : Fin r → Fin N) :
    ∃ d : ℕ,
      (finiteEquationJacobianMinor equations rows cols).IsHomogeneous d := by
  choose degree hdegree using fun i : Fin r ↦
    hhomogeneous (rows i).1 (rows i).2
  refine ⟨∑ i : Fin r, (degree i - 1), ?_⟩
  simpa only [finiteEquationJacobianMinor] using
    (matrix_det_isHomogeneous_of_row_isHomogeneous
      (finiteEquationJacobianMinorMatrix equations rows cols)
      (fun i ↦ degree i - 1)
      (fun i j ↦ (hdegree i).pderiv (i := cols j)))

/-- The original homogeneous equations together with every displayed
depth-seven Jacobian minor remain a literal finite homogeneous family. -/
theorem depthSevenJacobianExceptionalEquationFinset_each_isHomogeneous
    {k : Type u} [Field k] {N : ℕ}
    (equations : Finset (MvPolynomial (Fin N) k))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    (g : MvPolynomial (Fin N) k)
    (hg : g ∈ depthSevenJacobianExceptionalEquationFinset equations) :
    ∃ d : ℕ, g.IsHomogeneous d := by
  classical
  rcases Finset.mem_union.mp hg with hg | hg
  · exact hhomogeneous g hg
  · obtain ⟨C, rfl⟩ :=
      (mem_depthSevenJacobianMinorPolynomialFinset_iff equations g).mp hg
    exact finiteEquationJacobianMinor_exists_isHomogeneous
      equations hhomogeneous C.rows C.cols

/-- Each irreducible component of the finite homogeneous Jacobian
exceptional family is represented by an actual homogeneous prime ideal. -/
theorem exceptionalMinimalPrime_isHomogeneous
    {k : Type u} [Field k] {N : ℕ}
    (equations : Finset (MvPolynomial (Fin N) k))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    {Q : Ideal (MvPolynomial (Fin N) k)}
    (hQ : Q ∈ finiteMinimalPrimes
      (depthSevenJacobianExceptionalIdeal equations)) :
    Q.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin N) k) := by
  apply finiteEquationMinimalPrime_isHomogeneous
    (depthSevenJacobianExceptionalEquationFinset equations)
    (depthSevenJacobianExceptionalEquationFinset_each_isHomogeneous
      equations hhomogeneous)
  simpa [finiteEquationMinimalPrimes, finiteEquationIdeal,
    depthSevenJacobianExceptionalIdeal] using hQ

/-- The literal exceptional zero set is exactly the union of the zero sets
of the finitely many minimal primes of its augmented ideal. -/
theorem mem_exceptional_iff_exists_minimalPrime
    {k : Type u} [Field k] {N : ℕ}
    (equations : Finset (MvPolynomial (Fin N) k)) (z : Fin N → k) :
    z ∈ finiteAffineCommonZeroLocus
        (depthSevenJacobianExceptionalEquationFinset equations) ↔
      ∃ Q ∈ finiteMinimalPrimes
          (depthSevenJacobianExceptionalIdeal equations),
        z ∈ affineIdealZeroLocus Q := by
  constructor
  · intro hz
    obtain ⟨Q, hQ⟩ :=
      finiteEquationComponentsThroughPoint_nonempty_of_mem
        (depthSevenJacobianExceptionalEquationFinset equations) z hz
    have hQspec :=
      (mem_finiteEquationComponentsThroughPoint_iff
        (depthSevenJacobianExceptionalEquationFinset equations) z Q).mp hQ
    refine ⟨Q, ?_, ?_⟩
    · simpa [finiteEquationMinimalPrimes, finiteEquationIdeal,
        depthSevenJacobianExceptionalIdeal] using hQspec.1
    · exact hQspec.2
  · rintro ⟨Q, hQ, hzQ⟩
    intro f hf
    exact hzQ f <|
      (le_of_mem_finiteMinimalPrimes hQ) (Ideal.subset_span hf)

/-- Finite-set form of the component cover: counting a literal exceptional
point set reduces to summing any valid bounds for the finitely many actual
minimal-prime components. -/
theorem exceptionalDisplacement_card_le_sum_componentBounds
    {N : ℕ} (equations : Finset (MvPolynomial (Fin N) ℚ))
    (points : Finset (IntVector N)) (x₀ : IntVector N) (m : ℕ)
    (bound : Ideal (MvPolynomial (Fin N) ℚ) → ℕ)
    (hbound : ∀ Q ∈ finiteMinimalPrimes
        (depthSevenJacobianExceptionalIdeal equations),
      (points.filter fun z ↦
        (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
          affineIdealZeroLocus Q).card ≤ bound Q) :
    (points.filter fun z ↦
      (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
        finiteAffineCommonZeroLocus
          (depthSevenJacobianExceptionalEquationFinset equations)).card ≤
      ∑ Q ∈ finiteMinimalPrimes
        (depthSevenJacobianExceptionalIdeal equations), bound Q := by
  classical
  let components := finiteMinimalPrimes
    (depthSevenJacobianExceptionalIdeal equations)
  let componentPoints := fun Q : Ideal (MvPolynomial (Fin N) ℚ) ↦
    points.filter fun z ↦
      (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
        affineIdealZeroLocus Q
  have hsubset :
      points.filter (fun z ↦
        (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
          finiteAffineCommonZeroLocus
            (depthSevenJacobianExceptionalEquationFinset equations)) ⊆
        components.biUnion componentPoints := by
    intro z hz
    have hzspec := Finset.mem_filter.mp hz
    obtain ⟨Q, hQ, hzQ⟩ :=
      (mem_exceptional_iff_exists_minimalPrime equations _).mp hzspec.2
    apply Finset.mem_biUnion.mpr
    refine ⟨Q, hQ, ?_⟩
    exact Finset.mem_filter.mpr ⟨hzspec.1, hzQ⟩
  calc
    (points.filter fun z ↦
        (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
          finiteAffineCommonZeroLocus
            (depthSevenJacobianExceptionalEquationFinset equations)).card ≤
        (components.biUnion componentPoints).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ Q ∈ components, (componentPoints Q).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ Q ∈ components, bound Q := by
      exact Finset.sum_le_sum fun Q hQ ↦ hbound Q hQ

/-- Uniform translated-box count for the entire Jacobian exceptional locus.
If the original prime has affine-cone dimension `s` and `s ≤ e+1`, every
proper exceptional component has a homogeneous normalization with at most
`e` parameters.  Summing the finite component bounds gives `O(T^e)`.

In particular, `e = 4` requires the original affine-cone dimension to be at
most five.  Starting from dimension six, properness alone gives only the
specialization `e = 5`. -/
theorem exists_exceptionalDisplacement_card_le_mul_power
    {N s e : ℕ} (equations : Finset (MvPolynomial (Fin N) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    (P : Ideal (MvPolynomial (Fin N) ℚ)) [P.IsPrime]
    (hP : Ideal.span (equations : Set (MvPolynomial (Fin N) ℚ)) = P)
    (C : DepthSevenJacobianChartIndex equations) (hD : C.determinant ∉ P)
    (hPdim : ringKrullDim (MvPolynomial (Fin N) ℚ ⧸ P) = s)
    (hs : s ≤ e + 1) :
    ∃ K : ℕ, ∀ (points : Finset (IntVector N)) (x₀ : IntVector N)
      (m T : ℕ), 0 < m → 1 ≤ T →
      (∀ z ∈ points, ∀ i, (z i).natAbs ≤ T) →
      (points.filter fun z ↦
        (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
          finiteAffineCommonZeroLocus
            (depthSevenJacobianExceptionalEquationFinset equations)).card ≤
        K * T ^ e := by
  classical
  let components := finiteMinimalPrimes
    (depthSevenJacobianExceptionalIdeal equations)
  let Component := {Q : Ideal (MvPolynomial (Fin N) ℚ) // Q ∈ components}
  have hEach : ∀ Q : Component, ∃ K : ℕ,
      ∀ (points : Finset (IntVector N)) (x₀ : IntVector N)
        (m T : ℕ), 0 < m → 1 ≤ T →
        (∀ z ∈ points, ∀ i, (z i).natAbs ≤ T) →
        (∀ z ∈ points,
          (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
            affineIdealZeroLocus Q.1) →
        points.card ≤ K * T ^ e := by
    intro Q
    have hQ : Q.1 ∈ finiteMinimalPrimes
        (depthSevenJacobianExceptionalIdeal equations) := Q.2
    letI : Q.1.IsPrime := isPrime_of_mem_finiteMinimalPrimes hQ
    have hQhom := exceptionalMinimalPrime_isHomogeneous
      equations hhomogeneous hQ
    obtain ⟨D⟩ := exists_homogeneousLinearNormalizationData N Q.1
      (isPrime_of_mem_finiteMinimalPrimes hQ) hQhom
    have hQdim : ringKrullDim (MvPolynomial (Fin N) ℚ ⧸ Q.1) < s :=
      ringKrullDim_exceptionalMinimalPrime_lt_nat_of_determinant_notMem
        P Q.1 hP C hD hQ hPdim
    have hparameterlt : D.parameterCount < s :=
      normalization_parameter_lt_of_ringKrullDim_lt_nat
        D.hom D.hom_injective D.hom_finite.to_isIntegral hQdim
    have hparameter : D.parameterCount ≤ e := by omega
    exact exists_card_le_mul_power_of_parameterCount_le D hparameter
  choose componentConstant hcomponentConstant using hEach
  let bound : Ideal (MvPolynomial (Fin N) ℚ) → ℕ := fun Q ↦
    if hQ : Q ∈ components then componentConstant ⟨Q, hQ⟩ else 0
  refine ⟨∑ Q ∈ components, bound Q, ?_⟩
  intro points x₀ m T hm hT hbox
  have hcomponentBound : ∀ Q ∈ components,
      (points.filter fun z ↦
        (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
          affineIdealZeroLocus Q).card ≤ bound Q * T ^ e := by
    intro Q hQ
    have hlocal := hcomponentConstant ⟨Q, hQ⟩
      (points.filter fun z ↦
        (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
          affineIdealZeroLocus Q)
      x₀ m T hm hT
      (by
        intro z hz i
        exact hbox z (Finset.mem_filter.mp hz).1 i)
      (by
        intro z hz
        exact (Finset.mem_filter.mp hz).2)
    simpa [bound, hQ] using hlocal
  have hcover := exceptionalDisplacement_card_le_sum_componentBounds
    equations points x₀ m (fun Q ↦ bound Q * T ^ e) hcomponentBound
  calc
    (points.filter fun z ↦
        (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
          finiteAffineCommonZeroLocus
            (depthSevenJacobianExceptionalEquationFinset equations)).card ≤
        ∑ Q ∈ components, bound Q * T ^ e := hcover
    _ = (∑ Q ∈ components, bound Q) * T ^ e := by
      rw [Finset.sum_mul]

/-- Dimension-five specialization: a proper homogeneous Jacobian
exceptional locus is uniformly `O(T⁴)` in every positive affine rescaling. -/
theorem exists_exceptionalDisplacement_card_le_mul_fourthPower_of_dim_five
    {N : ℕ} (equations : Finset (MvPolynomial (Fin N) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    (P : Ideal (MvPolynomial (Fin N) ℚ)) [P.IsPrime]
    (hP : Ideal.span (equations : Set (MvPolynomial (Fin N) ℚ)) = P)
    (C : DepthSevenJacobianChartIndex equations) (hD : C.determinant ∉ P)
    (hPdim : ringKrullDim (MvPolynomial (Fin N) ℚ ⧸ P) = 5) :
    ∃ K : ℕ, ∀ (points : Finset (IntVector N)) (x₀ : IntVector N)
      (m T : ℕ), 0 < m → 1 ≤ T →
      (∀ z ∈ points, ∀ i, (z i).natAbs ≤ T) →
      (points.filter fun z ↦
        (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
          finiteAffineCommonZeroLocus
            (depthSevenJacobianExceptionalEquationFinset equations)).card ≤
        K * T ^ 4 := by
  exact exists_exceptionalDisplacement_card_le_mul_power
    (s := 5) (e := 4) equations hhomogeneous P hP C hD hPdim (by omega)

/-- Dimension-six specialization available from properness alone.  It has
power five, not power four. -/
theorem exists_exceptionalDisplacement_card_le_mul_fifthPower_of_dim_six
    {N : ℕ} (equations : Finset (MvPolynomial (Fin N) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    (P : Ideal (MvPolynomial (Fin N) ℚ)) [P.IsPrime]
    (hP : Ideal.span (equations : Set (MvPolynomial (Fin N) ℚ)) = P)
    (C : DepthSevenJacobianChartIndex equations) (hD : C.determinant ∉ P)
    (hPdim : ringKrullDim (MvPolynomial (Fin N) ℚ ⧸ P) = 6) :
    ∃ K : ℕ, ∀ (points : Finset (IntVector N)) (x₀ : IntVector N)
      (m T : ℕ), 0 < m → 1 ≤ T →
      (∀ z ∈ points, ∀ i, (z i).natAbs ≤ T) →
      (points.filter fun z ↦
        (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
          finiteAffineCommonZeroLocus
            (depthSevenJacobianExceptionalEquationFinset equations)).card ≤
        K * T ^ 5 := by
  exact exists_exceptionalDisplacement_card_le_mul_power
    (s := 6) (e := 5) equations hhomogeneous P hP C hD hPdim (by omega)

end

end TranslatedDepthSeven
