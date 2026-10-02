import TranslatedDepthSeven.ProjectiveDegreeTwoAlgebraBookkeeping
import TranslatedDepthSeven.ProjectiveHilbertCoefficientExtension
import TranslatedDepthSeven.FieldPolynomialKrullDimension
import TranslatedDepthSeven.CoefficientExtensionHomogeneousIdeal

/-!
# The degree-two linear-span bound used by the strict low-rank branch

This file proves the degree-two instance needed in ambient projective space
`P^12`.  It does not assume the general projective degree--span theorem.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 20000000

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem rationalLinearPolynomial_isHomogeneous_internal
    (a : Fin 13 → ℚ) :
    (rationalLinearPolynomial a).IsHomogeneous 1 := by
  change (∑ i : Fin 13, C (a i) * X i).IsHomogeneous 1
  apply MvPolynomial.IsHomogeneous.sum Finset.univ _ 1
  intro i _hi
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

private theorem rationalLinearPolynomial_coefficients_internal
    (f : MvPolynomial (Fin 13) ℚ) (hf : f.IsHomogeneous 1) :
    rationalLinearPolynomial
        (fun i ↦ (MvPolynomial.pderiv i f).coeff 0) = f := by
  have heuler : ∑ i : Fin 13, X i * pderiv i f = f := by
    simpa using hf.sum_X_mul_pderiv
  have hderiv : ∀ i : Fin 13,
      pderiv i f = C ((pderiv i f).coeff 0) := by
    intro i
    apply MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
    exact (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 13)).mpr
      (by simpa using hf.pderiv (i := i))
  rw [rationalLinearPolynomial]
  calc
    (∑ i : Fin 13, C ((pderiv i f).coeff 0) * X i) =
        ∑ i : Fin 13, X i * C ((pderiv i f).coeff 0) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact mul_comm _ _
    _ = ∑ i : Fin 13, X i * pderiv i f := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact congrArg (fun q ↦ X i * q) (hderiv i).symm
    _ = f := heuler

/-- Rank-nullity for literal rational linear forms and the degree-one
homogeneous quotient piece. -/
theorem finrank_rationalLinearFormsInIdeal_add_quotientDegreeOne_eq
    (I : Ideal (MvPolynomial (Fin 13) ℚ)) :
    Module.finrank ℚ (rationalLinearFormsInIdeal I) +
      Module.finrank ℚ
        (quotientHomogeneousComponent ℚ (Fin 13) I 1) = 13 := by
  let H := MvPolynomial.homogeneousSubmodule (Fin 13) ℚ 1
  let Q := quotientHomogeneousComponent ℚ (Fin 13) I 1
  let linH : (Fin 13 → ℚ) →ₗ[ℚ] H :=
    rationalLinearPolynomial.codRestrict H
      rationalLinearPolynomial_isHomogeneous_internal
  let q : (Fin 13 → ℚ) →ₗ[ℚ] Q :=
    (quotientHomogeneousComponentMap ℚ (Fin 13) I 1).comp linH
  have hqsurj : Function.Surjective q := by
    intro x
    obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.mp x.property
    let a : Fin 13 → ℚ := fun i ↦ (MvPolynomial.pderiv i f).coeff 0
    refine ⟨a, ?_⟩
    apply Subtype.ext
    change Ideal.Quotient.mk I (rationalLinearPolynomial a) = x
    rw [rationalLinearPolynomial_coefficients_internal f hf]
    exact hfx
  have hqrange : LinearMap.range q = ⊤ := LinearMap.range_eq_top.mpr hqsurj
  have hqker : LinearMap.ker q = rationalLinearFormsInIdeal I := by
    ext a
    simp only [LinearMap.mem_ker, mem_rationalLinearFormsInIdeal_iff]
    constructor
    · intro ha
      have hav := congrArg Subtype.val ha
      change Ideal.Quotient.mk I (rationalLinearPolynomial a) = 0 at hav
      exact Ideal.Quotient.eq_zero_iff_mem.mp hav
    · intro ha
      apply Subtype.ext
      change Ideal.Quotient.mk I (rationalLinearPolynomial a) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  have hrankNullity := q.finrank_range_add_finrank_ker
  rw [hqrange, finrank_top, hqker, Module.finrank_fin_fun] at hrankNullity
  simpa only [Fintype.card_fin, add_comm] using hrankNullity

/-- A geometrically integral projective fourfold of degree two in `P^12`
has at least seven rational linear equations.  Only the literal `Qbar`
prime test is used; the general degree--span inequality is not assumed. -/
theorem seven_le_finrank_rationalLinearFormsInIdeal_of_degree_two_qbarPrime
    (I : Ideal (MvPolynomial (Fin 13) ℚ))
    (hIprime : I.IsPrime)
    (hIhomogeneous :
      I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ))
    (hprojective : HasProjectiveDimensionDegree I 4 2)
    (hQbarPrime :
      (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime) :
    7 ≤ Module.finrank ℚ (rationalLinearFormsInIdeal I) := by
  let Ibar : Ideal (MvPolynomial (Fin 13) Qbar) :=
    I.map (MvPolynomial.map (algebraMap ℚ Qbar))
  have hIbarPrime : Ibar.IsPrime := hQbarPrime
  have hIbarHomogeneous :
      Ibar.IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 13) Qbar) := by
    exact isHomogeneous_map_mvPolynomialMap
      (algebraMap ℚ Qbar) I hIhomogeneous
  have hprojectiveBar : HasProjectiveDimensionDegree Ibar 4 2 :=
    qbarHasProjectiveDimensionDegree_of_rational I hprojective hIbarPrime
  obtain ⟨Dbar⟩ := exists_homogeneousLinearNormalizationData
    13 Ibar hIbarPrime hIbarHomogeneous
  have hparameterCount : Dbar.parameterCount = 5 := by
    have hdim := Dbar.ringKrullDim_eq_parameterPolynomial
      13 Ibar hIbarPrime
    rw [ringKrullDim_mvPolynomial_fin_eq_of_field] at hdim
    have hdim' : (Dbar.parameterCount : WithBot ℕ∞) = 5 := by
      exact hdim.symm.trans hprojectiveBar.1
    exact_mod_cast hdim'
  have hgenericRank :
      let B := MvPolynomial (Fin Dbar.parameterCount) Qbar
      let A := MvPolynomial (Fin 13) Qbar ⧸ Ibar
      letI : Algebra B A := Dbar.hom.toRingHom.toAlgebra
      Module.finrank (FractionRing B)
        (LocalizedModule (nonZeroDivisors B) A) ≤ 2 :=
    normalization_genericRank_le_projectiveDegree_fourfold_field
      Qbar Ibar Dbar hparameterCount hprojectiveBar
  have hbar : Module.finrank Qbar
      (quotientHomogeneousComponent Qbar (Fin 13) Ibar 1) ≤ 6 := by
    have h :=
      finrank_quotientHomogeneousComponent_one_le_succ_parameterCount_of_rank_le_two
        Qbar Ibar hIbarPrime hIbarHomogeneous Dbar hgenericRank
    rw [hparameterCount] at h
    norm_num at h ⊢
    exact h
  have htransport := projectiveHilbertPiece_finrank_map_eq
    (K := ℚ) (L := Qbar) 12 1 I
  have hrat : Module.finrank ℚ
      (quotientHomogeneousComponent ℚ (Fin 13) I 1) ≤ 6 := by
    have htransport' : Module.finrank Qbar
        (quotientHomogeneousComponent Qbar (Fin 13) Ibar 1) =
          Module.finrank ℚ
            (quotientHomogeneousComponent ℚ (Fin 13) I 1) := by
      simpa only [Published.projectiveHilbertPiece, Ibar] using htransport
    rw [← htransport']
    exact hbar
  have hsum := finrank_rationalLinearFormsInIdeal_add_quotientDegreeOne_eq I
  omega

/-- The exact degree-at-most-two form used downstream.  The degree-one case
is the already formalized finite-birational argument; the degree-two case is
the internal quadratic argument above. -/
theorem two_le_finrank_rationalLinearFormsInIdeal_of_degree_le_two_qbarPrime
    (I : Ideal (MvPolynomial (Fin 13) ℚ))
    (hIprime : I.IsPrime)
    (hIhomogeneous :
      I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ))
    (D : HomogeneousLinearNormalizationData I)
    (hparameterCount : D.parameterCount = 5)
    {d : ℕ} (hprojective : HasProjectiveDimensionDegree I 4 d)
    (hd : d ≤ 2)
    (hQbarPrime :
      (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime) :
    2 ≤ Module.finrank ℚ (rationalLinearFormsInIdeal I) := by
  have hdpos : 0 < d := hprojective.2.1
  interval_cases d
  · exact (by omega : 2 ≤ 8).trans
      (eight_le_finrank_rationalLinearFormsInIdeal_of_degree_one
        I hIprime hIhomogeneous D hparameterCount hprojective)
  · exact (by omega : 2 ≤ 7).trans
      (seven_le_finrank_rationalLinearFormsInIdeal_of_degree_two_qbarPrime
        I hIprime hIhomogeneous hprojective hQbarPrime)

/-- Uniform bounded-height codimension-two rational spaces for a fixed
finite family in the exact degree-at-most-two, `Qbar`-prime situation. -/
theorem exists_uniform_twoRow_linearSpan_of_finite_degreeAtMostTwo_qbarPrime
    {alpha : Type*} (components : Finset alpha)
    (ideal : alpha → Ideal (MvPolynomial (Fin 13) ℚ))
    (normalization : ∀ Q : alpha,
      HomogeneousLinearNormalizationData (ideal Q))
    (degree : alpha → ℕ)
    (hprime : ∀ Q ∈ components, (ideal Q).IsPrime)
    (hhomogeneous : ∀ Q ∈ components,
      (ideal Q).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ))
    (hparameterCount : ∀ Q ∈ components,
      (normalization Q).parameterCount = 5)
    (hprojective : ∀ Q ∈ components,
      HasProjectiveDimensionDegree (ideal Q) 4 (degree Q))
    (hdegree : ∀ Q ∈ components, degree Q ≤ 2)
    (hQbarPrime : ∀ Q ∈ components,
      ((ideal Q).map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime) :
    ∃ C : ℕ, ∀ Q ∈ components,
      ∃ v : Fin 2 → Fin 13 → ℚ,
        LinearIndependent ℚ v ∧
        (rationalLinearFormMatrix v).rank = 2 ∧
        (∀ i, rationalMatrixRowLinearPolynomial
          (rationalLinearFormMatrix v) i ∈ ideal Q) ∧
        rationalProjectiveLinearHeight
          (rationalLinearFormMatrix v) ≤ C := by
  apply exists_uniform_twoRow_linearSpan_of_finite components ideal
  intro Q hQ
  exact two_le_finrank_rationalLinearFormsInIdeal_of_degree_le_two_qbarPrime
    (ideal Q) (hprime Q hQ) (hhomogeneous Q hQ)
      (normalization Q) (hparameterCount Q hQ)
      (hprojective Q hQ) (hdegree Q hQ) (hQbarPrime Q hQ)

end

end TranslatedDepthSeven
