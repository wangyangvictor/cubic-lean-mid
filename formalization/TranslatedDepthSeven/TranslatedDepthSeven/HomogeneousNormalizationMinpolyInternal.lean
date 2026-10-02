import TranslatedDepthSeven.FiniteNormalDomainMinpolyDerivativeInternal
import TranslatedDepthSeven.ProjectiveExteriorPointSeparatorInternal

/-!
# Homogeneous minimal polynomials in linear normalization coordinates

For a homogeneous degree-one element, the minimal polynomial over the
normal polynomial parameter ring is homogeneous when every parameter and
the polynomial variable have degree one.  Indeed, its component in the
monic degree is another monic annihilator of the same degree.  Minimality
identifies the two polynomials.

Combined with the generic-rank degree bound and characteristic-zero
separability, this supplies a degree-bounded equation with nonzero formal
derivative at the generic point.  Coordinate-basis transport, Jacobian
minors, and singular-locus containment are not asserted here.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
open scoped nonZeroDivisors

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 500000

/-- The homogeneous component in the monic degree is still monic of
that same degree, even when the original coefficients are inhomogeneous. -/
theorem monic_homogeneousComponent_optionEquivLeft
    {K : Type*} [Field K] {σ : Type*} [Finite σ]
    (p : Polynomial (MvPolynomial σ K)) (hp : p.Monic) :
    let q := optionEquivLeft K σ
      (homogeneousComponent p.natDegree ((optionEquivLeft K σ).symm p))
    q.Monic ∧ q.natDegree = p.natDegree := by
  let H := homogeneousComponent p.natDegree ((optionEquivLeft K σ).symm p)
  let q := optionEquivLeft K σ H
  have hHhom : H.IsHomogeneous p.natDegree := homogeneousComponent_isHomogeneous _ _
  have hHvalue : eval (affineChartVector (0 : σ → K)) H = 1 :=
    eval_affineChartZero_homogeneousComponent_monic p hp
  have hHne : H ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hHvalue
    exact zero_ne_one hHvalue
  have hcoeff : q.coeff p.natDegree = 1 := by
    have h := coeff_optionEquivLeft_degree_eq_C_eval_affineChartVector_zero
      H p.natDegree hHhom
    simpa only [hHvalue, map_one] using h
  have hdegree : q.natDegree ≤ p.natDegree := by
    rw [show q = optionEquivLeft K σ H from rfl, natDegree_optionEquivLeft]
    exact (degreeOf_le_totalDegree H none).trans_eq (hHhom.totalDegree hHne)
  have hdegreeEq : q.natDegree = p.natDegree :=
    le_antisymm hdegree (Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff]; exact one_ne_zero))
  exact ⟨Polynomial.monic_of_natDegree_le_of_coeff_eq_one _ hdegree hcoeff, hdegreeEq⟩

/-- With degree-one normalization parameters and a degree-one source
element, the minimal polynomial is homogeneous in the formal variables. -/
theorem minpoly_isHomogeneous_of_linearNormalization
    {K : Type*} [Field K] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hIprime : I.IsPrime)
    (hIhom : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K))
    (D : HomogeneousLinearNormalizationData I)
    (w : MvPolynomial (Fin (N + 1)) K) (hwhom : w.IsHomogeneous 1) :
    let B := MvPolynomial (Fin D.parameterCount) K
    let A := MvPolynomial (Fin (N + 1)) K ⧸ I
    letI : Algebra B A := D.hom.toRingHom.toAlgebra
    let x : A := Ideal.Quotient.mk I w
    ((optionEquivLeft K (Fin D.parameterCount)).symm (minpoly B x)).IsHomogeneous
      (minpoly B x).natDegree := by
  letI : I.IsPrime := hIprime
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial (Fin (N + 1)) K ⧸ I
  letI : Algebra B A := D.hom.toRingHom.toAlgebra
  letI : FaithfulSMul B A :=
    (faithfulSMul_iff_algebraMap_injective B A).mpr D.hom_injective
  haveI : Module.Finite B A := D.hom_finite
  let mk := Ideal.Quotient.mkₐ K I
  let x : A := mk w
  let p := minpoly B x
  have hx : IsIntegral B x := Algebra.IsIntegral.isIntegral x
  have hpmonic : p.Monic := minpoly.monic hx
  let l : Option (Fin D.parameterCount) → MvPolynomial (Fin (N + 1)) K :=
    fun i ↦ i.elim w D.forms
  have hl : ∀ i, (l i).IsHomogeneous 1 := by
    intro i
    cases i with
    | none => exact hwhom
    | some i => exact D.forms_isHomogeneous i
  have hcomposition : mk.comp (aeval l) =
      ((Polynomial.aeval x).restrictScalars K).comp
        (optionEquivLeft K (Fin D.parameterCount)).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | none =>
        simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
        change mk w = Polynomial.aeval x
          ((optionEquivLeft K (Fin D.parameterCount)) (X none))
        rw [optionEquivLeft_X_none, Polynomial.aeval_X]
    | some i =>
        simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
        change mk (D.forms i) = Polynomial.aeval x
          ((optionEquivLeft K (Fin D.parameterCount)) (X (some i)))
        rw [optionEquivLeft_X_some, Polynomial.aeval_C]
        change mk (D.forms i) = D.hom (X i)
        simp [HomogeneousLinearNormalizationData.hom, mk]
  let F := (optionEquivLeft K (Fin D.parameterCount)).symm p
  have hFmem : aeval l F ∈ I := by
    apply (Ideal.Quotient.eq_zero_iff_mem).1
    have h := DFunLike.congr_fun hcomposition F
    change mk (aeval l F) = Polynomial.aeval x
      ((optionEquivLeft K (Fin D.parameterCount)) F) at h
    have hroot : Polynomial.aeval x p = 0 := minpoly.aeval B x
    rw [show (optionEquivLeft K (Fin D.parameterCount)) F = p by
      simp only [F, AlgEquiv.apply_symm_apply], hroot] at h
    exact h
  let H := homogeneousComponent p.natDegree F
  let q := optionEquivLeft K (Fin D.parameterCount) H
  have hHmem : aeval l H ∈ I := by
    have h := hIhom p.natDegree hFmem
    change (MvPolynomial.decomposition.decompose' (aeval l F) p.natDegree :
      MvPolynomial (Fin (N + 1)) K) ∈ I at h
    rw [MvPolynomial.decomposition.decompose'_apply,
      homogeneousComponent_aeval_degreeOne l hl] at h
    exact h
  have hqroot : Polynomial.aeval x q = 0 := by
    have h := DFunLike.congr_fun hcomposition H
    change mk (aeval l H) = Polynomial.aeval x q at h
    rw [← h]
    exact (Ideal.Quotient.eq_zero_iff_mem).2 hHmem
  have hq : q.Monic ∧ q.natDegree = p.natDegree :=
    monic_homogeneousComponent_optionEquivLeft p hpmonic
  have hqp : q = p :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le hpmonic hq.1
      (minpoly.isIntegrallyClosed_dvd hx hqroot) hq.2.le
  have hHF : H = F := by
    apply (optionEquivLeft K (Fin D.parameterCount)).injective
    simpa only [F, AlgEquiv.apply_symm_apply] using hqp
  change F.IsHomogeneous p.natDegree
  rw [← hHF]
  exact homogeneousComponent_isHomogeneous _ _

/-- A degree-one source element has a homogeneous monic equation of
degree at most the actual projective degree, with nonzero formal
derivative in the source domain.  No coordinate-complement assumption is
needed for this algebraic assertion. -/
theorem exists_bounded_homogeneous_normalization_equation_with_nonzero_derivative
    {K : Type*} [Field K] [CharZero K] {N r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hIprime : I.IsPrime)
    (hIhom : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K))
    (hdegree : HasProjectiveDimensionDegree I r d)
    (D : HomogeneousLinearNormalizationData I)
    (w : MvPolynomial (Fin (N + 1)) K) (hwhom : w.IsHomogeneous 1) :
    let B := MvPolynomial (Fin D.parameterCount) K
    let A := MvPolynomial (Fin (N + 1)) K ⧸ I
    letI : Algebra B A := D.hom.toRingHom.toAlgebra
    let x : A := Ideal.Quotient.mk I w
    ∃ p : Polynomial B,
      p.Monic ∧ p.natDegree ≤ d ∧
      ((optionEquivLeft K (Fin D.parameterCount)).symm p).IsHomogeneous p.natDegree ∧
      Polynomial.aeval x p = 0 ∧
      Polynomial.aeval x (Polynomial.derivative p) ≠ 0 := by
  letI : I.IsPrime := hIprime
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial (Fin (N + 1)) K ⧸ I
  letI : Algebra B A := D.hom.toRingHom.toAlgebra
  letI : FaithfulSMul B A :=
    (faithfulSMul_iff_algebraMap_injective B A).mpr D.hom_injective
  haveI : Module.Finite B A := D.hom_finite
  let x : A := Ideal.Quotient.mk I w
  have hx : IsIntegral B x := Algebra.IsIntegral.isIntegral x
  refine ⟨minpoly B x, minpoly.monic hx, ?_, ?_, minpoly.aeval B x, ?_⟩
  · exact (minpoly_natDegree_le_localized_rank x).trans
      (homogeneousLinearNormalization_genericRank_le_projectiveDegree I hIprime D hdegree).2
  · exact minpoly_isHomogeneous_of_linearNormalization I hIprime hIhom D w hwhom
  · exact minpoly_aeval_derivative_ne_zero_of_finite_normal_domain x

end

end TranslatedDepthSeven
