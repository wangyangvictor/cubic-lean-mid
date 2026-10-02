import TranslatedDepthSeven.HomogeneousChartPolynomialEmbedding
import TranslatedDepthSeven.PrimeAffineDimensionTranscendence
import TranslatedDepthSeven.SpecializedProjectiveSurfaceJacobianCover

/-!
# The Krull dimension of a nonempty projective affine chart

The cone domain `A` embeds in `R[T]`, where `R` is the chart domain.
This extension is algebraic: `T` is the image of the homogenizing coordinate,
and each chart coordinate `z_i` satisfies `T*z_i = image(X_i)`.
Transcendence-degree addition therefore identifies
`trdeg R + 1 = trdeg A`.  The internally proved affine dimension theorem
then gives exactly the projective dimension on the chart.

No dimension statement about projective charts or graded localizations is
assumed in this argument.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

universe u

/-- The polynomial ring over the chart has the same transcendence degree
as the cone domain.  The map is injective and algebraic, not asserted finite. -/
theorem trdeg_optionChartPolynomial_eq_cone
    {K : Type u} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Option (Fin n)) K))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Option (Fin n)) K))
    (hprime : I.IsPrime)
    (hX : MvPolynomial.X (none : Option (Fin n)) ∉ I) :
    Algebra.trdeg K (Polynomial (MvPolynomial (Fin n) K ⧸
        I.map multivariateDehomogenization.toRingHom)) =
      Algebra.trdeg K (MvPolynomial (Option (Fin n)) K ⧸ I) := by
  let J := I.map multivariateDehomogenization.toRingHom
  let A := MvPolynomial (Option (Fin n)) K ⧸ I
  let R := MvPolynomial (Fin n) K ⧸ J
  letI : I.IsPrime := hprime
  letI : J.IsPrime := map_multivariateDehomogenization_isPrime I hI hprime hX
  let g : A →ₐ[K] Polynomial R := optionConeChartPolynomialEmbedding I hI hprime hX
  letI : Algebra A (Polynomial R) := g.toRingHom.toAlgebra
  letI : IsScalarTower K A (Polynomial R) :=
    IsScalarTower.of_algebraMap_eq fun c ↦ by
      change algebraMap K (Polynomial R) c = g (algebraMap K A c)
      exact (g.commutes c).symm
  letI : FaithfulSMul A (Polynomial R) :=
    (faithfulSMul_iff_algebraMap_injective A (Polynomial R)).mpr
      (optionConeChartPolynomialEmbedding_injective I hI hprime hX)
  have hnone : g (Ideal.Quotient.mk I (MvPolynomial.X none)) =
      Polynomial.X := by
    change homogeneousScalingHom (optionChartQuotientEvaluation I)
      (MvPolynomial.X none) = Polynomial.X
    simp [homogeneousScalingHom,
      optionChartQuotientEvaluation, multivariateDehomogenization]
  have hsome (i : Fin n) : g (Ideal.Quotient.mk I (MvPolynomial.X (some i))) =
      Polynomial.X * Polynomial.C (Ideal.Quotient.mk J (MvPolynomial.X i)) := by
    change homogeneousScalingHom (optionChartQuotientEvaluation I)
      (MvPolynomial.X (some i)) = _
    simp [homogeneousScalingHom,
      optionChartQuotientEvaluation, multivariateDehomogenization, J]
  have hT : IsAlgebraic A (Polynomial.X : Polynomial R) := by
    have h := isAlgebraic_algebraMap (R := A) (A := Polynomial R)
      (Ideal.Quotient.mk I (MvPolynomial.X none))
    change IsAlgebraic A (g (Ideal.Quotient.mk I (MvPolynomial.X none))) at h
    rwa [hnone] at h
  have hz (i : Fin n) : IsAlgebraic A
      (Polynomial.C (Ideal.Quotient.mk J (MvPolynomial.X i))) := by
    have h := isAlgebraic_algebraMap (R := A) (A := Polynomial R)
      (Ideal.Quotient.mk I (MvPolynomial.X (some i)))
    change IsAlgebraic A (g (Ideal.Quotient.mk I (MvPolynomial.X (some i)))) at h
    rw [hsome] at h
    exact IsAlgebraic.of_mul
      (mem_nonZeroDivisors_of_ne_zero Polynomial.X_ne_zero) hT h
  have hscalar (c : K) : IsAlgebraic A (algebraMap K (Polynomial R) c) := by
    rw [IsScalarTower.algebraMap_eq K A (Polynomial R)]
    exact isAlgebraic_algebraMap (R := A) (A := Polynomial R) (algebraMap K A c)
  have hcoefficient (a : R) : IsAlgebraic A (Polynomial.C a) := by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    induction f using MvPolynomial.induction_on with
    | C c =>
        change IsAlgebraic A (algebraMap K (Polynomial R) c)
        exact hscalar c
    | add f₁ f₂ hf₁ hf₂ =>
        simpa only [map_add] using hf₁.add hf₂
    | mul_X f i hf =>
        simpa only [map_mul] using hf.mul (hz i)
  letI : Algebra.IsAlgebraic A (Polynomial R) := ⟨by
    intro f
    induction f using Polynomial.induction_on' with
    | add f₁ f₂ hf₁ hf₂ => exact hf₁.add hf₂
    | monomial k a =>
        simpa only [Polynomial.C_mul_X_pow_eq_monomial] using
          (hcoefficient a).mul (hT.pow k)⟩
  have h := trdeg_add_eq K A (A := Polynomial R)
  simpa only [trdeg_eq_zero, add_zero] using h.symm

/-- Exact internal discharge of the affine-chart Krull-dimension premise.
All degree and dimension data are those of the original homogeneous ideal. -/
theorem projectivePrimeAffineChartKrullDimension_internal :
    StandardAG.ProjectivePrimeAffineChartKrullDimension := by
  intro N r d I hprime hI hX hprojective
  let E := MvPolynomial.renameEquiv ℚ (_root_.finSuccEquiv N)
  let I' : Ideal (MvPolynomial (Option (Fin N)) ℚ) := I.map E
  have hI'homogeneous : I'.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Option (Fin N)) ℚ) := by
    exact map_renameEquiv_isHomogeneous (_root_.finSuccEquiv N) I hI
  have hI'prime : I'.IsPrime := by
    letI : I.IsPrime := hprime
    dsimp only [I', E]
    infer_instance
  have hI'X : MvPolynomial.X (none : Option (Fin N)) ∉ I' := by
    intro hmem
    obtain ⟨f, hfI, hfeq⟩ :=
      (Ideal.mem_map_iff_of_surjective E E.surjective).mp hmem
    have hfX : f = MvPolynomial.X (0 : Fin (N + 1)) := by
      apply E.injective
      rw [hfeq]
      simp [E, MvPolynomial.renameEquiv_apply]
    exact hX (hfX ▸ hfI)
  let J := I'.map multivariateDehomogenization.toRingHom
  let R := MvPolynomial (Fin N) ℚ ⧸ J
  have hJprime : J.IsPrime :=
    map_multivariateDehomogenization_isPrime I' hI'homogeneous hI'prime hI'X
  letI : J.IsPrime := hJprime
  have hconeTrdeg : Algebra.trdeg ℚ (MvPolynomial (Option (Fin N)) ℚ ⧸ I') =
      ((r + 1 : ℕ) : Cardinal) := by
    rw [← (renameQuotientAlgEquiv ℚ (_root_.finSuccEquiv N) I).trdeg_eq]
    exact trdeg_eq_nat_of_primeAffine_ringKrullDim_eq ℚ I hprime
      (by simpa only [Nat.cast_add, Nat.cast_one] using hprojective.1)
  have hpolyTrdeg : Algebra.trdeg ℚ (Polynomial R) =
      ((r + 1 : ℕ) : Cardinal) :=
    (trdeg_optionChartPolynomial_eq_cone I' hI'homogeneous hI'prime hI'X).trans
      hconeTrdeg
  obtain ⟨s, _hsN, _g, _hginjective, _hgfinite, hsTrdeg⟩ :=
    exists_finite_injective_normalization_of_primeAffine_with_trdeg J
  have hs : s = r := by
    have h := trdeg_add_eq ℚ R (A := Polynomial R)
    rw [Polynomial.trdeg_of_isDomain, hpolyTrdeg] at h
    change Algebra.trdeg ℚ (MvPolynomial (Fin N) ℚ ⧸ J) + 1 =
      ((r + 1 : ℕ) : Cardinal) at h
    rw [hsTrdeg] at h
    have hn : s + 1 = r + 1 := by exact_mod_cast h
    omega
  have hdim := ringKrullDim_eq_nat_of_primeAffine_trdeg_eq ℚ J hJprime
    (by simpa only [hs] using hsTrdeg)
  have hJ : J = I.map rationalDehomogenizeAtZeroHom :=
    map_dehomogenization_map_finSuccRename I
  rw [hJ] at hdim
  exact hdim

end

end TranslatedDepthSeven
