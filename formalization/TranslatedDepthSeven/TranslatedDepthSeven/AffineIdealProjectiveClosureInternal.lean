import TranslatedDepthSeven.HomogeneousConeStandardChart
import TranslatedDepthSeven.ProjectiveAffineChartDimensionInternal

/-!
# The homogeneous projective closure of a prime affine ideal

For an affine ideal `J`, substitute `X_i \mapsto T X_i` after passing to
the affine quotient.  The kernel is the homogeneous ideal of the projective
closure.  This file proves directly that its standard chart is exactly `J`.
For a prime affine ideal its consecutive-coordinate version is prime,
homogeneous, avoids `X₀`, and has the same dimension and degree as `J` in
the projective convention.

No projective-closure or saturation theorem is assumed.  Geometric
primality after arbitrary coefficient extension is deliberately separate:
the statements below are the same-field algebra needed for the bounded
affine-chart projection theorem.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 500000

universe u

variable {K : Type u} [Field K]

/-- Option-indexed homogeneous closure of an affine ideal.  The variable
`none` is the homogenizing coordinate. -/
def affineIdealHomogeneousClosure {n : ℕ}
    (J : Ideal (MvPolynomial (Fin n) K)) :
    Ideal (MvPolynomial (Option (Fin n)) K) :=
  RingHom.ker
    (homogeneousScalingHom
      ((Ideal.Quotient.mkₐ K J).comp multivariateDehomogenization)).toRingHom

/-- The homogeneous closure is prime whenever the affine ideal is prime. -/
theorem affineIdealHomogeneousClosure_isPrime
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) K)) (hJ : J.IsPrime) :
    (affineIdealHomogeneousClosure J).IsPrime := by
  letI : J.IsPrime := hJ
  exact RingHom.ker_isPrime _

/-- The kernel construction is homogeneous, coefficient by coefficient in
the new polynomial variable. -/
theorem affineIdealHomogeneousClosure_isHomogeneous
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) K)) :
    (affineIdealHomogeneousClosure J).IsHomogeneous
      (homogeneousSubmodule (Option (Fin n)) K) := by
  intro k f hf
  change (MvPolynomial.decomposition.decompose' f k :
      MvPolynomial (Option (Fin n)) K) ∈ affineIdealHomogeneousClosure J
  rw [MvPolynomial.decomposition.decompose'_apply]
  change homogeneousScalingHom
      ((Ideal.Quotient.mkₐ K J).comp multivariateDehomogenization)
      (homogeneousComponent k f) = 0
  have hcoef := congrArg (fun p ↦ Polynomial.coeff p k) hf
  change (homogeneousScalingHom
      ((Ideal.Quotient.mkₐ K J).comp multivariateDehomogenization) f).coeff k =
    (0 : Polynomial (MvPolynomial (Fin n) K ⧸ J)).coeff k at hcoef
  rw [homogeneousScalingHom_coeff, Polynomial.coeff_zero] at hcoef
  rw [homogeneousScalingHom_apply_of_isHomogeneous _ _
    (homogeneousComponent_isHomogeneous k f), hcoef, Polynomial.C_0, zero_mul]

/-- The homogenizing coordinate is nonzero on the affine chart. -/
theorem affineIdealHomogeneousClosure_X_none_not_mem
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) K)) (hJ : J.IsPrime) :
    X (none : Option (Fin n)) ∉ affineIdealHomogeneousClosure J := by
  letI : J.IsPrime := hJ
  intro hX
  have hzero : homogeneousScalingHom
      ((Ideal.Quotient.mkₐ K J).comp multivariateDehomogenization)
      (X (none : Option (Fin n))) = 0 := hX
  have hvalue : homogeneousScalingHom
      ((Ideal.Quotient.mkₐ K J).comp multivariateDehomogenization)
      (X (none : Option (Fin n))) = Polynomial.X := by
    simp [homogeneousScalingHom, multivariateDehomogenization]
  exact Polynomial.X_ne_zero (hvalue.symm.trans hzero)

/-- Dehomogenizing the homogeneous closure recovers the original affine
ideal exactly. -/
theorem map_affineIdealHomogeneousClosure_dehomogenization
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) K)) :
    (affineIdealHomogeneousClosure J).map
        multivariateDehomogenization.toRingHom = J := by
  classical
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    change multivariateDehomogenization f ∈ J
    rw [← f.sum_homogeneousComponent, map_sum]
    apply Ideal.sum_mem
    intro k hk
    have hzero : homogeneousScalingHom
        ((Ideal.Quotient.mkₐ K J).comp multivariateDehomogenization) f = 0 := hf
    have hcoef :
        (homogeneousScalingHom
          ((Ideal.Quotient.mkₐ K J).comp multivariateDehomogenization) f).coeff k =
            0 := by rw [hzero]; simp
    rw [homogeneousScalingHom_coeff] at hcoef
    exact Ideal.Quotient.eq_zero_iff_mem.mp hcoef
  · intro f hf
    let F := multivariateHomogenization f f.totalDegree
    have hF : F ∈ affineIdealHomogeneousClosure J := by
      change homogeneousScalingHom
          ((Ideal.Quotient.mkₐ K J).comp multivariateDehomogenization) F = 0
      rw [homogeneousScalingHom_apply_of_isHomogeneous _ F
        (multivariateHomogenization_isHomogeneous f f.totalDegree)]
      have hdehom : multivariateDehomogenization F = f :=
        multivariateDehomogenization_homogenization f f.totalDegree le_rfl
      change Polynomial.C
          (Ideal.Quotient.mk J (multivariateDehomogenization F)) *
            Polynomial.X ^ f.totalDegree = 0
      rw [hdehom, Ideal.Quotient.eq_zero_iff_mem.mpr hf,
        Polynomial.C_0, zero_mul]
    have himage := Ideal.mem_map_of_mem multivariateDehomogenization.toRingHom hF
    simpa [F, multivariateDehomogenization_homogenization f f.totalDegree le_rfl]
      using himage

/-! ## Consecutive coordinates over `ℚ` -/

/-- Projective closure in coordinates `Fin (n+1)`, with coordinate zero
homogenizing. -/
def affineIdealProjectiveClosure {n : ℕ}
    (J : Ideal (MvPolynomial (Fin n) ℚ)) :
    Ideal (MvPolynomial (Fin (n + 1)) ℚ) :=
  (affineIdealHomogeneousClosure J).map
    (MvPolynomial.renameEquiv ℚ (_root_.finSuccEquiv n).symm)

theorem affineIdealProjectiveClosure_isPrime
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℚ)) (hJ : J.IsPrime) :
    (affineIdealProjectiveClosure J).IsPrime := by
  letI : (affineIdealHomogeneousClosure J).IsPrime :=
    affineIdealHomogeneousClosure_isPrime J hJ
  exact Ideal.map_isPrime_of_equiv
    (MvPolynomial.renameEquiv ℚ (_root_.finSuccEquiv n).symm).toRingEquiv

theorem affineIdealProjectiveClosure_isHomogeneous
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℚ)) :
    (affineIdealProjectiveClosure J).IsHomogeneous
      (homogeneousSubmodule (Fin (n + 1)) ℚ) := by
  exact map_renameEquiv_isHomogeneous (_root_.finSuccEquiv n).symm
    (affineIdealHomogeneousClosure J)
    (affineIdealHomogeneousClosure_isHomogeneous J)

theorem affineIdealProjectiveClosure_X_zero_not_mem
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℚ)) (hJ : J.IsPrime) :
    X (0 : Fin (n + 1)) ∉ affineIdealProjectiveClosure J := by
  intro hX
  let E := MvPolynomial.renameEquiv ℚ (_root_.finSuccEquiv n).symm
  have hback : E.symm (X (0 : Fin (n + 1))) ∈
      affineIdealHomogeneousClosure J :=
    (Ideal.symm_apply_mem_of_equiv_iff (f := E.toRingEquiv)).mpr hX
  apply affineIdealHomogeneousClosure_X_none_not_mem J hJ
  simpa [E, MvPolynomial.renameEquiv_symm, MvPolynomial.renameEquiv_apply]
    using hback

/-- The standard consecutive affine chart of the projective closure is
literally the original affine ideal. -/
theorem map_affineIdealProjectiveClosure_standardDehomogenization
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℚ)) :
    (affineIdealProjectiveClosure J).map
        (standardDehomogenizationHom ℚ n) = J := by
  let I := affineIdealProjectiveClosure J
  have hrename : I.map
      (MvPolynomial.renameEquiv ℚ (_root_.finSuccEquiv n)) =
      affineIdealHomogeneousClosure J := by
    dsimp only [I, affineIdealProjectiveClosure]
    exact Ideal.map_of_equiv
      (MvPolynomial.renameEquiv ℚ (_root_.finSuccEquiv n).symm).toRingEquiv
  have h := map_standardDehomogenizationHom_finSuccRename I
  rw [hrename, map_affineIdealHomogeneousClosure_dehomogenization] at h
  exact h.symm

/-- A prime affine dimension-degree certificate becomes the projective
dimension-degree certificate of its homogeneous closure, with the same
displayed dimension and degree. -/
theorem affineIdealProjectiveClosure_hasProjectiveDimensionDegree
    {n r d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℚ))
    (hJ : HasAffineDimensionDegree J r d) :
    HasProjectiveDimensionDegree (affineIdealProjectiveClosure J) r d := by
  let Iopt := affineIdealHomogeneousClosure J
  let I := affineIdealProjectiveClosure J
  have hIoptPrime : Iopt.IsPrime :=
    affineIdealHomogeneousClosure_isPrime J hJ.1
  have hIoptHom : Iopt.IsHomogeneous
      (homogeneousSubmodule (Option (Fin n)) ℚ) :=
    affineIdealHomogeneousClosure_isHomogeneous J
  have hIoptX : X (none : Option (Fin n)) ∉ Iopt :=
    affineIdealHomogeneousClosure_X_none_not_mem J hJ.1
  have hIPrime : I.IsPrime := affineIdealProjectiveClosure_isPrime J hJ.1
  have hIHom : I.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) ℚ) :=
    affineIdealProjectiveClosure_isHomogeneous J
  have hIX : X (0 : Fin (n + 1)) ∉ I :=
    affineIdealProjectiveClosure_X_zero_not_mem J hJ.1
  let R := MvPolynomial (Fin n) ℚ ⧸ J
  have hJtrdeg : Algebra.trdeg ℚ R = (r : Cardinal) :=
    trdeg_eq_nat_of_primeAffine_ringKrullDim_eq ℚ J hJ.1 hJ.2.1
  letI : J.IsPrime := hJ.1
  have hpolyTrdeg : Algebra.trdeg ℚ (Polynomial R) = ((r + 1 : ℕ) : Cardinal) := by
    have h := trdeg_add_eq ℚ R (A := Polynomial R)
    rw [Polynomial.trdeg_of_isDomain, hJtrdeg] at h
    simpa only [Nat.cast_add, Nat.cast_one] using h.symm
  have hchart : Iopt.map multivariateDehomogenization.toRingHom = J :=
    map_affineIdealHomogeneousClosure_dehomogenization J
  have hoptTrdeg : Algebra.trdeg ℚ
      (MvPolynomial (Option (Fin n)) ℚ ⧸ Iopt) =
        ((r + 1 : ℕ) : Cardinal) := by
    have h := trdeg_optionChartPolynomial_eq_cone
      Iopt hIoptHom hIoptPrime hIoptX
    rw [hchart] at h
    exact h.symm.trans hpolyTrdeg
  have hItrdeg : Algebra.trdeg ℚ
      (MvPolynomial (Fin (n + 1)) ℚ ⧸ I) =
        ((r + 1 : ℕ) : Cardinal) := by
    let E := renameQuotientAlgEquiv ℚ (_root_.finSuccEquiv n).symm Iopt
    have hE := E.trdeg_eq
    change Algebra.trdeg ℚ (MvPolynomial (Option (Fin n)) ℚ ⧸ Iopt) =
      Algebra.trdeg ℚ (MvPolynomial (Fin (n + 1)) ℚ ⧸ I) at hE
    exact hE.symm.trans hoptTrdeg
  have hIdim : ringKrullDim
      (MvPolynomial (Fin (n + 1)) ℚ ⧸ I) =
        ((r + 1 : ℕ) : WithBot ℕ∞) :=
    ringKrullDim_eq_nat_of_primeAffine_trdeg_eq ℚ I hIPrime hItrdeg
  rcases hJ with ⟨_hprime, _hdim, hd, P, hPdegree, hPlc, k₀, heventual⟩
  refine ⟨hIdim, hd, P, hPdegree, hPlc, k₀, ?_⟩
  intro k hk
  rw [finrank_projectiveHilbertPiece_eq_standardAffineChart
    I hIHom hIPrime hIX]
  rw [map_affineIdealProjectiveClosure_standardDehomogenization J]
  exact heventual k hk

end

end TranslatedDepthSeven
