import TranslatedDepthSeven.StandardSmoothChartLocalRingInternal
import TranslatedDepthSeven.SurjectivePointLocalizationInternal
import TranslatedDepthSeven.SurjectiveDomainDimensionInternal
import TranslatedDepthSeven.JacobianMinorStandardSmoothChart
import TranslatedDepthSeven.AffineDomainMaximalHeightInternal

/-!
# A codimension-sized Jacobian minor implies smoothness of a prime variety

The displayed equations need only belong to the prime ideal.  They need
not generate it.  Their nonzero minor gives a standard-smooth complete
intersection containing the variety near the rational point.  The two
local rings are domains, the containing ring has dimension at most the
dimension of the variety, and the map onto the variety's local ring is
surjective.  Strict dimension drop for a nonzero prime kernel proves that
the map is an isomorphism.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

theorem rationalPoint_mem_smoothLocus_of_codimension_jacobian_minor
    {K : Type*} [Field K] [CharZero K] {N c : ℕ}
    (I : Ideal (MvPolynomial (Fin N) K)) [I.IsPrime]
    (equations : Fin c → MvPolynomial (Fin N) K)
    (hequations : ∀ j, equations j ∈ I)
    (selectedVar : Fin c → Fin N) (hselected : Function.Injective selectedVar)
    (z : Fin N → K)
    (hz : I ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom)
    (hminor : MvPolynomial.aeval z
      (selectedJacobianDeterminant equations selectedVar) ≠ 0)
    (hdimension : ringKrullDim (MvPolynomial (Fin N) K ⧸ I) =
      ((N - c : ℕ) : WithBot ℕ∞)) :
    (⟨RingHom.ker (affineQuotientRationalPoint I z hz).toRingHom,
      rationalPoint_ker_isPrime (affineQuotientRationalPoint I z hz)⟩ :
        PrimeSpectrum (MvPolynomial (Fin N) K ⧸ I)) ∈
      Algebra.smoothLocus K (MvPolynomial (Fin N) K ⧸ I) := by
  classical
  let J := Ideal.span (Set.range equations)
  have hJI : J ≤ I := Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hequations j)
  have hzJ : J ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom := hJI.trans hz
  let A := MvPolynomial (Fin N) K ⧸ J
  let B := MvPolynomial (Fin N) K ⧸ I
  let pointA : A →ₐ[K] K := affineQuotientRationalPoint J z hzJ
  let pointB : B →ₐ[K] K := affineQuotientRationalPoint I z hz
  let M := RingHom.ker pointA.toRingHom
  let P := RingHom.ker pointB.toRingHom
  letI : M.IsPrime := rationalPoint_ker_isPrime pointA
  letI : P.IsMaximal := RingHom.ker_isMaximal_of_surjective pointB.toRingHom
    (fun a ↦ ⟨algebraMap K B a, by simp⟩)
  let chart : A := Ideal.Quotient.mk J (selectedJacobianDeterminant equations selectedVar)
  let T := Localization.Away chart
  obtain ⟨pointT, hpointT, hsmooth⟩ :=
    selectedJacobian_principalOpen_standardSmooth_and_point
      equations selectedVar hselected J rfl z hzJ hminor
  letI : Algebra.IsStandardSmoothOfRelativeDimension (N - c) K T := hsmooth
  obtain ⟨hsourceDomain, hsourceDimension, hsourceSmooth⟩ :=
    localRing_of_standardSmooth_localizationChart (Submonoid.powers chart)
      pointT (N - c) M (congrArg (fun f : A →ₐ[K] K ↦ RingHom.ker f.toRingHom)
        hpointT.symm)
  letI : IsDomain (Localization.AtPrime M) := hsourceDomain
  letI : Algebra.FormallySmooth K (Localization.AtPrime M) := hsourceSmooth
  let g : A →ₐ[K] B := Ideal.Quotient.factorₐ K hJI
  have hg : Function.Surjective g := Ideal.Quotient.factor_surjective hJI
  have hpoints : pointB.comp g = pointA := by
    apply Ideal.Quotient.algHom_ext
    rfl
  have hMP : M = P.comap g := by
    ext a
    change pointA a = 0 ↔ pointB (g a) = 0
    rw [← AlgHom.comp_apply, hpoints]
  obtain ⟨φ, hφsurj, _⟩ := exists_surjective_pointLocalizationAlgHom g hg M P hMP
  have htargetDimension : ringKrullDim (Localization.AtPrime P) =
      ((N - c : ℕ) : WithBot ℕ∞) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P)]
    exact (affineDomain_maximal_height_eq_dimension K B P).trans hdimension
  have hφbij : Function.Bijective φ :=
    bijective_of_surjective_of_domain_dimension_bounds φ.toRingHom hφsurj
      (N - c) hsourceDimension htargetDimension.ge
  change Algebra.FormallySmooth K (Localization.AtPrime P)
  exact Algebra.FormallySmooth.of_equiv (AlgEquiv.ofBijective φ hφbij)

end

end TranslatedDepthSeven
