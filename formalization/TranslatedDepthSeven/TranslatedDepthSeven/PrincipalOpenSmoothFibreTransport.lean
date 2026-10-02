import TranslatedDepthSeven.AffineZeroLocusQuotientPoints
import TranslatedDepthSeven.PrincipalOpenProjectiveReduction
import TranslatedDepthSeven.PrincipalOpenStandardSmoothDescent
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Rational points and smooth points under the projective-fibre ideal equality

The affine chart of the reduced principal-open model and the direct reduction
of the integral affine chart are defined by literally equal ideals.  This file
records the consequences at the level at which the smooth-point form of the
determinant method is applied:

* quotient coordinate rings are identified by `Ideal.quotientEquivAlgOfEq`;
* rational points are transported by precomposition with that equivalence;
* every affine coordinate has the same value after transport; and
* membership of the corresponding prime in `Algebra.smoothLocus` is
  equivalent.

There is no comparison of independently defined schemes here.  All statements
follow from an equality of ideals and the standard Mathlib quotient
equivalence.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial
open scoped TensorProduct

universe u v

/-- Equal affine ideals give the same coordinate values on the rational point
transported through the canonical quotient algebra equivalence. -/
theorem quotientRationalPoint_transport_apply_mk_of_ideal_eq
    {k : Type u} {σ : Type v} [Field k]
    {I J : Ideal (MvPolynomial σ k)} (hIJ : I = J)
    (x : (MvPolynomial σ k ⧸ I) →ₐ[k] k)
    (f : MvPolynomial σ k) :
    (x.comp (Ideal.quotientEquivAlgOfEq k hIJ).symm.toAlgHom)
        (Ideal.Quotient.mk J f) =
      x (Ideal.Quotient.mk I f) := by
  rw [AlgHom.comp_apply, Ideal.quotientEquivAlgOfEq_symm]
  exact congrArg x (Ideal.quotientEquivAlgOfEq_mk k hIJ.symm f)

/-- The canonical transport of a rational point across equality of affine
ideals preserves, and reflects, smooth-locus membership at its kernel. -/
theorem quotientRationalPoint_mem_smoothLocus_iff_of_ideal_eq
    {k : Type u} {σ : Type v} [Field k]
    {I J : Ideal (MvPolynomial σ k)} (hIJ : I = J)
    (x : (MvPolynomial σ k ⧸ I) →ₐ[k] k) :
    let y : (MvPolynomial σ k ⧸ J) →ₐ[k] k :=
      x.comp (Ideal.quotientEquivAlgOfEq k hIJ).symm.toAlgHom
    (⟨RingHom.ker x.toRingHom, rationalPoint_ker_isPrime x⟩ :
          PrimeSpectrum (MvPolynomial σ k ⧸ I)) ∈
        Algebra.smoothLocus k (MvPolynomial σ k ⧸ I) ↔
      (⟨RingHom.ker y.toRingHom, rationalPoint_ker_isPrime y⟩ :
          PrimeSpectrum (MvPolynomial σ k ⧸ J)) ∈
        Algebra.smoothLocus k (MvPolynomial σ k ⧸ J) := by
  subst J
  have htransport :
      x.comp
          (Ideal.quotientEquivAlgOfEq k (rfl : I = I)).symm.toAlgHom = x := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    exact quotientRationalPoint_transport_apply_mk_of_ideal_eq
      (rfl : I = I) x (MvPolynomial.X i)
  rw [htransport]

/-- A global standard-smooth algebra is smooth at the prime defined by every
rational point.  This is the direct link from a marked standard-smooth chart
to Mathlib's smooth locus. -/
theorem rationalPoint_mem_smoothLocus_of_isStandardSmoothOfRelativeDimension
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n k A]
    (x : A →ₐ[k] k) :
    (⟨RingHom.ker x.toRingHom, rationalPoint_ker_isPrime x⟩ :
        PrimeSpectrum A) ∈ Algebra.smoothLocus k A := by
  letI : Algebra.IsStandardSmooth k A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  letI : Algebra.Smooth k A := inferInstance
  rw [Algebra.smoothLocus_eq_univ_iff.mpr inferInstance]
  exact Set.mem_univ _

/-- A marked point on a standard-smooth algebra remains a rational smooth
point after extension of the base to a field.  The point is the literal
tensor-product point constructed in
`PrincipalOpenStandardSmoothDescent`. -/
theorem baseChangePoint_mem_smoothLocus_of_isStandardSmoothOfRelativeDimension
    {R : Type u} {k : Type v} {A : Type max u v}
    [CommRing R] [Field k] [CommRing A]
    [Algebra R k] [Algebra R A]
    (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n R A]
    (g : A →ₐ[R] k) :
    let point : (k ⊗[R] A) →ₐ[k] k := baseChangePointAlgHom R k A g
    (⟨RingHom.ker point.toRingHom, rationalPoint_ker_isPrime point⟩ :
        PrimeSpectrum (k ⊗[R] A)) ∈
      Algebra.smoothLocus k (k ⊗[R] A) := by
  letI : Algebra.IsStandardSmoothOfRelativeDimension n k (k ⊗[R] A) :=
    standardSmooth_relativeDimension_stable_under_baseChange
  exact
    rationalPoint_mem_smoothLocus_of_isStandardSmoothOfRelativeDimension
      n (baseChangePointAlgHom R k A g)

/-- A rational smooth point on a principal localization gives a rational
smooth point of the unlocalized affine scheme by composition with the
localization map.  This is the pointwise form of
`Algebra.smoothLocus_comap_of_isLocalization`. -/
theorem localizationAway_rationalPoint_mem_smoothLocus_down
    {k : Type u} {A : Type v} {Af : Type max u v}
    [Field k] [CommRing A] [CommRing Af]
    [Algebra k A] [Algebra A Af] [Algebra k Af]
    [IsScalarTower k A Af]
    (f : A) [IsLocalization.Away f Af]
    (x : Af →ₐ[k] k)
    (hx :
      (⟨RingHom.ker x.toRingHom, rationalPoint_ker_isPrime x⟩ :
          PrimeSpectrum Af) ∈ Algebra.smoothLocus k Af) :
    let y : A →ₐ[k] k := x.comp (IsScalarTower.toAlgHom k A Af)
    (⟨RingHom.ker y.toRingHom, rationalPoint_ker_isPrime y⟩ :
        PrimeSpectrum A) ∈ Algebra.smoothLocus k A := by
  let P : PrimeSpectrum Af :=
    ⟨RingHom.ker x.toRingHom, rationalPoint_ker_isPrime x⟩
  have hcomap :
      PrimeSpectrum.comap (algebraMap A Af) P ∈
        Algebra.smoothLocus k A := by
    have hset := Algebra.smoothLocus_comap_of_isLocalization
      (R := k) (A := A) (Af := Af) f
    rw [← hset] at hx
    exact hx
  convert hcomap using 1

/-- The exact three-step smooth-point transport used for an affine chart:
descend a rational smooth point from a principal localization to its quotient
coordinate ring, then transport it across a literal equality of defining
ideals. -/
theorem localizationAway_quotientRationalPoint_mem_smoothLocus_transport
    {k : Type u} {σ : Type v} [Field k]
    {I J : Ideal (MvPolynomial σ k)} (hIJ : I = J)
    {Af : Type max u v} [CommRing Af]
    [Algebra (MvPolynomial σ k ⧸ I) Af] [Algebra k Af]
    [IsScalarTower k (MvPolynomial σ k ⧸ I) Af]
    (f : MvPolynomial σ k ⧸ I) [IsLocalization.Away f Af]
    (x : Af →ₐ[k] k)
    (hx :
      (⟨RingHom.ker x.toRingHom, rationalPoint_ker_isPrime x⟩ :
          PrimeSpectrum Af) ∈ Algebra.smoothLocus k Af) :
    let xI : (MvPolynomial σ k ⧸ I) →ₐ[k] k :=
      x.comp (IsScalarTower.toAlgHom k (MvPolynomial σ k ⧸ I) Af)
    let xJ : (MvPolynomial σ k ⧸ J) →ₐ[k] k :=
      xI.comp (Ideal.quotientEquivAlgOfEq k hIJ).symm.toAlgHom
    (⟨RingHom.ker xJ.toRingHom, rationalPoint_ker_isPrime xJ⟩ :
        PrimeSpectrum (MvPolynomial σ k ⧸ J)) ∈
      Algebra.smoothLocus k (MvPolynomial σ k ⧸ J) := by
  let xI : (MvPolynomial σ k ⧸ I) →ₐ[k] k :=
    x.comp (IsScalarTower.toAlgHom k (MvPolynomial σ k ⧸ I) Af)
  have hxI :
      (⟨RingHom.ker xI.toRingHom, rationalPoint_ker_isPrime xI⟩ :
          PrimeSpectrum (MvPolynomial σ k ⧸ I)) ∈
        Algebra.smoothLocus k (MvPolynomial σ k ⧸ I) :=
    localizationAway_rationalPoint_mem_smoothLocus_down f x hx
  exact
    (quotientRationalPoint_mem_smoothLocus_iff_of_ideal_eq hIJ xI).mp hxI

/-- If the localized quotient chart is standard smooth, its every rational
point transports to a smooth rational point of the quotient by the equal
ideal. -/
theorem localizationAway_quotientRationalPoint_mem_smoothLocus_transport_of_standardSmooth
    {k : Type u} {σ : Type v} [Field k]
    {I J : Ideal (MvPolynomial σ k)} (hIJ : I = J)
    {Af : Type max u v} [CommRing Af]
    [Algebra (MvPolynomial σ k ⧸ I) Af] [Algebra k Af]
    [IsScalarTower k (MvPolynomial σ k ⧸ I) Af]
    (f : MvPolynomial σ k ⧸ I) [IsLocalization.Away f Af]
    (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n k Af]
    (x : Af →ₐ[k] k) :
    let xI : (MvPolynomial σ k ⧸ I) →ₐ[k] k :=
      x.comp (IsScalarTower.toAlgHom k (MvPolynomial σ k ⧸ I) Af)
    let xJ : (MvPolynomial σ k ⧸ J) →ₐ[k] k :=
      xI.comp (Ideal.quotientEquivAlgOfEq k hIJ).symm.toAlgHom
    (⟨RingHom.ker xJ.toRingHom, rationalPoint_ker_isPrime xJ⟩ :
        PrimeSpectrum (MvPolynomial σ k ⧸ J)) ∈
      Algebra.smoothLocus k (MvPolynomial σ k ⧸ J) := by
  apply localizationAway_quotientRationalPoint_mem_smoothLocus_transport
    hIJ f x
  exact
    rationalPoint_mem_smoothLocus_of_isStandardSmoothOfRelativeDimension n x

/-- On every polynomial representative, the canonical quotient equivalence
attached to the principal-open special-fibre ideal equality is literally the
identity.  Together with
`quotientRationalPoint_mem_smoothLocus_iff_of_ideal_eq`, this identifies the
rational smooth points of the two affine charts. -/
theorem dehomogenized_principalOpen_specialFibre_quotientEquiv_apply_mk
    {σ : Type u}
    (Δ : ℤ) (p : ℕ) (hp : p.Prime) (hpΔ : ¬ p ∣ Δ.natAbs)
    (I : Ideal (MvPolynomial (Option σ) ℤ)) :
    let Iopen : Ideal (MvPolynomial σ (ZMod p)) :=
      Ideal.map
        (multivariateDehomogenization
          (R := ZMod p) (σ := σ)).toRingHom
        (Ideal.map (MvPolynomial.map (awayIntToZMod Δ p hp hpΔ))
          (Ideal.map
            (MvPolynomial.map (algebraMap ℤ (Localization.Away Δ))) I))
    let Idirect : Ideal (MvPolynomial σ (ZMod p)) :=
      Ideal.map (MvPolynomial.map (Int.castRingHom (ZMod p)))
        (Ideal.map
          (multivariateDehomogenization
            (R := ℤ) (σ := σ)).toRingHom I)
    ∀ f : MvPolynomial σ (ZMod p),
      Ideal.quotientEquivAlgOfEq (ZMod p)
          (dehomogenized_principalOpen_specialFibreIdeal_eq
            Δ p hp hpΔ I)
          (Ideal.Quotient.mk Iopen f) =
        Ideal.Quotient.mk Idirect f := by
  dsimp only
  intro f
  exact Ideal.quotientEquivAlgOfEq_mk (ZMod p)
    (dehomogenized_principalOpen_specialFibreIdeal_eq Δ p hp hpΔ I) f

end

end TranslatedDepthSeven
