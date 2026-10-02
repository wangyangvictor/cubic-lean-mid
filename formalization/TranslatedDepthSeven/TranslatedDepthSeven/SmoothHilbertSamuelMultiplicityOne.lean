import TranslatedDepthSeven.PublishedCountingTheorems
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# A literal multiplicity-one criterion for special-fibre jets

`Published.HasHilbertSamuelMultiplicityAt` deliberately spells out
Hilbert--Samuel multiplicity through the dimensions of the displayed jet
quotients.  This file discharges all polynomial bookkeeping in the smooth
multiplicity-one case: it is enough to identify those dimensions with the
binomial coefficients `choose (k + r) r`.

The remaining local-algebra statement needed to derive that identity from
standard smoothness is the usual identification of the associated graded
ring at a rational smooth point with the symmetric algebra of its cotangent
space.  That higher-jet identification is not currently available in
Mathlib, so it is not postulated here.
-/

namespace TranslatedDepthSeven

noncomputable section

open Published
open scoped TensorProduct
open KaehlerDifferential

universe u v

/-! ## The first infinitesimal neighbourhood -/

/-- At a rational point of a standard-smooth algebra of relative dimension
`r`, the displayed conormal space `m / m^2` has dimension `r`.

This is the degree-one part of the regular-local calculation.  It follows
from the already formalized cotangent complex and standard-smoothness of the
source; unlike the missing higher-degree statement, it needs no associated
graded-ring theorem. -/
theorem finrank_cotangent_of_isStandardSmoothOfRelativeDimension
    {K : Type u} {A : Type v} [Field K] [CommRing A] [Algebra K A]
    (f : A →ₐ[K] K) (r : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A] :
    Module.finrank K (RingHom.ker f.toRingHom).Cotangent = r := by
  have hf : Function.Surjective f := fun x ↦
    ⟨algebraMap K A x, by simp⟩
  let P : Algebra.Extension.{v} K K :=
    Algebra.Extension.ofSurjective f hf
  letI : Algebra.IsStandardSmooth K A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth r
  letI : Algebra.Smooth K A := inferInstance
  letI : Nontrivial P.Ring := hf.nontrivial
  letI : Algebra.IsStandardSmoothOfRelativeDimension r K P.Ring :=
    show Algebra.IsStandardSmoothOfRelativeDimension r K A from inferInstance
  letI : Algebra.IsStandardSmooth K P.Ring :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth r
  letI : Algebra.FormallySmooth K P.Ring :=
    show Algebra.FormallySmooth K A from inferInstance
  let E₀ : P.Cotangent ≃ₗ[K] P.ker.Cotangent := {
    toFun := Algebra.Extension.Cotangent.val
    invFun := Algebra.Extension.Cotangent.of
    left_inv x := Algebra.Extension.Cotangent.of_val x
    right_inv x := Algebra.Extension.Cotangent.val_of x
    map_add' _ _ := Algebra.Extension.Cotangent.val_add _ _
    map_smul' c x := Algebra.Extension.Cotangent.val_smul'' c x
  }
  have hinj : Function.Injective P.cotangentComplex := by
    rw [P.cotangentComplex_injective_iff]
    infer_instance
  have hsurj : Function.Surjective P.cotangentComplex := by
    intro y
    exact (P.exact_cotangentComplex_toKaehler y).mp
      (Subsingleton.elim _ _)
  let E : P.Cotangent ≃ₗ[K] P.CotangentSpace :=
    LinearEquiv.ofBijective P.cotangentComplex ⟨hinj, hsurj⟩
  change Module.finrank K P.ker.Cotangent = r
  rw [← E₀.finrank_eq, E.finrank_eq]
  rw [Module.finrank_baseChange]
  exact Module.finrank_eq_of_rank_eq
    (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential r)

/-- The conormal space at a rational point of a standard-smooth algebra is
finite-dimensional over the displayed residue field. -/
theorem cotangent_moduleFinite_of_isStandardSmoothOfRelativeDimension
    {K : Type u} {A : Type v} [Field K] [CommRing A] [Algebra K A]
    (f : A →ₐ[K] K) (r : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A] :
    Module.Finite K (RingHom.ker f.toRingHom).Cotangent := by
  have hf : Function.Surjective f := fun x ↦
    ⟨algebraMap K A x, by simp⟩
  let P : Algebra.Extension.{v} K K :=
    Algebra.Extension.ofSurjective f hf
  letI : Algebra.IsStandardSmooth K A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth r
  letI : Algebra.Smooth K A := inferInstance
  letI : Nontrivial P.Ring := hf.nontrivial
  letI : Algebra.IsStandardSmoothOfRelativeDimension r K P.Ring :=
    show Algebra.IsStandardSmoothOfRelativeDimension r K A from inferInstance
  letI : Algebra.IsStandardSmooth K P.Ring :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth r
  letI : Algebra.FormallySmooth K P.Ring :=
    show Algebra.FormallySmooth K A from inferInstance
  let E₀ : P.Cotangent ≃ₗ[K] P.ker.Cotangent := {
    toFun := Algebra.Extension.Cotangent.val
    invFun := Algebra.Extension.Cotangent.of
    left_inv x := Algebra.Extension.Cotangent.of_val x
    right_inv x := Algebra.Extension.Cotangent.val_of x
    map_add' _ _ := Algebra.Extension.Cotangent.val_add _ _
    map_smul' c x := Algebra.Extension.Cotangent.val_smul'' c x
  }
  have hinj : Function.Injective P.cotangentComplex := by
    rw [P.cotangentComplex_injective_iff]
    infer_instance
  have hsurj : Function.Surjective P.cotangentComplex := by
    intro y
    exact (P.exact_cotangentComplex_toKaehler y).mp
      (Subsingleton.elim _ _)
  let E : P.Cotangent ≃ₗ[K] P.CotangentSpace :=
    LinearEquiv.ofBijective P.cotangentComplex ⟨hinj, hsurj⟩
  haveI : Module.Finite K P.CotangentSpace := inferInstance
  change Module.Finite K P.ker.Cotangent
  exact Module.Finite.equiv (E.symm.trans E₀)

/-- If the conormal space of a rational augmentation is finite-dimensional,
then so is its first infinitesimal neighbourhood.  Concretely, constants and
`m / m^2` span `A / m^2`. -/
theorem firstJet_moduleFinite_of_cotangent
    {K : Type u} {A : Type v} [Field K] [CommRing A] [Algebra K A]
    (f : A →ₐ[K] K)
    [Module.Finite K (RingHom.ker f.toRingHom).Cotangent] :
    Module.Finite K
      (A ⧸ (RingHom.ker f.toRingHom) ^ 2) := by
  let m : Ideal A := RingHom.ker f.toRingHom
  let B := A ⧸ m ^ 2
  let cotangentInclusion : m.Cotangent →ₗ[K] B :=
    m.cotangentToQuotientSquare.restrictScalars K
  let spanMap : K × m.Cotangent →ₗ[K] B :=
    (Algebra.linearMap K B).coprod cotangentInclusion
  apply Module.Finite.of_surjective spanMap
  intro b
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  have ha : a - algebraMap K A (f a) ∈ m := by
    change f (a - algebraMap K A (f a)) = 0
    simp
  refine ⟨(f a, m.toCotangent ⟨a - algebraMap K A (f a), ha⟩), ?_⟩
  change Ideal.Quotient.mk (m ^ 2) (algebraMap K A (f a)) +
      m.cotangentToQuotientSquare
        (m.toCotangent ⟨a - algebraMap K A (f a), ha⟩) =
    Ideal.Quotient.mk (m ^ 2) a
  rw [Ideal.toCotangent_to_quotient_square]
  simp

/-- The first jet has one constant direction and precisely the cotangent
directions.  This is the exact length formula
`dim_K(A / m^2) = 1 + dim_K(m / m^2)` for a rational augmentation. -/
theorem finrank_firstJet_eq_cotangent_add_one
    {K : Type u} {A : Type v} [Field K] [CommRing A] [Algebra K A]
    (f : A →ₐ[K] K)
    [Module.Finite K (RingHom.ker f.toRingHom).Cotangent] :
    Module.finrank K (A ⧸ (RingHom.ker f.toRingHom) ^ 2) =
      Module.finrank K (RingHom.ker f.toRingHom).Cotangent + 1 := by
  let m : Ideal A := RingHom.ker f.toRingHom
  let B := A ⧸ m ^ 2
  let g : B →ₐ[K] K := f.kerSquareLift
  letI : Module.Finite K B := firstJet_moduleFinite_of_cotangent f
  have hg : Function.Surjective g := fun x ↦
    ⟨algebraMap K B x, by simp [g]⟩
  have hrange : LinearMap.range g.toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr hg
  have hker : LinearMap.ker g.toLinearMap =
      m.cotangentIdeal.restrictScalars K := by
    ext x
    change x ∈ RingHom.ker g.toRingHom ↔ x ∈ m.cotangentIdeal
    rw [show RingHom.ker g.toRingHom = m.cotangentIdeal by
      simpa [g, m, B] using AlgHom.ker_kerSquareLift f]
  have hkerRank : Module.finrank K (LinearMap.ker g.toLinearMap) =
      Module.finrank K m.Cotangent := by
    rw [hker]
    exact (m.cotangentEquivIdeal.restrictScalars K).finrank_eq.symm
  have h := g.toLinearMap.finrank_range_add_finrank_ker
  rw [hrange, finrank_top, Module.finrank_self, hkerRank] at h
  change Module.finrank K B = Module.finrank K m.Cotangent + 1
  omega

/-- The first infinitesimal neighbourhood of a rational point on a
standard-smooth `r`-fold has the expected dimension `r + 1`. -/
theorem finrank_firstJet_eq_add_one_of_isStandardSmoothOfRelativeDimension
    {K : Type u} {A : Type v} [Field K] [CommRing A] [Algebra K A]
    (f : A →ₐ[K] K) (r : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A] :
    Module.finrank K (A ⧸ (RingHom.ker f.toRingHom) ^ 2) = r + 1 := by
  letI : Module.Finite K (RingHom.ker f.toRingHom).Cotangent :=
    cotangent_moduleFinite_of_isStandardSmoothOfRelativeDimension f r
  rw [finrank_firstJet_eq_cotangent_add_one f,
    finrank_cotangent_of_isStandardSmoothOfRelativeDimension f r]

/-! ## Comparison with the literal special-fibre jets -/

/-- The displayed quotient evaluation, with its evident algebra-map
structure made explicit. -/
noncomputable def specialFiberQuotientEvaluationAlgHom
    {M p : ℕ} [Fact p.Prime]
    (J : Ideal (MvPolynomial (Fin M) (ZMod p)))
    (P : Fin M → ZMod p) (hP : IsPointOnSpecialFiber J P) :
    (MvPolynomial (Fin M) (ZMod p) ⧸ J) →ₐ[ZMod p] ZMod p where
  toRingHom := specialFiberQuotientEvaluation J P hP
  commutes' c := by
    change Ideal.Quotient.lift J (specialFiberEvaluation P) hP
      (Ideal.Quotient.mk J (MvPolynomial.C c)) = c
    rw [Ideal.Quotient.lift_mk]
    exact MvPolynomial.eval₂Hom_C (RingHom.id (ZMod p)) P c

set_option synthInstance.maxHeartbeats 100000 in
/-- The jet quotient used in `Published.HasHilbertSamuelMultiplicityAt` is
the quotient of the affine coordinate ring by the corresponding power of
the rational point ideal.  This is just the third isomorphism theorem, but
recording it explicitly prevents any ambiguity about which local filtration
is being measured. -/
noncomputable def specialFiberPointPowerQuotientAlgEquivJetSpace
    {M p : ℕ} [Fact p.Prime]
    (J : Ideal (MvPolynomial (Fin M) (ZMod p)))
    (P : Fin M → ZMod p) (hP : IsPointOnSpecialFiber J P) (k : ℕ) :
    ((MvPolynomial (Fin M) (ZMod p) ⧸ J) ⧸
        specialFiberPointIdeal J P hP ^ (k + 1)) ≃ₐ[ZMod p]
      specialFiberJetSpace J P k := by
  let R := MvPolynomial (Fin M) (ZMod p)
  let K : Ideal R := RingHom.ker (specialFiberEvaluation P)
  let q : R →ₐ[ZMod p] R ⧸ J := Ideal.Quotient.mkₐ (ZMod p) J
  have hm : specialFiberPointIdeal J P hP = K.map q := by
    simpa [specialFiberPointIdeal, specialFiberQuotientEvaluation, K, q, R] using
      (Ideal.ker_quotient_lift (specialFiberEvaluation P) hP)
  have hpow : specialFiberPointIdeal J P hP ^ (k + 1) =
      (K ^ (k + 1)).map q := by
    rw [hm, Ideal.map_pow]
  exact (Ideal.quotientEquivAlgOfEq (ZMod p) hpow).trans
    (DoubleQuot.quotQuotEquivQuotSupₐ (ZMod p) J (K ^ (k + 1)))

set_option synthInstance.maxHeartbeats 100000 in
/-- The literal first jet in the published multiplicity predicate has the
expected dimension at a standard-smooth affine-chart point. -/
theorem finrank_specialFiberJetSpace_one_eq_add_one_of_isStandardSmooth
    {M p : ℕ} [Fact p.Prime]
    (J : Ideal (MvPolynomial (Fin M) (ZMod p)))
    (P : Fin M → ZMod p) (hP : IsPointOnSpecialFiber J P) (r : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension r (ZMod p)
      (MvPolynomial (Fin M) (ZMod p) ⧸ J)] :
    Module.finrank (ZMod p) (specialFiberJetSpace J P 1) = r + 1 := by
  let f := specialFiberQuotientEvaluationAlgHom J P hP
  let E := specialFiberPointPowerQuotientAlgEquivJetSpace J P hP 1
  rw [← E.toLinearEquiv.finrank_eq]
  change Module.finrank (ZMod p)
    ((MvPolynomial (Fin M) (ZMod p) ⧸ J) ⧸
      RingHom.ker f.toRingHom ^ 2) = r + 1
  exact finrank_firstJet_eq_add_one_of_isStandardSmoothOfRelativeDimension f r

/-- Exact binomial jet lengths give Hilbert--Samuel multiplicity one at the
displayed affine-chart point.  This is the literal numerical endpoint of the
regular-local-ring calculation; no geometric or counting assertion is
packaged into the hypotheses. -/
theorem hasHilbertSamuelMultiplicityAt_one_of_finrank_specialFiberJetSpace_eq_choose
    {N p : ℕ} (hp : p.Prime) [Fact p.Prime]
    (J : Ideal (MvPolynomial (Fin (N + 1)) (ZMod p)))
    (P : Fin (N + 1) → ZMod p) (r : ℕ)
    (hP : IsPointOnSpecialFiber (standardAffineChartIdeal J)
      (standardAffineChartPoint P))
    (hfinite : ∀ k : ℕ, Module.Finite (ZMod p)
      (specialFiberJetSpace (standardAffineChartIdeal J)
        (standardAffineChartPoint P) k))
    (hjet : ∀ k : ℕ,
      Module.finrank (ZMod p)
          (specialFiberJetSpace (standardAffineChartIdeal J)
            (standardAffineChartPoint P) k) =
        (k + r).choose r) :
    HasHilbertSamuelMultiplicityAt hp J P r 1 := by
  refine ⟨hP, hfinite, Polynomial.preHilbertPoly ℚ r 0, ?_, ?_, 0, ?_⟩
  · exact Polynomial.natDegree_preHilbertPoly ℚ r 0
  · rw [Polynomial.leadingCoeff_preHilbertPoly]
    simp
  · intro k _
    rw [hjet]
    simpa [Nat.add_comm] using
      (Polynomial.preHilbertPoly_eq_choose_sub_add ℚ r (k := 0) (n := k)
        (Nat.zero_le k)).symm

/-- An eventual binomial jet formula already suffices.  This is occasionally
more convenient than the exact formula when low-order thickenings are treated
separately. -/
theorem hasHilbertSamuelMultiplicityAt_one_of_eventually_finrank_specialFiberJetSpace_eq_choose
    {N p : ℕ} (hp : p.Prime) [Fact p.Prime]
    (J : Ideal (MvPolynomial (Fin (N + 1)) (ZMod p)))
    (P : Fin (N + 1) → ZMod p) (r k₀ : ℕ)
    (hP : IsPointOnSpecialFiber (standardAffineChartIdeal J)
      (standardAffineChartPoint P))
    (hfinite : ∀ k : ℕ, Module.Finite (ZMod p)
      (specialFiberJetSpace (standardAffineChartIdeal J)
        (standardAffineChartPoint P) k))
    (hjet : ∀ k ≥ k₀,
      Module.finrank (ZMod p)
          (specialFiberJetSpace (standardAffineChartIdeal J)
            (standardAffineChartPoint P) k) =
        (k + r).choose r) :
    HasHilbertSamuelMultiplicityAt hp J P r 1 := by
  refine ⟨hP, hfinite, Polynomial.preHilbertPoly ℚ r 0, ?_, ?_, k₀, ?_⟩
  · exact Polynomial.natDegree_preHilbertPoly ℚ r 0
  · rw [Polynomial.leadingCoeff_preHilbertPoly]
    simp
  · intro k hk
    rw [hjet k hk]
    simpa [Nat.add_comm] using
      (Polynomial.preHilbertPoly_eq_choose_sub_add ℚ r (k := 0) (n := k)
        (Nat.zero_le k)).symm

end

end TranslatedDepthSeven
