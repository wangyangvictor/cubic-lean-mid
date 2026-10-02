import TranslatedDepthSeven.ProjectiveBertiniGenericQuotient
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Etale.Field

/-! Reducedness of the literal full generic affine hyperplane quotient.
The independent constant coefficient eliminates one universal parameter.
This is an algebraic assertion about the actual quotient, not a supplied
Bertini or reduced-fiber premise. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
noncomputable section
namespace CubicTenVariables.GenericReducedAffineHyperplane
open MvPolynomial TranslatedDepthSeven
open scoped TensorProduct

/-- With coefficient one on the constant parameter, the actual incidence
ring is a polynomial ring over the source coordinate ring. -/
def incidenceEquiv {R σ : Type*} [CommRing R] [Fintype σ] (d : σ → R) :
    BertiniIncidenceRing ((fun i : Option σ => i.elim (1 : R) d)) ≃+* MvPolynomial σ R := by
  classical
  let e := optionEquivLeft R σ
  have he : e (bertiniLinear ((fun i : Option σ => i.elim (1 : R) d))) =
      Polynomial.X - Polynomial.C (-bertiniLinear d) := by
    dsimp only [e]
    rw [bertiniLinear_option]
    simp only [Option.elim_none, Option.elim_some, map_add, map_mul,
      optionEquivLeft_C, optionEquivLeft_X_none, map_one, one_mul,
      bertini_optionEquivLeft_rename_some, map_neg, sub_neg_eq_add]
  have hmap : Ideal.span {Polynomial.X - Polynomial.C (-bertiniLinear d)} =
      (Ideal.span {bertiniLinear ((fun i : Option σ => i.elim (1 : R) d))}).map e.toRingHom := by
    rw [Ideal.map_span, Set.image_singleton]
    change _ = Ideal.span {e (bertiniLinear (fun i : Option σ => i.elim (1 : R) d))}
    rw [he]
  exact (Ideal.quotientEquiv _ _ e.toRingEquiv hmap).trans
    (Polynomial.quotientSpanXSubCAlgEquiv (-bertiniLinear d)).toRingEquiv

theorem incidence_isReduced {R σ : Type*} [CommRing R] [IsReduced R] [Fintype σ]
    (d : σ → R) : IsReduced (BertiniIncidenceRing ((fun i : Option σ => i.elim (1 : R) d))) :=
  isReduced_of_injective (incidenceEquiv d).toRingHom (incidenceEquiv d).injective

variable {k σ : Type*} [Field k] [Fintype σ]

/-- The coefficient family consists of the literal constant 1 and all
actual affine coordinate polynomials. -/
def coordinateFamily : Option σ → MvPolynomial σ k := fun i => i.elim 1 X

/-- The actual ideal after extending coefficients to the full parameter
fraction field and adjoining its full generic affine linear equation. -/
def genericIdeal (L : Type*) [CommRing L] [Algebra (MvPolynomial (Option σ) k) L]
    (I : Ideal (MvPolynomial σ k)) : Ideal (MvPolynomial σ L) :=
  I.map (MvPolynomial.map ((algebraMap (MvPolynomial (Option σ) k) L).comp C)) ⊔
    Ideal.span {MvPolynomial.map (algebraMap (MvPolynomial (Option σ) k) L)
      (bertiniCoefficientHyperplane (coordinateFamily (k := k) (σ := σ)))}

/-- Every reduced affine source has a reduced full parameter-generic
hyperplane quotient. This statement itself is characteristic-free and
allows an empty generic intersection. -/
theorem generic_quotient_isReduced
    (L : Type*) [CommRing L] [Algebra (MvPolynomial (Option σ) k) L]
    [IsFractionRing (MvPolynomial (Option σ) k) L]
    (I : Ideal (MvPolynomial σ k)) (hI : I.IsRadical) :
    IsReduced (MvPolynomial σ L ⧸ genericIdeal L I) := by
  letI : IsReduced (MvPolynomial σ k ⧸ I) :=
    (Ideal.isRadical_iff_quotient_reduced I).mp hI
  let d : Option σ → MvPolynomial σ k ⧸ I :=
    fun i => Ideal.Quotient.mk I (coordinateFamily i)
  have hd : d = (fun j => j.elim 1 (fun i => Ideal.Quotient.mk I (X i))) := by
    funext i
    cases i <;> simp [d, coordinateFamily]
  letI : IsReduced (BertiniIncidenceRing d) := by
    rw [hd]
    exact incidence_isReduced _
  letI : IsReduced (BertiniGenericIncidenceRing (K := k) d) := inferInstance
  exact isReduced_of_injective
    (bertiniGenericCoefficientQuotientEquiv L I coordinateFamily).toRingHom
    (bertiniGenericCoefficientQuotientEquiv L I coordinateFamily).injective

/-- Reduced incidence after selecting any parameter whose coefficient is one. -/
theorem incidence_isReduced_of_one
    {R τ υ : Type*} [CommRing R] [IsReduced R] [Fintype τ] [Fintype υ]
    (e : τ ≃ Option υ) (d : τ → R) (hd : d (e.symm none) = 1) :
    IsReduced (BertiniIncidenceRing d) := by
  classical
  let d' : υ → R := fun i => d (e.symm (some i))
  have he : rename e (bertiniLinear d) =
      bertiniLinear (fun i : Option υ => i.elim (1 : R) d') := by
    rw [bertiniLinear_rename]
    congr 1
    funext i
    cases i <;> simp [Function.comp_def, hd, d']
  let f := renameEquiv R e
  have hmap : Ideal.span {bertiniLinear (fun i : Option υ => i.elim (1 : R) d')} =
      (Ideal.span {bertiniLinear d}).map f.toRingHom := by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun p => Ideal.span {p}) he.symm
  let q := Ideal.quotientEquiv _ _ f.toRingEquiv hmap
  letI := incidence_isReduced d'
  exact isReduced_of_injective q.toRingHom q.injective

/-- The same literal generic quotient theorem allows arbitrary coordinate
indexing and any polynomial family with one coefficient equal to one. -/
theorem generic_family_quotient_isReduced
    {τ υ : Type*} [Fintype τ] [Fintype υ]
    (L : Type*) [CommRing L] [Algebra (MvPolynomial τ k) L]
    [IsFractionRing (MvPolynomial τ k) L]
    (I : Ideal (MvPolynomial σ k)) (hI : I.IsRadical)
    (e : τ ≃ Option υ) (E : τ → MvPolynomial σ k)
    (hE : E (e.symm none) = 1) :
    IsReduced (MvPolynomial σ L ⧸
      (I.map (MvPolynomial.map ((algebraMap (MvPolynomial τ k) L).comp C)) ⊔
       Ideal.span {MvPolynomial.map (algebraMap (MvPolynomial τ k) L)
         (bertiniCoefficientHyperplane E)})) := by
  letI : IsReduced (MvPolynomial σ k ⧸ I) :=
    (Ideal.isRadical_iff_quotient_reduced I).mp hI
  let d : τ → MvPolynomial σ k ⧸ I := fun i => Ideal.Quotient.mk I (E i)
  letI : IsReduced (BertiniIncidenceRing d) :=
    incidence_isReduced_of_one e d (by simp [d, hE])
  letI : IsReduced (BertiniGenericIncidenceRing (K := k) d) := inferInstance
  exact isReduced_of_injective
    (bertiniGenericCoefficientQuotientEquiv L I E).toRingHom
    (bertiniGenericCoefficientQuotientEquiv L I E).injective

end CubicTenVariables.GenericReducedAffineHyperplane
