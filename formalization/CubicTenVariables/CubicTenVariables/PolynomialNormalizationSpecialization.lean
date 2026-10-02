import CubicTenVariables.IntegralPrimeSpecialization
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Field.ZMod

/-! A finite injective polynomial normalization retains its dimension under
surjective coefficient specialization to a field. This is the form needed
for integral parameter evaluations into a prime field. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.PolynomialNormalizationSpecialization
open MvPolynomial

universe u v

/-- Kernel of the induced quotient map under a surjective ring map. -/
theorem ker_quotientMap_of_surjective
    {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (f : R →+* S) (hf : Function.Surjective f) :
    RingHom.ker (Ideal.quotientMap (I.map f) f Ideal.le_comap_map) =
      (RingHom.ker f).map (Ideal.Quotient.mk I) := by
  rw [Ideal.quotientMap, Ideal.ker_quotient_lift,
    ← RingHom.comap_ker, Ideal.mk_ker,
    Ideal.comap_map_of_surjective f hf,
    Ideal.map_sup, Ideal.map_mk_eq_bot_of_le le_rfl, bot_sup_eq]
  rfl

/-- The literal specialized polynomial quotient has the same dimension as
the specialized parameter polynomial ring. The only compatibility hypothesis
is the displayed equality of the two concrete homomorphisms. -/
theorem ringKrullDim_eq_of_surjective_coefficients
    {B : Type u} {L : Type v} [CommRing B] [Field L] {N d : ℕ}
    (I : Ideal (MvPolynomial (Fin N) B))
    (g : MvPolynomial (Fin d) B →ₐ[B] (MvPolynomial (Fin N) B ⧸ I))
    (hinj : Function.Injective g) (hint : g.toRingHom.IsIntegral)
    (ρ : B →+* L) (hρ : Function.Surjective ρ)
    (g' : MvPolynomial (Fin d) L →ₐ[L]
      (MvPolynomial (Fin N) L ⧸ I.map (MvPolynomial.map ρ)))
    (hcomm :
      (Ideal.quotientMap (I.map (MvPolynomial.map ρ))
        (MvPolynomial.map ρ) Ideal.le_comap_map).comp g.toRingHom =
      g'.toRingHom.comp (MvPolynomial.map ρ)) :
    ringKrullDim (MvPolynomial (Fin N) L ⧸ I.map (MvPolynomial.map ρ)) =
      ringKrullDim (MvPolynomial (Fin d) L) := by
  letI : Algebra (MvPolynomial (Fin d) B) (MvPolynomial (Fin N) B ⧸ I) :=
    g.toRingHom.toAlgebra
  letI : Algebra.IsIntegral (MvPolynomial (Fin d) B)
      (MvPolynomial (Fin N) B ⧸ I) := ⟨hint⟩
  have hgi : Function.Injective (algebraMap (MvPolynomial (Fin d) B)
      (MvPolynomial (Fin N) B ⧸ I)) := hinj
  apply IntegralPrimeSpecialization.specialized_ringKrullDim_eq
    (R := MvPolynomial (Fin d) B) (S := MvPolynomial (Fin N) B ⧸ I)
    hgi (MvPolynomial.map ρ)
    (Ideal.quotientMap (I.map (MvPolynomial.map ρ))
      (MvPolynomial.map ρ) Ideal.le_comap_map)
    g'.toRingHom (MvPolynomial.map_surjective ρ hρ)
    (Ideal.quotientMap_surjective (MvPolynomial.map_surjective ρ hρ)) hcomm
  rw [ker_quotientMap_of_surjective I (MvPolynomial.map ρ)
      (MvPolynomial.map_surjective ρ hρ),
    MvPolynomial.ker_map, MvPolynomial.ker_map, Ideal.map_map, Ideal.map_map]
  congr 1
  ext b
  exact (g.commutes b).symm

/-- The quotient homomorphism defined by displayed normalization coordinates. -/
def normalizationHom {B : Type*} [CommRing B] {N d : ℕ}
    (I : Ideal (MvPolynomial (Fin N) B)) (q : Fin d → MvPolynomial (Fin N) B) :
    MvPolynomial (Fin d) B →ₐ[B] (MvPolynomial (Fin N) B ⧸ I) :=
  (Ideal.Quotient.mkₐ B I).comp (MvPolynomial.aeval q)

/-- Coefficient specialization commutes with the literal normalization map. -/
theorem normalizationHom_map_comm
    {B L : Type*} [CommRing B] [CommRing L] {N d : ℕ}
    (I : Ideal (MvPolynomial (Fin N) B)) (q : Fin d → MvPolynomial (Fin N) B)
    (ρ : B →+* L) :
    (Ideal.quotientMap (I.map (MvPolynomial.map ρ))
      (MvPolynomial.map ρ) Ideal.le_comap_map).comp (normalizationHom I q).toRingHom =
    (normalizationHom (I.map (MvPolynomial.map ρ))
      (fun j => MvPolynomial.map ρ (q j))).toRingHom.comp (MvPolynomial.map ρ) := by
  apply MvPolynomial.ringHom_ext
  · intro b
    simp [normalizationHom]
  · intro j
    simp [normalizationHom]

/-- Generic injectivity descends along an injective coefficient map. In
particular this recovers the injection discarded by a fraction-field model. -/
theorem normalizationHom_injective_of_map_injective
    {B L : Type*} [CommRing B] [CommRing L] {N d : ℕ}
    (I : Ideal (MvPolynomial (Fin N) B)) (q : Fin d → MvPolynomial (Fin N) B)
    (ρ : B →+* L) (hρ : Function.Injective ρ)
    (hgeneric : Function.Injective (normalizationHom (I.map (MvPolynomial.map ρ))
      (fun j => MvPolynomial.map ρ (q j)))) :
    Function.Injective (normalizationHom I q) := by
  intro x y hxy
  apply MvPolynomial.map_injective ρ hρ
  apply hgeneric
  have hc := normalizationHom_map_comm I q ρ
  have hx := RingHom.congr_fun hc x
  have hy := RingHom.congr_fun hc y
  exact hx.symm.trans ((congrArg (Ideal.quotientMap (I.map (MvPolynomial.map ρ))
    (MvPolynomial.map ρ) Ideal.le_comap_map) hxy).trans hy)

/-- A literal normalization keeps its exact parameter dimension under a
surjective coefficient specialization to a field. -/
theorem normalizationHom_specialized_dimension
    {B : Type u} {L : Type v} [CommRing B] [Field L] {N d : ℕ}
    (I : Ideal (MvPolynomial (Fin N) B)) (q : Fin d → MvPolynomial (Fin N) B)
    (hinj : Function.Injective (normalizationHom I q))
    (hint : (normalizationHom I q).toRingHom.IsIntegral)
    (ρ : B →+* L) (hρ : Function.Surjective ρ) :
    ringKrullDim (MvPolynomial (Fin N) L ⧸ I.map (MvPolynomial.map ρ)) =
      ringKrullDim (MvPolynomial (Fin d) L) :=
  ringKrullDim_eq_of_surjective_coefficients I (normalizationHom I q) hinj hint
    ρ hρ (normalizationHom (I.map (MvPolynomial.map ρ))
      (fun j => MvPolynomial.map ρ (q j))) (normalizationHom_map_comm I q ρ)

/-- The displayed number of normalization parameters is bounded by the
actual specialized quotient dimension. -/
theorem normalization_parameter_le_of_specialized_dimension_le
    {B : Type u} {L : Type v} [CommRing B] [Field L] {N d j : ℕ}
    (I : Ideal (MvPolynomial (Fin N) B)) (q : Fin d → MvPolynomial (Fin N) B)
    (hinj : Function.Injective (normalizationHom I q))
    (hint : (normalizationHom I q).toRingHom.IsIntegral)
    (ρ : B →+* L) (hρ : Function.Surjective ρ)
    (hdim : ringKrullDim (MvPolynomial (Fin N) L ⧸ I.map (MvPolynomial.map ρ)) ≤
      (j : WithBot ℕ∞)) :
    d ≤ j := by
  have hlower := ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial
    (R := L) (Fin d)
  simp only [ringKrullDim_eq_zero_of_field, zero_add, Nat.card_fin] at hlower
  rw [← normalizationHom_specialized_dimension I q hinj hint ρ hρ] at hlower
  exact_mod_cast hlower.trans hdim

/-- Every ring homomorphism into a prime field is surjective, so the
parameter bound applies to all actual integral parameter evaluations. -/
theorem normalization_parameter_le_zmod
    {B : Type u} [CommRing B] {N d j p : ℕ} [Fact p.Prime]
    (I : Ideal (MvPolynomial (Fin N) B)) (q : Fin d → MvPolynomial (Fin N) B)
    (hinj : Function.Injective (normalizationHom I q))
    (hint : (normalizationHom I q).toRingHom.IsIntegral)
    (ρ : B →+* ZMod p)
    (hdim : ringKrullDim (MvPolynomial (Fin N) (ZMod p) ⧸ I.map (MvPolynomial.map ρ)) ≤
      (j : WithBot ℕ∞)) :
    d ≤ j := by
  exact normalization_parameter_le_of_specialized_dimension_le
    (B := B) (L := ZMod p) (N := N) (d := d) (j := j) I q hinj hint ρ
    (ZMod.ringHom_surjective ρ) hdim

end CubicTenVariables.PolynomialNormalizationSpecialization
