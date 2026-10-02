import TranslatedDepthSeven.AlgebraicallyClosedCoefficientPrime
import TranslatedDepthSeven.QbarPrimeAlgebraicCoefficientExtension
import Mathlib.Algebra.Module.Rat

/-!
# The algebraic-closure test for geometric primeness

Embed `Qbar` in an algebraic closure of the requested coefficient field.
The prime ideal over `Qbar` remains prime there by the tensor-domain theorem.
Faithfully flat contraction then proves primality over the requested field.
This includes transcendental coefficient extensions such as `ℝ`.
-/

namespace TranslatedDepthSeven

noncomputable section

universe u v

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 2000000

noncomputable local instance geometricPrimePolynomialAlgebra
    {K L : Type*} {σ : Type*} [CommSemiring K] [CommSemiring L]
    [Algebra K L] : Algebra (MvPolynomial σ K) (MvPolynomial σ L) :=
  MvPolynomial.algebraMvPolynomial

/-- The `Qbar` prime test implies primality after every coefficient-field
extension, including extensions transcendental over `ℚ`. -/
theorem coefficientExtension_isPrime_of_qbarExtension_isPrime
    {E : Type u} [Field E] [Algebra ℚ E] {σ : Type v} [Finite σ]
    (I : Ideal (MvPolynomial σ ℚ))
    (hQbar : (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime) :
    (I.map (MvPolynomial.map (algebraMap ℚ E))).IsPrime := by
  let Ω := AlgebraicClosure E
  let ι : Qbar →ₐ[ℚ] Ω := IsAlgClosed.lift
  letI : Algebra Qbar Ω := ι.toRingHom.toAlgebra
  letI : IsScalarTower ℚ Qbar Ω := by
    constructor
    intro r x y
    change ι (r • x) * y = r • (ι x * y)
    simp only [Rat.smul_def, map_mul, map_ratCast, mul_assoc]
  let f : MvPolynomial σ ℚ →+* MvPolynomial σ E :=
    MvPolynomial.map (algebraMap ℚ E)
  let g : MvPolynomial σ E →+* MvPolynomial σ Ω :=
    MvPolynomial.map (algebraMap E Ω)
  let h : MvPolynomial σ ℚ →+* MvPolynomial σ Ω :=
    MvPolynomial.map (algebraMap ℚ Ω)
  have hQbarMap :
      (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).map
        (MvPolynomial.map (algebraMap Qbar Ω)) = I.map h := by
    rw [Ideal.map_map]
    congr 1
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [h, ← IsScalarTower.algebraMap_apply]
    · intro i
      simp [h]
  have hprimeΩ : (I.map h).IsPrime := by
    rw [← hQbarMap]
    exact coefficientExtension_isPrime_of_isAlgClosed (L := Ω)
      (I.map (MvPolynomial.map (algebraMap ℚ Qbar))) hQbar
  have hgf : g.comp f = h := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [f, g, h, ← IsScalarTower.algebraMap_apply]
    · intro i
      simp [f, g, h]
  have hmap : (I.map f).map g = I.map h := by
    rw [Ideal.map_map, hgf]
  have hprimeMap : ((I.map f).map g).IsPrime := hmap.symm ▸ hprimeΩ
  have hprimeComap := hprimeMap.comap g
  letI : Module.FaithfullyFlat (MvPolynomial σ E) (MvPolynomial σ Ω) :=
    mvPolynomial_faithfullyFlat
  have hcontract : ((I.map f).map g).comap g = I.map f := by
    change ((I.map f).map (algebraMap (MvPolynomial σ E)
      (MvPolynomial σ Ω))).comap
        (algebraMap (MvPolynomial σ E) (MvPolynomial σ Ω)) = I.map f
    exact Ideal.comap_map_eq_self_of_faithfullyFlat (I.map f)
  rw [hcontract] at hprimeComap
  exact hprimeComap

/-- The literal geometric-primality predicate follows from its algebraic
closure test, with no additional geometric premise. -/
theorem geometricallyPrime_of_qbarCoefficientExtension_isPrime
    {σ : Type v} [Finite σ] (I : Ideal (MvPolynomial σ ℚ))
    (hQbar : (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime) :
    GeometricallyPrimeMvPolynomialIdeal I := by
  intro E _ _
  exact coefficientExtension_isPrime_of_qbarExtension_isPrime (E := E) I hQbar

end

end TranslatedDepthSeven
