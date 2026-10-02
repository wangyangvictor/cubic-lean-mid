import TranslatedDepthSeven.AffinePolynomialChange
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Geometric primeness under affine changes of variables

For an ideal in a polynomial ring over a field, this file uses the literal
base-change definition of geometric primeness: every coefficient-field
extension of the relevant universe is prime.  This is the form actually
needed later for both algebraic-closure components and real coefficient
extension, and it avoids silently importing the theorem equating this
definition with a single algebraic-closure test.  We prove directly that an
invertible scalar affine change of variables preserves the predicate.

The key input is not an abstract geometric interface: it is the displayed
ring-homomorphism identity saying that coefficient extension commutes with
the substitution `X i ↦ y₀ i + r X i`.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

universe u v w

variable {K : Type u} {L : Type v} {σ : Type w}
variable [Field K] [Field L] [Algebra K L]

@[simp]
theorem affinePolynomialChangeAlgEquiv_C
    (y₀ : σ → K) (r : K) (hr : r ≠ 0) (a : K) :
    affinePolynomialChangeAlgEquiv y₀ r hr (C a) = C a := by
  exact (affinePolynomialChangeAlgEquiv y₀ r hr).commutes a

/-- Extending coefficients from `K` to `L` commutes exactly with an
invertible scalar affine substitution. -/
theorem map_affinePolynomialChangeAlgEquiv
    (y₀ : σ → K) (r : K) (hr : r ≠ 0) (f : MvPolynomial σ K) :
    MvPolynomial.map (algebraMap K L)
        (affinePolynomialChangeAlgEquiv y₀ r hr f) =
      affinePolynomialChangeAlgEquiv
        (fun i ↦ algebraMap K L (y₀ i)) (algebraMap K L r)
        ((map_ne_zero (algebraMap K L)).2 hr)
        (MvPolynomial.map (algebraMap K L) f) := by
  let lhs : MvPolynomial σ K →+* MvPolynomial σ L :=
    (MvPolynomial.map (algebraMap K L)).comp
      (affinePolynomialChangeAlgEquiv y₀ r hr).toRingHom
  let rhs : MvPolynomial σ K →+* MvPolynomial σ L :=
    (affinePolynomialChangeAlgEquiv
      (fun i ↦ algebraMap K L (y₀ i)) (algebraMap K L r)
      ((map_ne_zero (algebraMap K L)).2 hr)).toRingHom.comp
        (MvPolynomial.map (algebraMap K L))
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change MvPolynomial.map (algebraMap K L)
          (affinePolynomialChangeAlgEquiv y₀ r hr (C a)) =
        affinePolynomialChangeAlgEquiv
          (fun i ↦ algebraMap K L (y₀ i)) (algebraMap K L r)
          ((map_ne_zero (algebraMap K L)).2 hr)
          (MvPolynomial.map (algebraMap K L) (C a))
      simp
    · intro i
      simp [lhs, rhs]
  change lhs f = rhs f
  exact RingHom.congr_fun hhom f

/-- Ideal extension also commutes exactly with the same affine change of
variables. -/
theorem map_map_affinePolynomialChangeAlgEquiv
    (y₀ : σ → K) (r : K) (hr : r ≠ 0)
    (I : Ideal (MvPolynomial σ K)) :
    (I.map (affinePolynomialChangeAlgEquiv y₀ r hr)).map
        (MvPolynomial.map (algebraMap K L)) =
      (I.map (MvPolynomial.map (algebraMap K L))).map
        (affinePolynomialChangeAlgEquiv
          (fun i ↦ algebraMap K L (y₀ i)) (algebraMap K L r)
          ((map_ne_zero (algebraMap K L)).2 hr)) := by
  change
    Ideal.map (MvPolynomial.map (algebraMap K L))
        (Ideal.map
          (affinePolynomialChangeAlgEquiv y₀ r hr).toRingHom I) =
      Ideal.map
        (affinePolynomialChangeAlgEquiv
          (fun i ↦ algebraMap K L (y₀ i)) (algebraMap K L r)
          ((map_ne_zero (algebraMap K L)).2 hr)).toRingHom
        (Ideal.map (MvPolynomial.map (algebraMap K L)) I)
  rw [Ideal.map_map, Ideal.map_map]
  apply congrArg (fun φ : MvPolynomial σ K →+* MvPolynomial σ L ↦ I.map φ)
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro i
    simp

/-- Literal geometric-primality predicate for a polynomial ideal: every
coefficient-field extension is prime.  The universe level is fixed only to
avoid a universe-polymorphic proposition; it includes every coefficient
field used in this development. -/
def GeometricallyPrimeMvPolynomialIdeal
    (I : Ideal (MvPolynomial σ K)) : Prop :=
  ∀ (E : Type (max u w)) [Field E] [Algebra K E],
    (I.map (MvPolynomial.map (algebraMap K E))).IsPrime

/-- An affine polynomial automorphism preserves geometric primeness, in both
directions. -/
theorem geometricallyPrime_map_affinePolynomialChangeAlgEquiv_iff
    (y₀ : σ → K) (r : K) (hr : r ≠ 0)
    (I : Ideal (MvPolynomial σ K)) :
    GeometricallyPrimeMvPolynomialIdeal
        (I.map (affinePolynomialChangeAlgEquiv y₀ r hr)) ↔
      GeometricallyPrimeMvPolynomialIdeal I := by
  constructor
  · intro h E _ _
    let y₀' : σ → E := fun i ↦ algebraMap K E (y₀ i)
    let r' : E := algebraMap K E r
    have hr' : r' ≠ 0 := (map_ne_zero (algebraMap K E)).2 hr
    let φ : MvPolynomial σ E ≃+* MvPolynomial σ E :=
      (affinePolynomialChangeAlgEquiv y₀' r' hr').toRingEquiv
    have hbase :
        ((I.map (affinePolynomialChangeAlgEquiv y₀ r hr)).map
          (MvPolynomial.map (algebraMap K E))) =
          (I.map (MvPolynomial.map (algebraMap K E))).map φ := by
      simpa [y₀', r', φ] using
        (map_map_affinePolynomialChangeAlgEquiv
          (L := E) y₀ r hr I)
    have hprime : ((I.map (MvPolynomial.map (algebraMap K E))).map φ).IsPrime := by
      rw [← hbase]
      exact h E
    letI : ((I.map (MvPolynomial.map (algebraMap K E))).map φ).IsPrime := hprime
    have hback :
        (((I.map (MvPolynomial.map (algebraMap K E))).map φ).map
          φ.symm).IsPrime :=
      Ideal.map_isPrime_of_equiv φ.symm
    have hundo :
        ((I.map (MvPolynomial.map (algebraMap K E))).map φ).map φ.symm =
          I.map (MvPolynomial.map (algebraMap K E)) :=
      Ideal.map_of_equiv φ
    rw [hundo] at hback
    exact hback
  · intro h E _ _
    let y₀' : σ → E := fun i ↦ algebraMap K E (y₀ i)
    let r' : E := algebraMap K E r
    have hr' : r' ≠ 0 := (map_ne_zero (algebraMap K E)).2 hr
    let φ : MvPolynomial σ E ≃+* MvPolynomial σ E :=
      (affinePolynomialChangeAlgEquiv y₀' r' hr').toRingEquiv
    have hbase :
        ((I.map (affinePolynomialChangeAlgEquiv y₀ r hr)).map
          (MvPolynomial.map (algebraMap K E))) =
          (I.map (MvPolynomial.map (algebraMap K E))).map φ := by
      simpa [y₀', r', φ] using
        (map_map_affinePolynomialChangeAlgEquiv
          (L := E) y₀ r hr I)
    rw [hbase]
    letI : (I.map (MvPolynomial.map (algebraMap K E))).IsPrime := h E
    exact Ideal.map_isPrime_of_equiv φ

end

end TranslatedDepthSeven
