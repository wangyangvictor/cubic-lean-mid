import HessianTheorem11.PolynomialCoordinateEquiv
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! Algebraic dimension bridges for cuts. No geometric input is used.
Translations identify the heights of closed points of affine space;
Noether normalization and going-down extend full height to every closed
point of an integral affine algebra. -/
noncomputable section
namespace HessianTheorem11.UnconditionalCutHeight
open MvPolynomial Ideal

theorem integral_dimension_le {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] :
    ringKrullDim S ≤ ringKrullDim R := by
  apply Order.krullDim_le_of_strictMono (algebraMap R S).specComap
  intro P Q hPQ
  obtain ⟨x, hxQ, hxP⟩ := SetLike.exists_of_lt hPQ
  exact Ideal.comap_lt_comap_of_integral_mem_sdiff hPQ.le ⟨hxQ, hxP⟩
    (Algebra.IsIntegral.isIntegral x)

def translation {n : ℕ} (v : GeometricPoint n) :
    PolynomialCoordinateEquiv (Fin n) (Fin n) where
  forward i := X i + C (v i)
  inverse i := X i - C (v i)
  forward_inverse i := by simp
  inverse_forward i := by simp

@[simp] theorem translation_forward {n : ℕ} (v x : GeometricPoint n) :
    (translation v).forwardMap x = x + v := by
  ext i
  simp [translation, PolynomialCoordinateEquiv.forwardMap, polynomialMap]

theorem point_height_eq {n : ℕ} (x y : GeometricPoint n) :
    (vanishingIdeal GeometricField {x}).height =
      (vanishingIdeal GeometricField {y}).height := by
  let E := translation (y - x)
  have he : E.forwardMap '' {x} = {y} := by
    simp only [Set.image_singleton, E, translation_forward]
    congr 1
    abel
  have hi := E.vanishingIdeal_image {x}
  rw [he] at hi
  rw [hi]
  exact (E.pullbackAlgEquiv.symm.toRingEquiv.height_map _).symm

/-- Every maximal ideal of a polynomial ring over Qbar has full height.
This uses actual translations and the Nullstellensatz, not a dimension formula. -/
theorem polynomial_maximal_height {n : ℕ}
    (m : Ideal (GeometricPolynomial n)) [m.IsMaximal] :
    (m.height : Dimension) = ringKrullDim (GeometricPolynomial n) := by
  apply le_antisymm (Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top')
  apply (ringKrullDim_le_iff_isMaximal_height_le _).mpr
  intro l hl
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal
    GeometricField (show m.IsMaximal from inferInstance)
  obtain ⟨y, hy⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal
    GeometricField hl
  rw [hx, hy, point_height_eq x y]

/-- All closed points of an integral finite-type Qbar algebra have full
height. Noether normalization supplies an integral polynomial subalgebra;
normal-base going-down supplies the height lower bound. -/
theorem finiteType_maximal_height (A : Type*) [CommRing A] [IsDomain A]
    [Algebra GeometricField A] [Algebra.FiniteType GeometricField A]
    (m : Ideal A) [m.IsMaximal] : (m.height : Dimension) = ringKrullDim A := by
  obtain ⟨s, g, hginj, hgint⟩ :=
    exists_integral_inj_algHom_of_fg GeometricField A
  let B := MvPolynomial (Fin s) GeometricField
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr hginj
  letI : Algebra.IsIntegral B A := ⟨hgint⟩
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing GeometricField A
  have hm : (m.under B).IsMaximal := inferInstance
  have hheight := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (m.under B) m
  have hle : (m.under B).height ≤ m.height := by
    rw [hheight]
    exact le_self_add
  apply le_antisymm (Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top')
  calc
    ringKrullDim A ≤ ringKrullDim B := integral_dimension_le
    _ = ((m.under B).height : Dimension) := (polynomial_maximal_height _).symm
    _ ≤ (m.height : Dimension) := by exact_mod_cast hle

/-- An explicit Noether-normalization embedding preserves actual Krull
dimension. This is useful independently of the cut theorem. -/
theorem normalization_dimension_eq {n : ℕ} (A : Type*) [CommRing A]
    [IsDomain A] [IsNoetherianRing A] [Algebra GeometricField A]
    (g : GeometricPolynomial n →ₐ[GeometricField] A)
    (hginj : Function.Injective g) (hgint : g.IsIntegral) :
    ringKrullDim A = ringKrullDim (GeometricPolynomial n) := by
  let B := GeometricPolynomial n
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr hginj
  letI : Algebra.IsIntegral B A := ⟨hgint⟩
  apply le_antisymm integral_dimension_le
  obtain ⟨m, hm, _⟩ := Ideal.exists_le_maximal (⊥ : Ideal A) bot_ne_top
  letI : m.IsMaximal := hm
  have hheight := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (m.under B) m
  have hle : (m.under B).height ≤ m.height := by
    rw [hheight]
    exact le_self_add
  calc
    ringKrullDim B = ((m.under B).height : Dimension) :=
      (polynomial_maximal_height _).symm
    _ ≤ (m.height : Dimension) := by exact_mod_cast hle
    _ ≤ ringKrullDim A := Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'

end HessianTheorem11.UnconditionalCutHeight
