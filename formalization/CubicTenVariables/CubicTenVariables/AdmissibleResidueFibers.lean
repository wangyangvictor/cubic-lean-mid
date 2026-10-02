import CubicTenVariables.PrimeSumAdapter
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Tactic

/-!
# Admissible low digits as actual affine fibers

The canonical representatives modulo L are evaluated modulo M without
pretending that this is a ring homomorphism. Their additive carry is an
actual multiple of L. After applying H and quotienting by image(LH), this
becomes an honest additive map. The admissible linear frequencies are its
affine fibers, so all nonempty fibers have the same exact cardinality.
-/

noncomputable section
namespace CubicTenVariables.AdmissibleResidueFibers
open scoped BigOperators Matrix

variable (M L n : ℕ) [NeZero L]

/-- Canonical natural representatives modulo L, then actual casts modulo M. -/
def canonicalLift (v : Fin n → ZMod L) : Fin n → ZMod M :=
  fun i => ((v i).val : ZMod M)

/-- The failure of additivity is exactly a multiple of L in every coordinate. -/
theorem canonicalLift_add_carry (v w : Fin n → ZMod L) :
    ∃ c : Fin n → ZMod M,
      canonicalLift M L n (v+w) = canonicalLift M L n v + canonicalLift M L n w +
        (L : ZMod M) • c := by
  have hd (i : Fin n) : (L : ℤ) ∣
      (((v+w) i).val : ℤ) - (v i).val - (w i).val := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ L).mp
    simp only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val, Pi.add_apply]
    abel
  choose c hc using hd
  refine ⟨fun i => (c i : ZMod M), ?_⟩
  ext i
  have h := congrArg (fun z : ℤ => (z : ZMod M)) (hc i)
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_mul, Pi.add_apply] at h
  simp only [canonicalLift, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination h

/-- The actual image of the scaled matrix over the target residue ring. -/
def scaledImage (H : Matrix (Fin n) (Fin n) (ZMod M)) :
    Submodule (ZMod M) (Fin n → ZMod M) :=
  LinearMap.range (((L : ZMod M) • H).mulVecLin)

/-- The quotient map induced by canonical lifting and the actual matrix H. -/
def quotientMap (H : Matrix (Fin n) (Fin n) (ZMod M)) :
    (Fin n → ZMod L) →+ ((Fin n → ZMod M) ⧸ scaledImage M L n H) where
  toFun v := (scaledImage M L n H).mkQ (H.mulVec (canonicalLift M L n v))
  map_zero' := by
    have hz : canonicalLift M L n 0 = 0 := by ext i; simp [canonicalLift]
    rw [hz, Matrix.mulVec_zero, map_zero]
  map_add' v w := by
    obtain ⟨c, hc⟩ := canonicalLift_add_carry M L n v w
    have hz : (scaledImage M L n H).mkQ (H.mulVec ((L : ZMod M) • c)) = 0 := by
      apply (Submodule.Quotient.mk_eq_zero (scaledImage M L n H)).mpr
      refine ⟨c, ?_⟩
      simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVecLin_apply]
    simp only [hc, Matrix.mulVec_add, map_add, hz, add_zero]

/-- The original literal frequency condition, with a genuine solution in the target modulus. -/
def admissible (H : Matrix (Fin n) (Fin n) (ZMod M))
    (ell : Fin n → ZMod M) (alpha : (ZMod M)ˣ) (v : Fin n → ZMod L) : Prop :=
  ∃ x : Fin n → ZMod M,
    ((L : ZMod M) • H).mulVec x =
      ell + (alpha : ZMod M) • H.mulVec (canonicalLift M L n v)

/-- The frequency condition is precisely a fiber of the proved additive quotient map. -/
theorem admissible_iff_quotientMap_eq
    (H : Matrix (Fin n) (Fin n) (ZMod M))
    (ell : Fin n → ZMod M) (alpha : (ZMod M)ˣ) (v : Fin n → ZMod L) :
    admissible M L n H ell alpha v ↔
      quotientMap M L n H v =
        alpha⁻¹ • (-(scaledImage M L n H).mkQ ell) := by
  change (ell + (alpha : ZMod M) • H.mulVec (canonicalLift M L n v) ∈
    scaledImage M L n H) ↔ _
  rw [← Submodule.Quotient.mk_eq_zero]
  change (scaledImage M L n H).mkQ
    (ell + (alpha : ZMod M) • H.mulVec (canonicalLift M L n v)) = 0 ↔ _
  rw [map_add, map_smul]
  change (scaledImage M L n H).mkQ ell + alpha • quotientMap M L n H v = 0 ↔ _
  rw [add_comm, add_eq_zero_iff_eq_neg, smul_eq_iff_eq_inv_smul]

/-- Every nonempty admissible fiber has exactly the size of the actual homogeneous fiber. -/
theorem card_admissible_eq_homogeneous_of_nonempty
    (H : Matrix (Fin n) (Fin n) (ZMod M))
    (ell : Fin n → ZMod M) (alpha : (ZMod M)ˣ)
    (hv : ∃ v, admissible M L n H ell alpha v) :
    Nat.card {v : Fin n → ZMod L // admissible M L n H ell alpha v} =
      Nat.card {v : Fin n → ZMod L //
        ∃ x : Fin n → ZMod M,
          ((L : ZMod M) • H).mulVec x = H.mulVec (canonicalLift M L n v)} := by
  obtain ⟨v₀, hv₀⟩ := hv
  have he := (admissible_iff_quotientMap_eq M L n H ell alpha v₀).mp hv₀
  have hcard := Nat.card_congr ((quotientMap M L n H).fiberEquivKer v₀)
  have hz (v : Fin n → ZMod L) :
      quotientMap M L n H v = 0 ↔ ∃ x : Fin n → ZMod M,
          ((L : ZMod M) • H).mulVec x = H.mulVec (canonicalLift M L n v) := by
    exact Submodule.Quotient.mk_eq_zero (scaledImage M L n H)
  have heq : {v : Fin n → ZMod L // admissible M L n H ell alpha v} ≃
      (quotientMap M L n H) ⁻¹' {(quotientMap M L n H) v₀} :=
    Equiv.subtypeEquivRight (fun v => by
      change admissible M L n H ell alpha v ↔ quotientMap M L n H v = _
      rw [he]
      exact admissible_iff_quotientMap_eq M L n H ell alpha v)
  have heq0 : (quotientMap M L n H).ker ≃
      {v : Fin n → ZMod L // ∃ x : Fin n → ZMod M,
        ((L : ZMod M) • H).mulVec x = H.mulVec (canonicalLift M L n v)} :=
    Equiv.subtypeEquivRight hz
  exact (Nat.card_congr heq).trans (hcard.trans (Nat.card_congr heq0))

/-- The cardinality is zero or the actual homogeneous count. This statement
has no unproved normal-form or congruence-solubility premise. -/
theorem card_admissible_eq_zero_or_homogeneous
    (H : Matrix (Fin n) (Fin n) (ZMod M))
    (ell : Fin n → ZMod M) (alpha : (ZMod M)ˣ) :
    Nat.card {v : Fin n → ZMod L // admissible M L n H ell alpha v} = 0 ∨
    Nat.card {v : Fin n → ZMod L // admissible M L n H ell alpha v} =
      Nat.card {v : Fin n → ZMod L //
        ∃ x : Fin n → ZMod M,
          ((L : ZMod M) • H).mulVec x = H.mulVec (canonicalLift M L n v)} := by
  classical
  by_cases hv : ∃ v, admissible M L n H ell alpha v
  · exact Or.inr (card_admissible_eq_homogeneous_of_nonempty M L n H ell alpha hv)
  · left
    haveI : IsEmpty {v : Fin n → ZMod L // admissible M L n H ell alpha v} :=
      ⟨fun v => hv ⟨v, v.property⟩⟩
    exact Nat.card_of_isEmpty

end CubicTenVariables.AdmissibleResidueFibers
