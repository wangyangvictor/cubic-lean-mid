import CubicTenVariables.LiftingCharacters
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Units.Equiv

/-! Exact standard-character CRT decomposition, with the inverse-modulus
twists retained and only the actual CRT projections between residue rings. -/

noncomputable section
namespace CubicTenVariables.CRTCharacters

open LiftingCharacters PrimeSumAdapter

variable {m n : ℕ}

def leftProjection (h : m.Coprime n) : ZMod (m*n) →+* ZMod m :=
  (RingHom.fst (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h).toRingHom

def rightProjection (h : m.Coprime n) : ZMod (m*n) →+* ZMod n :=
  (RingHom.snd (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h).toRingHom

def leftTwist (h : m.Coprime n) : (ZMod m)ˣ := (ZMod.unitOfCoprime n h.symm)⁻¹
def rightTwist (h : m.Coprime n) : (ZMod n)ˣ := (ZMod.unitOfCoprime m h)⁻¹

@[simp] theorem modulus_mul_leftTwist (h : m.Coprime n) :
    (n : ZMod m) * (leftTwist h : ZMod m) = 1 := by
  change (ZMod.unitOfCoprime n h.symm : ZMod m) *
    (↑((ZMod.unitOfCoprime n h.symm)⁻¹) : ZMod m) = 1
  exact Units.mul_inv _

@[simp] theorem modulus_mul_rightTwist (h : m.Coprime n) :
    (m : ZMod n) * (rightTwist h : ZMod n) = 1 := by
  change (ZMod.unitOfCoprime m h : ZMod n) *
    (↑((ZMod.unitOfCoprime m h)⁻¹) : ZMod n) = 1
  exact Units.mul_inv _

/-- CRT reconstruction using actual integer representatives of the twisted projections. -/
theorem reconstruction (h : m.Coprime n) [NeZero m] [NeZero n] (x : ZMod (m*n)) :
    x = ((n * ((leftTwist h : ZMod m) * leftProjection h x).val +
      m * ((rightTwist h : ZMod n) * rightProjection h x).val : ℕ) : ZMod (m*n)) := by
  apply (ZMod.chineseRemainder h).injective
  ext
  · change leftProjection h x = leftProjection h _
    rw [map_natCast]
    push_cast
    simp only [ZMod.natCast_self, zero_mul, add_zero, ZMod.natCast_zmod_val,
      ← mul_assoc, modulus_mul_leftTwist, one_mul]
  · change rightProjection h x = rightProjection h _
    rw [map_natCast]
    push_cast
    simp only [ZMod.natCast_self, zero_mul, zero_add, ZMod.natCast_zmod_val,
      ← mul_assoc, modulus_mul_rightTwist, one_mul]

/-- The standard character at a product modulus is the product of the
two standard characters of the inverse-modulus-twisted projections. -/
theorem stdAddChar_crt (h : m.Coprime n) [NeZero m] [NeZero n] (x : ZMod (m*n)) :
    ZMod.stdAddChar x =
      ZMod.stdAddChar ((leftTwist h : ZMod m) * leftProjection h x) *
      ZMod.stdAddChar ((rightTwist h : ZMod n) * rightProjection h x) := by
  let a := ((leftTwist h : ZMod m) * leftProjection h x).val
  let b := ((rightTwist h : ZMod n) * rightProjection h x).val
  have hx : x = (((n : ℤ) * a + (m : ℤ) * b : ℤ) : ZMod (m*n)) := by
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_add, Nat.cast_mul,
      a, b] using reconstruction h x
  calc
    ZMod.stdAddChar x = residueExponential (m*n) ((n : ℤ)*a+(m : ℤ)*b) := by
      rw [hx, residueExponential_eq_stdAddChar]
    _ = residueExponential m a * residueExponential n b := by
      rw [residueExponential_add, residueExponential_mul_modulus m n]
      congr 1
      simpa only [Nat.mul_comm] using residueExponential_mul_modulus n m (b : ℤ)
    _ = _ := by
      rw [residueExponential_eq_stdAddChar, residueExponential_eq_stdAddChar]
      simp only [Int.cast_natCast, a, b, ZMod.natCast_zmod_val]

/-- Coordinatewise actual CRT, grouped into its two vector components. -/
def vectorEquiv (h : m.Coprime n) (d : ℕ) :
    (Fin d → ZMod (m*n)) ≃ ((Fin d → ZMod m) × (Fin d → ZMod n)) :=
  (Equiv.piCongrRight fun _ => (ZMod.chineseRemainder h).toEquiv).trans
    (Equiv.arrowProdEquivProdArrow (Fin d) (fun _ => ZMod m) (fun _ => ZMod n))

@[simp] theorem vectorEquiv_fst (h : m.Coprime n) (d : ℕ)
    (x : Fin d → ZMod (m*n)) (i : Fin d) :
    (vectorEquiv h d x).1 i = leftProjection h (x i) := rfl

@[simp] theorem vectorEquiv_snd (h : m.Coprime n) (d : ℕ)
    (x : Fin d → ZMod (m*n)) (i : Fin d) :
    (vectorEquiv h d x).2 i = rightProjection h (x i) := rfl

/-- The genuine CRT equivalence on units. -/
def unitEquiv (h : m.Coprime n) : (ZMod (m*n))ˣ ≃ ((ZMod m)ˣ × (ZMod n)ˣ) :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).toEquiv.trans
    MulEquiv.prodUnits.toEquiv

@[simp] theorem unitEquiv_fst_coe (h : m.Coprime n) (u : (ZMod (m*n))ˣ) :
    ((unitEquiv h u).1 : ZMod m) = leftProjection h (u : ZMod (m*n)) := rfl

@[simp] theorem unitEquiv_snd_coe (h : m.Coprime n) (u : (ZMod (m*n))ˣ) :
    ((unitEquiv h u).2 : ZMod n) = rightProjection h (u : ZMod (m*n)) := rfl

end CubicTenVariables.CRTCharacters
