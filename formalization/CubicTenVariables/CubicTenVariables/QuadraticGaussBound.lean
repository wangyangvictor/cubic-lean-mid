import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-!
# A finite quadratic Gauss bound over every nonzero modulus

The sum here uses the literal standard character exp(2πit/d). Its phase is
an actual function on all vectors over ZMod d, satisfying the displayed
quadratic translation identity with an actual matrix B. Orthogonality and
finite differencing prove that the squared norm is at most d^n times the
number of vectors killed by B. No field hypothesis or division by 2 occurs;
in particular even moduli, modulus 1, and dimension 0 are included.
-/

noncomputable section
namespace CubicTenVariables.QuadraticGaussBound

open scoped BigOperators

variable (d n : ℕ) [NeZero d]

/-- The full quadratic exponential sum, with the positive standard phase. -/
def gaussSum (Q : (Fin n → ZMod d) → ZMod d) : ℂ :=
  ∑ z, ZMod.stdAddChar (Q z)

/-- The literal finite kernel of the displayed polar matrix. -/
def kernelVectors (B : Matrix (Fin n) (Fin n) (ZMod d)) :
    Finset (Fin n → ZMod d) :=
  Finset.univ.filter (fun h => B.mulVec h = 0)

@[simp] theorem norm_stdAddChar (a : ZMod d) : ‖ZMod.stdAddChar a‖ = 1 := by
  simp [ZMod.stdAddChar_apply]

@[simp] theorem stdAddChar_mul_conj (a : ZMod d) :
    ZMod.stdAddChar a * starRingEnd ℂ (ZMod.stdAddChar a) = 1 := by
  rw [Complex.mul_conj]
  simp [Complex.normSq_eq_norm_sq]

/-- The actual linear character on the vector module. -/
def linearCharacter (b : Fin n → ZMod d) : AddChar (Fin n → ZMod d) ℂ where
  toFun z := ZMod.stdAddChar (dotProduct z b)
  map_zero_eq_one' := by simp
  map_add_eq_mul' z w := by rw [add_dotProduct, AddChar.map_add_eq_mul]

theorem linearCharacter_ne_one (b : Fin n → ZMod d) (hb : b ≠ 0) :
    linearCharacter d n b ≠ 1 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, b j ≠ 0 := by
    by_contra! hz
    exact hb (funext hz)
  apply AddChar.ne_one_iff.mpr
  refine ⟨Pi.single j 1, ?_⟩
  change ZMod.stdAddChar (dotProduct (Pi.single j 1) b) ≠ 1
  simp only [single_dotProduct, one_mul]
  intro he
  apply hj
  apply ZMod.injective_stdAddChar
  simpa using he

/-- Orthogonality on the full finite module, including a nonfield modulus. -/
theorem sum_linear_phase (b : Fin n → ZMod d) :
    (∑ z : Fin n → ZMod d, ZMod.stdAddChar (dotProduct z b)) =
      if b = 0 then (d : ℂ) ^ n else 0 := by
  classical
  by_cases hb : b = 0
  · simp [hb, ZMod.card]
  · rw [if_neg hb]
    exact AddChar.sum_eq_zero_of_ne_one (linearCharacter_ne_one d n b hb)

/-- Exact differencing identity before taking the triangle inequality. -/
theorem gaussSum_mul_conj (Q : (Fin n → ZMod d) → ZMod d)
    (B : Matrix (Fin n) (Fin n) (ZMod d))
    (hQ : ∀ z h, Q (z + h) = Q z + Q h + dotProduct z (B.mulVec h)) :
    gaussSum d n Q * starRingEnd ℂ (gaussSum d n Q) =
      (d : ℂ) ^ n * ∑ h ∈ kernelVectors d n B, ZMod.stdAddChar (Q h) := by
  classical
  have hshift (z : Fin n → ZMod d) :
      (∑ h, ZMod.stdAddChar (Q (z + h))) = gaussSum d n Q := by
    exact Equiv.sum_comp (Equiv.addLeft z) (fun h => ZMod.stdAddChar (Q h))
  calc
    gaussSum d n Q * starRingEnd ℂ (gaussSum d n Q) =
        ∑ z, (∑ h, ZMod.stdAddChar (Q (z + h))) *
          starRingEnd ℂ (ZMod.stdAddChar (Q z)) := by
      simp_rw [hshift]
      rw [gaussSum, map_sum, Finset.mul_sum]
    _ = ∑ h, ∑ z, ZMod.stdAddChar (Q (z + h)) *
          starRingEnd ℂ (ZMod.stdAddChar (Q z)) := by
      simp_rw [Finset.sum_mul]
      exact Finset.sum_comm
    _ = ∑ h, ZMod.stdAddChar (Q h) *
          ∑ z, ZMod.stdAddChar (dotProduct z (B.mulVec h)) := by
      apply Finset.sum_congr rfl
      intro h _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      rw [hQ, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
      calc
        _ = (ZMod.stdAddChar (Q z) * starRingEnd ℂ (ZMod.stdAddChar (Q z))) *
            (ZMod.stdAddChar (Q h) * ZMod.stdAddChar (dotProduct z (B.mulVec h))) := by ring
        _ = _ := by rw [stdAddChar_mul_conj, one_mul]
    _ = (d : ℂ) ^ n * ∑ h ∈ kernelVectors d n B, ZMod.stdAddChar (Q h) := by
      simp_rw [sum_linear_phase]
      simp [kernelVectors, Finset.sum_filter, Finset.mul_sum, mul_ite, mul_comm]

/-- The squared norm of the literal sum is bounded by the ambient
cardinality times the cardinality of the actual polar-matrix kernel. -/
theorem norm_gaussSum_sq_le (Q : (Fin n → ZMod d) → ZMod d)
    (B : Matrix (Fin n) (Fin n) (ZMod d))
    (hQ : ∀ z h, Q (z + h) = Q z + Q h + dotProduct z (B.mulVec h)) :
    ‖gaussSum d n Q‖ ^ 2 ≤ (d : ℝ) ^ n * (kernelVectors d n B).card := by
  classical
  have he := congrArg norm (gaussSum_mul_conj d n Q B hQ)
  have hk : ‖∑ h ∈ kernelVectors d n B, ZMod.stdAddChar (Q h)‖ ≤
      ((kernelVectors d n B).card : ℝ) := by
    calc
      _ ≤ ∑ h ∈ kernelVectors d n B, ‖ZMod.stdAddChar (Q h)‖ := norm_sum_le _ _
      _ = _ := by simp
  have he' : ‖gaussSum d n Q‖ ^ 2 =
      (d : ℝ) ^ n * ‖∑ h ∈ kernelVectors d n B, ZMod.stdAddChar (Q h)‖ := by
    simpa [norm_mul, norm_pow, Complex.norm_conj, pow_two] using he
  rw [he']
  exact mul_le_mul_of_nonneg_left hk (pow_nonneg (Nat.cast_nonneg d) n)

/-- A formulation with the full sum and the kernel subtype both displayed. -/
theorem norm_sum_sq_le_card_kernel (Q : (Fin n → ZMod d) → ZMod d)
    (B : Matrix (Fin n) (Fin n) (ZMod d))
    (hQ : ∀ z h, Q (z + h) = Q z + Q h + dotProduct z (B.mulVec h)) :
    ‖∑ z : Fin n → ZMod d, ZMod.stdAddChar (Q z)‖ ^ 2 ≤
      (d : ℝ) ^ n * Nat.card {h : Fin n → ZMod d // B.mulVec h = 0} := by
  classical
  simpa only [gaussSum, kernelVectors, Nat.card_eq_fintype_card, Fintype.card_subtype]
    using norm_gaussSum_sq_le d n Q B hQ

/-- Multiplying the quadratic phase by a unit and adding any linear phase
preserves the same kernel-cardinality bound, over composite moduli as well. -/
theorem norm_mixed_sum_sq_le (Q : (Fin n → ZMod d) → ZMod d)
    (B : Matrix (Fin n) (Fin n) (ZMod d))
    (hQ : ∀ z h, Q (z + h) = Q z + Q h + dotProduct z (B.mulVec h))
    (u : (ZMod d)ˣ) (v : Fin n → ZMod d) :
    ‖∑ z : Fin n → ZMod d,
      ZMod.stdAddChar ((u : ZMod d) * Q z + dotProduct v z)‖ ^ 2 ≤
      (d : ℝ) ^ n * Nat.card {h : Fin n → ZMod d // B.mulVec h = 0} := by
  classical
  let Q' := fun z => (u : ZMod d) * Q z + dotProduct v z
  have hQ' : ∀ z h, Q' (z + h) = Q' z + Q' h +
      dotProduct z (((u : ZMod d) • B).mulVec h) := by
    intro z h
    dsimp [Q']
    rw [hQ, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul]
    simp only [smul_eq_mul]
    ring
  simpa only [Q', Matrix.smul_mulVec, u.isUnit.smul_eq_zero] using
    norm_sum_sq_le_card_kernel d n Q' ((u : ZMod d) • B) hQ'

end CubicTenVariables.QuadraticGaussBound
