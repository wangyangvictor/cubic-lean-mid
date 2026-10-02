import TranslatedDepthSeven.IntegerGridAvoidance
import TranslatedDepthSeven.PrimitiveDirectionNormalization
import TranslatedDepthSeven.AffinePolynomialChange
import TranslatedDepthSeven.HomogeneousCone

/-!
# A bounded primitive direction in a nonempty open subset of a line

If a polynomial does not vanish identically on the span of two independent
integral vectors, a bounded integral linear combination avoids its zero
set. Multiplication of the restricted polynomial by its first variable
ensures that the selected vector is nonzero, including for a constant
polynomial. For a homogeneous polynomial, primitive normalization preserves
nonvanishing and cannot increase the vector's coordinates.

In the plane application the polynomial is a nonzero restriction of a
Jacobian minor. The argument uses only the finite grid and integer Bezout.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

/-- Restrict an integral polynomial to the span of two displayed vectors. -/
def integralTwoVectorRestriction {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (v w : IntVector n) :
    MvPolynomial (Fin 2) ℤ :=
  aeval (fun i ↦ C (v i) * X 0 + C (w i) * X 1) f

theorem eval_integralTwoVectorRestriction {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (v w : IntVector n)
    (a : Fin 2 → ℤ) :
    eval a (integralTwoVectorRestriction f v w) =
      eval (fun i ↦ a 0 * v i + a 1 * w i) f := by
  unfold integralTwoVectorRestriction
  change ((aeval a).comp
    (aeval fun i ↦ C (v i) * X 0 + C (w i) * X 1)) f = _
  have hcomp : (aeval a).comp
      (aeval fun i ↦ C (v i) * X 0 + C (w i) * X 1) =
      aeval (fun i ↦ a 0 * v i + a 1 * w i) := by
    ext i
    simp [mul_comm]
  rw [hcomp]
  rfl

theorem totalDegree_integralTwoVectorRestriction_le {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (v w : IntVector n) :
    (integralTwoVectorRestriction f v w).totalDegree ≤ f.totalDegree := by
  apply totalDegree_aeval_le_of_totalDegree_le_one
  intro i
  apply (totalDegree_add _ _).trans
  apply max_le
  · exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])
  · exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])

/-- A nonvanishing restriction has a nonzero integral representative with
coefficients in `{0,...,D+1}`. The extra factor `X 0` excludes zero even
when the original polynomial is constant. -/
theorem exists_bounded_twoVectorCombination_eval_ne_zero
    {n D : ℕ} (f : MvPolynomial (Fin n) ℤ) (v w : IntVector n)
    (hdegree : f.totalDegree ≤ D)
    (hrestrict : integralTwoVectorRestriction f v w ≠ 0)
    (hminor : ∃ i j, v i * w j - v j * w i ≠ 0) :
    ∃ a b : ℤ,
      (0 < a ∧ a ≤ D + 1) ∧ (0 ≤ b ∧ b ≤ D + 1) ∧
      (fun i ↦ a * v i + b * w i) ≠ 0 ∧
      eval (fun i ↦ a * v i + b * w i) f ≠ 0 := by
  let g := integralTwoVectorRestriction f v w * X (0 : Fin 2)
  have hg : g ≠ 0 := mul_ne_zero hrestrict (X_ne_zero 0)
  have hgdegree : g.totalDegree ≤ D + 1 := by
    exact (totalDegree_mul _ _).trans (by
      simpa only [totalDegree_X] using Nat.add_le_add_right
        ((totalDegree_integralTwoVectorRestriction_le f v w).trans hdegree) 1)
  obtain ⟨a, ha, heval⟩ :=
    exists_nonzero_eval_on_nonnegativeIntegerGrid g hg hgdegree
  have hfactor :
      eval (fun i ↦ a 0 * v i + a 1 * w i) f * a 0 ≠ 0 := by
    simpa only [g, map_mul, eval_X, eval_integralTwoVectorRestriction]
      using heval
  have ha0 : 0 < a 0 := lt_of_le_of_ne (ha 0).1
    (Ne.symm (mul_ne_zero_iff.mp hfactor).2)
  refine ⟨a 0, a 1, ⟨ha0, (ha 0).2⟩, ha 1, ?_,
    (mul_ne_zero_iff.mp hfactor).1⟩
  intro hzero
  obtain ⟨i, j, hij⟩ := hminor
  have hi : a 0 * v i + a 1 * w i = 0 := congrFun hzero i
  have hj : a 0 * v j + a 1 * w j = 0 := congrFun hzero j
  have hproduct : a 0 * (v i * w j - v j * w i) = 0 := by
    nlinarith [congrArg (fun t : ℤ ↦ t * w j) hi,
      congrArg (fun t : ℤ ↦ t * w i) hj]
  exact (mul_ne_zero (ne_of_gt ha0) hij) hproduct

/-- A homogeneous nonvanishing condition on a rational line has a small
primitive integral witness. The proportionality is retained explicitly,
so every other homogeneous equation vanishing on the line also vanishes
at the selected witness. -/
theorem exists_bounded_primitiveDirection_twoVectorRestriction
    {n D d U : ℕ} (f : MvPolynomial (Fin n) ℤ)
    (v w : IntVector n) (hfhom : f.IsHomogeneous d)
    (hdegree : f.totalDegree ≤ D)
    (hrestrict : integralTwoVectorRestriction f v w ≠ 0)
    (hminor : ∃ i j, v i * w j - v j * w i ≠ 0)
    (hv : ∀ i, (v i).natAbs ≤ U) (hw : ∀ i, (w i).natAbs ≤ U) :
    ∃ h : IntVector n, ∃ a b : ℤ, ∃ r : ℚ,
      PrimitiveDirection h ∧ directionHeight h ≤ 2 * (D + 1) * U ∧
      r ≠ 0 ∧
      (∀ i, (h i : ℚ) = r * ((a * v i + b * w i : ℤ) : ℚ)) ∧
      eval h f ≠ 0 := by
  obtain ⟨a, b, ha, hb, hnonzero, heval⟩ :=
    exists_bounded_twoVectorCombination_eval_ne_zero
      f v w hdegree hrestrict hminor
  let z : IntVector n := fun i ↦ a * v i + b * w i
  obtain ⟨h, r, hprimitive, hr, hscale, hbound⟩ :=
    exists_bounded_primitiveDirection_of_ne_zero z hnonzero
  have haAbs : a.natAbs ≤ D + 1 := by
    exact_mod_cast (show (a.natAbs : ℤ) ≤ (D + 1 : ℕ) by
      rw [Int.natCast_natAbs, abs_of_pos ha.1]
      exact ha.2)
  have hbAbs : b.natAbs ≤ D + 1 := by
    exact_mod_cast (show (b.natAbs : ℤ) ≤ (D + 1 : ℕ) by
      rw [Int.natCast_natAbs, abs_of_nonneg hb.1]
      exact hb.2)
  have hzbound : ∀ i, (z i).natAbs ≤ 2 * (D + 1) * U := by
    intro i
    calc
      (z i).natAbs ≤ (a * v i).natAbs + (b * w i).natAbs :=
        Int.natAbs_add_le _ _
      _ = a.natAbs * (v i).natAbs + b.natAbs * (w i).natAbs := by
        simp only [Int.natAbs_mul]
      _ ≤ (D + 1) * U + (D + 1) * U :=
        Nat.add_le_add (Nat.mul_le_mul haAbs (hv i))
          (Nat.mul_le_mul hbAbs (hw i))
      _ = 2 * (D + 1) * U := by ring
  refine ⟨h, a, b, r, hprimitive, ?_, hr, hscale, ?_⟩
  · apply Finset.sup_le
    intro i _
    exact (hbound i).trans (hzbound i)
  · let fQ := MvPolynomial.map (Int.castRingHom ℚ) f
    have hfQ : fQ.IsHomogeneous d := hfhom.map _
    have hcast (s : IntVector n) :
        eval (fun i ↦ (s i : ℚ)) fQ = ((eval s f : ℤ) : ℚ) :=
      (MvPolynomial.map_eval (Int.castRingHom ℚ) s f).symm
    have hnonzeroQ : eval (fun i ↦ (z i : ℚ)) fQ ≠ 0 := by
      rw [hcast]
      exact_mod_cast heval
    have hscaled : eval (fun i ↦ (h i : ℚ)) fQ =
        r ^ d * eval (fun i ↦ (z i : ℚ)) fQ := by
      simpa only [← hscale] using
        eval_smul_of_isHomogeneous fQ (fun i ↦ (z i : ℚ)) r d hfQ
    have hresult := hscaled ▸ mul_ne_zero (pow_ne_zero d hr) hnonzeroQ
    intro hhzero
    apply hresult
    rw [hcast, hhzero, Int.cast_zero]

end

end TranslatedDepthSeven
