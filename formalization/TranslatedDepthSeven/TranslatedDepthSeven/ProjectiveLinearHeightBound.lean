import TranslatedDepthSeven.RationalProjectiveLinearSpace
import TranslatedDepthSeven.TangentPacketSpan

/-!
# An elementary Plücker-height bound for integral equation matrices

The packet construction eventually presents a rational projective linear
space by a matrix of integral linear equations.  This file records the
literal fixed-dimensional height estimate needed there.  If every entry of
a `c` by `N` integral matrix has absolute value at most `M`, then the
primitive Plücker height of the same matrix over `ℚ` is at most
`c! M^c`.

There is no elimination or height-theory input: the Plücker coordinates are
maximal minors, their canonical denominator is one, and the estimate is the
elementary determinant bound.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- The row of integral maximal minors of an integral equation matrix. -/
def integralMaximalMinorRow {c N : ℕ}
    (A : Matrix (Fin c) (Fin N) ℤ) :
    Matrix (Fin 1) (RationalPluckerIndex c N) ℤ :=
  fun _ J ↦ (A.submatrix id J).det

/-- The rational Plücker row of an integral matrix is obtained by casting
its literal integral maximal-minor row. -/
theorem rationalPluckerRow_map_intCast {c N : ℕ}
    (A : Matrix (Fin c) (Fin N) ℤ) :
    rationalPluckerRow (A.map ((↑) : ℤ → ℚ)) =
      (integralMaximalMinorRow A).map ((↑) : ℤ → ℚ) := by
  ext i J
  simp only [rationalPluckerRow, rationalPluckerCoordinate,
    integralMaximalMinorRow, Matrix.map_apply]
  exact ((Int.castRingHom ℚ).map_det (A.submatrix id J)).symm

/-- No denominator is introduced when an integral equation matrix is
regarded as a rational matrix. -/
@[simp]
theorem rationalPluckerDenominator_map_intCast {c N : ℕ}
    (A : Matrix (Fin c) (Fin N) ℤ) :
    rationalPluckerDenominator (A.map ((↑) : ℤ → ℚ)) = 1 := by
  rw [rationalPluckerDenominator, rationalPluckerRow_map_intCast,
    Matrix.den_map_intCast]

/-- The canonical integral Plücker coordinate is the corresponding
integral maximal minor. -/
@[simp]
theorem integralPluckerCoordinate_map_intCast {c N : ℕ}
    (A : Matrix (Fin c) (Fin N) ℤ) (J : RationalPluckerIndex c N) :
    integralPluckerCoordinate (A.map ((↑) : ℤ → ℚ)) J =
      (A.submatrix id J).det := by
  rw [integralPluckerCoordinate, rationalPluckerRow_map_intCast,
    Matrix.num_map_intCast]
  rfl

/-- Primitive normalization can only decrease the absolute value of an
integral maximal minor. -/
theorem primitiveIntegralPluckerCoordinate_map_intCast_natAbs_le
    {c N : ℕ} (A : Matrix (Fin c) (Fin N) ℤ)
    (J : RationalPluckerIndex c N) :
    (primitiveIntegralPluckerCoordinate
      (A.map ((↑) : ℤ → ℚ)) J).natAbs ≤
        (A.submatrix id J).det.natAbs := by
  rw [primitiveIntegralPluckerCoordinate_natAbs,
    integralPluckerCoordinate_map_intCast]
  exact Nat.div_le_self _ _

/-- Every maximal minor obeys the same factorial entrywise determinant
bound. -/
theorem integralMaximalMinor_natAbs_le {c N M : ℕ}
    (A : Matrix (Fin c) (Fin N) ℤ)
    (hA : ∀ i j, (A i j).natAbs ≤ M)
    (J : RationalPluckerIndex c N) :
    (A.submatrix id J).det.natAbs ≤ c.factorial * M ^ c := by
  apply TangentPacketSpan.det_natAbs_le_factorial_mul_pow
  intro i j
  exact hA i (J j)

/-- **Integral equation-matrix height bound.**  Casting a bounded integral
`c` by `N` matrix to `ℚ` gives primitive projective Plücker height at most
`c! M^c`. -/
theorem rationalProjectiveLinearHeight_map_intCast_le
    {c N M : ℕ} (A : Matrix (Fin c) (Fin N) ℤ)
    (hA : ∀ i j, (A i j).natAbs ≤ M) :
    rationalProjectiveLinearHeight (A.map ((↑) : ℤ → ℚ)) ≤
      c.factorial * M ^ c := by
  unfold rationalProjectiveLinearHeight
  apply Finset.sup_le
  intro J _hJ
  exact (primitiveIntegralPluckerCoordinate_map_intCast_natAbs_le A J).trans
    (integralMaximalMinor_natAbs_le A hA J)

end

end TranslatedDepthSeven
