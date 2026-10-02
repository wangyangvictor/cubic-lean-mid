import TranslatedDepthSeven.IntegralLocalEquationMultiplicitySpecialization
import TranslatedDepthSeven.StrictRootTheorem

/-!
# Integralizing a rational local complete-intersection chart

This file clears all rational coefficients in a local equation chart for a
fixed integral component.  The clearing is literal.  Each rational equation
is first multiplied by its displayed common coefficient denominator, and a
second nonzero integer clears its membership in the integral component ideal.
The selected Jacobian determinant is thereby multiplied by the product of
these nonzero row scalars, so its nonvanishing at an integral marked point is
preserved.

The rational principal-open equality is then cleared against a finite
integral generating family.  The output is precisely the integral
`u * J \subseteq (g_1,\ldots,g_c)` certificate used by
`hasHilbertSamuelMultiplicityAt_one_of_integral_localEquations`.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

/-- Multiplying every displayed equation by a scalar multiplies its selected
Jacobian determinant by the product of those scalars. -/
theorem selectedJacobianDeterminant_C_mul
    {K : Type*} [CommRing K] {N c : ℕ}
    (equations : Fin c → MvPolynomial (Fin N) K)
    (selectedVar : Fin c → Fin N) (a : Fin c → K) :
    selectedJacobianDeterminant
        (fun j ↦ MvPolynomial.C (a j) * equations j) selectedVar =
      MvPolynomial.C (∏ j, a j) *
        selectedJacobianDeterminant equations selectedVar := by
  classical
  let M : Matrix (Fin c) (Fin c) (MvPolynomial (Fin N) K) :=
    Matrix.of fun i j ↦ MvPolynomial.pderiv (selectedVar i) (equations j)
  have hmatrix : Matrix.of (fun i j ↦
      MvPolynomial.pderiv (selectedVar i)
        (MvPolynomial.C (a j) * equations j)) =
      M * Matrix.diagonal (fun j ↦ MvPolynomial.C (a j)) := by
    apply Matrix.ext
    intro i j
    simp [M, mul_comm]
  rw [selectedJacobianDeterminant, selectedJacobianDeterminant, hmatrix,
    Matrix.det_mul, Matrix.det_diagonal, map_prod]
  simp only [M]
  ring

/-- Rescaling each member of a finite equation family by a nonzero scalar
does not change the ideal which the family generates over a field. -/
theorem span_range_C_mul_eq_of_forall_ne_zero
    {K : Type*} [Field K] {N c : ℕ}
    (equations : Fin c → MvPolynomial (Fin N) K)
    (a : Fin c → K) (ha : ∀ i, a i ≠ 0) :
    Ideal.span
        (Set.range fun i ↦ MvPolynomial.C (a i) * equations i) =
      Ideal.span (Set.range equations) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (Ideal.span (Set.range equations)).mul_mem_left
      (MvPolynomial.C (a i)) (Ideal.subset_span ⟨i, rfl⟩)
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hscaled : MvPolynomial.C (a i) * equations i ∈
        Ideal.span
          (Set.range fun i ↦ MvPolynomial.C (a i) * equations i) :=
      Ideal.subset_span ⟨i, rfl⟩
    have hinv :=
      (Ideal.span
        (Set.range fun i ↦ MvPolynomial.C (a i) * equations i)).mul_mem_left
          (MvPolynomial.C (a i)⁻¹) hscaled
    convert hinv using 1
    rw [← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ (ha i)]
    simp

noncomputable local instance integralPolynomialToRationalAlgebra'
    {N : ℕ} :
    Algebra (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) ℚ) :=
  (MvPolynomial.map (Int.castRingHom ℚ)).toAlgebra

/-- Membership after rational coefficient extension is witnessed by one
nonzero integer multiple before extension. -/
theorem exists_nonzero_int_C_mul_mem_of_map_intCast_mem
    {N : ℕ} (J : Ideal (MvPolynomial (Fin N) ℤ))
    (f : MvPolynomial (Fin N) ℤ)
    (hf : MvPolynomial.map (Int.castRingHom ℚ) f ∈
      Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) J) :
    ∃ d : ℤ, d ≠ 0 ∧ MvPolynomial.C d * f ∈ J := by
  let R := MvPolynomial (Fin N) ℤ
  let S := MvPolynomial (Fin N) ℚ
  let M : Submonoid R :=
    (nonZeroDivisors ℤ).map (MvPolynomial.C : ℤ →+* R)
  letI : IsLocalization M S :=
    MvPolynomial.isLocalization (nonZeroDivisors ℤ) ℚ
  have hf' : algebraMap R S f ∈ Ideal.map (algebraMap R S) J := by
    exact hf
  obtain ⟨m, hmM, hmf⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff M S J f).mp hf'
  obtain ⟨d, hd, hdm⟩ := Submonoid.mem_map.mp hmM
  refine ⟨d, mem_nonZeroDivisors_iff_ne_zero.mp hd, ?_⟩
  rw [← hdm] at hmf
  exact hmf

end

end TranslatedDepthSeven
