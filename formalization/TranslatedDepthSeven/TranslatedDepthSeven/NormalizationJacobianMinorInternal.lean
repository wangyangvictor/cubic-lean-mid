import TranslatedDepthSeven.NormalizationConormalEquationsInternal
import TranslatedDepthSeven.EquationFamilyTangentBaseChange

/-!
# A degree-bounded ordinary Jacobian minor

Diagonal differentiation in constant directions implies that the ordinary
coordinate Jacobian has independent rows at the generic point.  Selecting
a coordinate minor and using row homogeneity gives the explicit degree
bound.  This is not an assertion about generators of the defining ideal.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000

/-- A diagonal directional pairing with nonzero entries in a prime
quotient supplies a literal ordinary-coordinate minor outside that prime. -/
theorem exists_jacobian_minor_notMem_of_diagonal_directions
    {K : Type*} [Field K] {n c : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (hIprime : I.IsPrime)
    (F g : Fin c → MvPolynomial (Fin n) K)
    (v : Fin c → Fin n → K)
    (hg : ∀ j, g j ∉ I)
    (hpair : ∀ i j, constantPolynomialDirectionalDerivative (v i) (F j) =
      if i = j then g j else 0) :
    ∃ cols : Fin c → Fin n, Function.Injective cols ∧
      (Matrix.of (fun i j ↦ pderiv (cols j) (F i))).det ∉ I := by
  classical
  letI : I.IsPrime := hIprime
  let A := MvPolynomial (Fin n) K ⧸ I
  let L := FractionRing A
  let φ : MvPolynomial (Fin n) K →+* L :=
    (algebraMap A L).comp (Ideal.Quotient.mk I)
  have hφg (j : Fin c) : φ (g j) ≠ 0 := by
    intro hzero
    have h : Ideal.Quotient.mk I (g j) = 0 := by
      apply IsFractionRing.injective A L
      simpa only [map_zero] using hzero
    exact hg j ((Ideal.Quotient.eq_zero_iff_mem).1 h)
  let J : Matrix (Fin c) (Fin n) L := fun j k ↦ φ (pderiv k (F j))
  let V : Matrix (Fin n) (Fin c) L := fun k i ↦ φ (C (v i k))
  have hJV : J * V = Matrix.diagonal (fun j ↦ φ (g j)) := by
    ext j i
    have h := congrArg φ (hpair i j)
    rw [constantPolynomialDirectionalDerivative_eq_sum] at h
    simp only [map_sum, map_mul, apply_ite φ, map_zero] at h
    change (∑ k, φ (pderiv k (F j)) * φ (C (v i k))) = _
    simpa only [Matrix.diagonal_apply, eq_comm, mul_comm] using h
  have hrows : LinearIndependent L J.row := by
    apply LinearIndependent.of_comp V.vecMulLinear
    have hcomp : V.vecMulLinear ∘ J.row = (J * V).row := by
      funext i j
      rfl
    rw [hcomp, hJV]
    apply Matrix.linearIndependent_rows_of_det_ne_zero
    change (Matrix.diagonal (fun j ↦ φ (g j))).det ≠ 0
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun j _ ↦ hφg j)
  obtain ⟨cols, hcols, hdet⟩ :=
    TangentBaseChange.exists_selectedMinor_ne_zero_of_linearIndependent_rows J hrows
  refine ⟨cols, hcols, ?_⟩
  intro hmem
  apply hdet
  have hz : φ ((Matrix.of (fun i j ↦ pderiv (cols j) (F i))).det) = 0 := by
    change algebraMap A L
      (Ideal.Quotient.mk I ((Matrix.of (fun i j ↦ pderiv (cols j) (F i))).det)) = 0
    rw [(Ideal.Quotient.eq_zero_iff_mem).2 hmem, map_zero]
  rw [φ.map_det] at hz
  exact hz

/-- The normalizing equations yield an ordinary coordinate minor of
degree at most `codimension * (degree - 1)`, outside the source prime.
All equations used have degree at most the actual projective degree. -/
theorem exists_bounded_normalization_jacobian_minor
    {K : Type*} [Field K] [CharZero K] {N r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hIprime : I.IsPrime)
    (hIhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K))
    (hdegree : HasProjectiveDimensionDegree I r d)
    (D : HomogeneousLinearNormalizationData I) :
    ∃ (F : Fin (N + 1 - D.parameterCount) → MvPolynomial (Fin (N + 1)) K)
      (degrees : Fin (N + 1 - D.parameterCount) → ℕ)
      (cols : Fin (N + 1 - D.parameterCount) → Fin (N + 1)),
      Function.Injective cols ∧
      (∀ j, degrees j ≤ d) ∧
      (∀ j, (F j).IsHomogeneous (degrees j)) ∧
      (∀ j, F j ∈ I) ∧
      (Matrix.of (fun i j ↦ pderiv (cols j) (F i))).det ∉ I ∧
      ((Matrix.of (fun i j ↦ pderiv (cols j) (F i))).det).totalDegree ≤
        (N + 1 - D.parameterCount) * (d - 1) := by
  classical
  obtain ⟨F, g, v, degrees, hdegrees, hFhom, hFmem, hg, hpair⟩ :=
    exists_bounded_normalization_equations_diagonal_derivatives
      I hIprime hIhom hdegree D
  obtain ⟨cols, hcols, hminor⟩ :=
    exists_jacobian_minor_notMem_of_diagonal_directions I hIprime F g v hg hpair
  refine ⟨F, degrees, cols, hcols, hdegrees, hFhom, hFmem, hminor, ?_⟩
  have hhom : (Matrix.of (fun i j ↦ pderiv (cols j) (F i))).det.IsHomogeneous
      (∑ i, (degrees i - 1)) :=
    matrix_det_isHomogeneous_of_row_isHomogeneous _ _
      (fun i j ↦ (hFhom i).pderiv)
  apply hhom.totalDegree_le.trans
  calc
    (∑ i, (degrees i - 1)) ≤ ∑ _i : Fin (N + 1 - D.parameterCount), (d - 1) :=
      Finset.sum_le_sum (fun i _ ↦ Nat.sub_le_sub_right (hdegrees i) 1)
    _ = _ := by simp

end

end TranslatedDepthSeven
