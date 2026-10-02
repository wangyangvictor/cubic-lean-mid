import TranslatedDepthSeven.IntegralPacketSpanBasis

/-!
# Bounded equations from the points themselves

A finite set of integral vectors whose rational span has codimension at
least `c` lies on `c` independent integral linear equations of explicitly
bounded coefficient height. The equations are obtained from a basis chosen
among the points and a nonsingular minor; no height of the ambient variety
or of an irreducible component is involved.
-/

namespace TranslatedDepthSeven

noncomputable section

open Matrix

set_option maxHeartbeats 5000000

/-- A fixed number of independent rows of the Cramer equation matrix. -/
def selectedCramerSpanEquationMatrix {c r N : ℕ}
    (hc : c ≤ N - r) (B : Matrix (Fin r) (Fin N) ℤ)
    (J : Fin r ↪ Fin N) : Matrix (Fin c) (Fin N) ℤ :=
  (cramerSpanEquationFinMatrix B J).submatrix (Fin.castLE hc) id

theorem selectedCramerSpanEquationMatrix_rank {c r N : ℕ}
    (hc : c ≤ N - r) (B : Matrix (Fin r) (Fin N) ℤ)
    (J : Fin r ↪ Fin N)
    (hdet : (selectedIntegralPivot B J).det ≠ 0) :
    ((selectedCramerSpanEquationMatrix hc B J).map
      ((↑) : ℤ → ℚ)).rank = c := by
  have hfull : LinearIndependent ℚ
      ((cramerSpanEquationFinMatrix B J).map ((↑) : ℤ → ℚ)).row := by
    simpa [cramerSpanEquationFinMatrix] using
      (cramerSpanEquationMatrix_rows_linearIndependent B J hdet).comp
        (matrixNonpivotEquivFin J).symm
        (matrixNonpivotEquivFin J).symm.injective
  have hselected : LinearIndependent ℚ
      ((selectedCramerSpanEquationMatrix hc B J).map
        ((↑) : ℤ → ℚ)).row := by
    simpa [selectedCramerSpanEquationMatrix] using
      hfull.comp (Fin.castLE hc) (Fin.castLE_injective hc)
  simpa using hselected.rank_matrix

theorem selectedCramerSpanEquationMatrix_mulVec_row_eq_zero {c r N : ℕ}
    (hc : c ≤ N - r) (B : Matrix (Fin r) (Fin N) ℤ)
    (J : Fin r ↪ Fin N) (i : Fin r) :
    selectedCramerSpanEquationMatrix hc B J *ᵥ B.row i = 0 := by
  funext k
  have hk := congrFun (cramerSpanEquationMatrix_mulVec_row_eq_zero B J i)
    ((matrixNonpivotEquivFin J).symm (Fin.castLE hc k))
  simpa [selectedCramerSpanEquationMatrix, cramerSpanEquationFinMatrix,
    Matrix.mulVec, dotProduct] using hk

/-- The same equations vanish on the whole rational row span. -/
theorem selectedCramerSpanEquationMatrix_mulVec_eq_zero_of_mem_span
    {c r N : ℕ} (hc : c ≤ N - r)
    (B : Matrix (Fin r) (Fin N) ℤ) (J : Fin r ↪ Fin N)
    (v : Fin N → ℚ)
    (hv : v ∈ Submodule.span ℚ
      (Set.range ((B.map ((↑) : ℤ → ℚ)).row))) :
    ((selectedCramerSpanEquationMatrix hc B J).map
      ((↑) : ℤ → ℚ)) *ᵥ v = 0 := by
  let A := (selectedCramerSpanEquationMatrix hc B J).map ((↑) : ℤ → ℚ)
  have hker : Submodule.span ℚ
      (Set.range ((B.map ((↑) : ℤ → ℚ)).row)) ≤
      LinearMap.ker A.mulVecLin := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change A *ᵥ (fun j ↦ (B i j : ℚ)) = 0
    funext k
    have hz := congrFun
      (selectedCramerSpanEquationMatrix_mulVec_row_eq_zero hc B J i) k
    have hmap := (Int.castRingHom ℚ).map_mulVec
      (selectedCramerSpanEquationMatrix hc B J) (B.row i) k
    simpa only [hz, map_zero, A, Matrix.row_apply] using hmap.symm
  exact hker hv

/-- A height bound depending only on the point bound and the dimension of
their span, uniformly in the finite point set. Empty sets are allowed. -/
theorem exists_bounded_integral_equations_of_pointSpan_finrank_le
    {c N M : ℕ} (hNc : c ≤ N) (Z : Finset (IntVector N))
    (hdim : Module.finrank ℚ
      (Submodule.span ℚ (Set.range fun z : {z // z ∈ Z} ↦
        fun j ↦ (z.1 j : ℚ))) ≤ N - c)
    (hcoord : ∀ z ∈ Z, ∀ j, (z j).natAbs ≤ M) :
    ∃ A : Matrix (Fin c) (Fin N) ℤ,
      (A.map ((↑) : ℤ → ℚ)).rank = c ∧
      (∀ z ∈ Z, A *ᵥ z = 0) ∧
      (∀ i j, (A i j).natAbs ≤
        (N - c).factorial * (max 1 M) ^ (N - c)) ∧
      rationalProjectiveLinearHeight (A.map ((↑) : ℤ → ℚ)) ≤
        c.factorial *
          ((N - c).factorial * (max 1 M) ^ (N - c)) ^ c := by
  classical
  have hdim' : Module.finrank ℚ
      (Submodule.span ℚ (Set.range fun z : {z // z ∈ Z} ↦
        rationalIntegralDifference 0 z.1)) ≤ N - c := by
    have heq : (fun z : {z // z ∈ Z} ↦
        rationalIntegralDifference (0 : IntVector N) z.1) =
        (fun z : {z // z ∈ Z} ↦ fun j ↦ (z.1 j : ℚ)) := by
      funext z j
      simp [rationalIntegralDifference]
    rw [heq]
    exact hdim
  obtain ⟨r, point, J, hr, hdet, hspan, hB⟩ :=
    exists_integralDifferenceBasis_with_pivot Z 0 hdim'
      (by simpa only [Pi.zero_apply, sub_zero] using hcoord)
  let B := integralDifferenceMatrix 0 (fun i ↦ (point i).1)
  have hc : c ≤ N - r := by omega
  let A := selectedCramerSpanEquationMatrix hc B J
  have hentry : ∀ i j, (A i j).natAbs ≤
      (N - c).factorial * (max 1 M) ^ (N - c) := by
    intro i j
    have hraw := cramerSpanEquationMatrix_entry_natAbs_le B J hB
      ((matrixNonpivotEquivFin J).symm (Fin.castLE hc i)) j
    change (A i j).natAbs ≤ r.factorial * M ^ r at hraw
    refine hraw.trans (Nat.mul_le_mul (Nat.factorial_le hr) ?_)
    exact (Nat.pow_le_pow_left (Nat.le_max_right 1 M) r).trans
      (Nat.pow_le_pow_right (Nat.le_max_left 1 M) hr)
  refine ⟨A, selectedCramerSpanEquationMatrix_rank hc B J hdet, ?_, hentry, ?_⟩
  · intro z hz
    have hmem : (fun j ↦ (z j : ℚ)) ∈
        Submodule.span ℚ (Set.range (B.map ((↑) : ℤ → ℚ)).row) := by
      rw [hspan]
      have hmem := Submodule.subset_span (R := ℚ)
        (show rationalIntegralDifference 0 z ∈
          Set.range (fun z : {z // z ∈ Z} ↦
            rationalIntegralDifference 0 z.1) from ⟨⟨z, hz⟩, rfl⟩)
      have heq : rationalIntegralDifference (0 : IntVector N) z =
          (fun j ↦ (z j : ℚ)) := by
        funext j
        simp [rationalIntegralDifference]
      rw [heq] at hmem
      exact hmem
    have hzero := selectedCramerSpanEquationMatrix_mulVec_eq_zero_of_mem_span
      hc B J (fun j ↦ (z j : ℚ)) hmem
    funext i
    have hi := congrFun hzero i
    have hmap := (Int.castRingHom ℚ).map_mulVec A z i
    have hzcast : ((A *ᵥ z) i : ℚ) = 0 := by
      exact hmap.trans hi
    exact_mod_cast hzcast
  · exact rationalProjectiveLinearHeight_map_intCast_le A hentry

end

end TranslatedDepthSeven
