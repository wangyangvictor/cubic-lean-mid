import CubicTenVariables.AdmissibleResidueCount
import CubicTenVariables.SmithKernelFormula

/-! Actual unimodular diagonal data supply both kernel factors in the
canonical low-digit count. The same integral diagonal is chosen before the
two moduli and every frequency/unit. No diagonalization data are assumed
by the final existence theorem. -/

noncomputable section
namespace CubicTenVariables.AdmissibleSmithCount
open MatrixSmithKernel MatrixSmithExistence SmithKernelFormula AdmissibleResidueCount
open scoped BigOperators Matrix

/-- The same integral row/column changes diagonalize every scalar multiple. -/
theorem diagonalization_smul {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ) (d : Fin n → ℤ)
    (hD : (U : Matrix (Fin n) (Fin n) ℤ) * B * V = Matrix.diagonal d) (L : ℤ) :
    (U : Matrix (Fin n) (Fin n) ℤ) * (L • B) * V =
      Matrix.diagonal (fun i => L * d i) := by
  rw [Matrix.mul_smul, Matrix.smul_mul, hD, ← Matrix.diagonal_smul]
  rfl

/-- Both actual modular kernels use the same chosen integer diagonal. -/
theorem card_scaled_kernel_eq_prod_gcd {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ) (d : Fin n → ℤ)
    (hD : (U : Matrix (Fin n) (Fin n) ℤ) * B * V = Matrix.diagonal d)
    (M L : ℕ) [NeZero M] :
    Nat.card {x : Fin n → ZMod M //
      ((L : ZMod M) • B.map (Int.castRingHom (ZMod M))).mulVec x = 0} =
      ∏ i, Nat.gcd (((L : ℤ) * d i).natAbs) M := by
  have hmap : (((L : ℤ) • B).map (Int.castRingHom (ZMod M))) =
      (L : ZMod M) • B.map (Int.castRingHom (ZMod M)) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
      map_natCast]
  rw [← hmap]
  exact card_kernel_eq_prod_gcd_of_int_equivalence M ((L : ℤ) • B)
    (fun i => (L : ℤ) * d i) U V (diagonalization_smul B U V d hD L)

/-- The exact gcd ratio for a displayed actual integral diagonalization. -/
theorem admissible_fin_gcd_ratio_of_diagonalization {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℤ)
    (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ) (d : Fin n → ℤ)
    (hD : (U : Matrix (Fin n) (Fin n) ℤ) * B * V = Matrix.diagonal d)
    (M L : ℕ) [NeZero M] [NeZero L]
    (ell : Fin n → ZMod M) (alpha : (ZMod M)ˣ) :
    let H := B.map (Int.castRingHom (ZMod M))
    let K := Nat.card {v : Fin n → Fin L // ∃ x : Fin n → ZMod M,
      ((L : ZMod M) • H).mulVec x =
        ell + (alpha : ZMod M) • H.mulVec (fun i => ((v i).val : ZMod M))}
    K = 0 ∨ K * (∏ i, Nat.gcd (((L : ℤ) * d i).natAbs) M) =
      L^n * ∏ i, Nat.gcd (d i).natAbs M := by
  have h := card_admissible_fin_eq_zero_or_ratio M L n
    (B.map (Int.castRingHom (ZMod M))) ell alpha
  rw [card_scaled_kernel_eq_prod_gcd B U V d hD M L,
    card_kernel_eq_prod_gcd_of_int_equivalence M B d U V hD] at h
  exact h

/-- A single actual diagonal supplies the exact zero-or-gcd ratio for all
positive pairs of moduli and every actual unit/frequency. -/
theorem exists_admissible_fin_gcd_ratio {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    ∃ d : Fin n → ℤ, ∀ (M L : ℕ) [NeZero M] [NeZero L],
      ∀ (ell : Fin n → ZMod M) (alpha : (ZMod M)ˣ),
      let H := B.map (Int.castRingHom (ZMod M))
      let K := Nat.card {v : Fin n → Fin L // ∃ x : Fin n → ZMod M,
        ((L : ZMod M) • H).mulVec x =
          ell + (alpha : ZMod M) • H.mulVec (fun i => ((v i).val : ZMod M))}
      K = 0 ∨ K * (∏ i, Nat.gcd (((L : ℤ) * d i).natAbs) M) =
        L^n * ∏ i, Nat.gcd (d i).natAbs M := by
  obtain ⟨U,V,d,hD⟩ := exists_integer_diagonalization B
  refine ⟨d, ?_⟩
  intro M L hM hL ell alpha
  letI := hM
  letI := hL
  dsimp only
  have h := card_admissible_fin_eq_zero_or_ratio M L n
    (B.map (Int.castRingHom (ZMod M))) ell alpha
  rw [card_scaled_kernel_eq_prod_gcd B U V d hD M L,
    card_kernel_eq_prod_gcd_of_int_equivalence M B d U V hD] at h
  exact h

end CubicTenVariables.AdmissibleSmithCount
