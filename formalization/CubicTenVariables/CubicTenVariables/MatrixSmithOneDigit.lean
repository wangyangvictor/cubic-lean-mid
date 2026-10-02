import CubicTenVariables.MatrixSmithProfileInvariant
import CubicTenVariables.DiagonalSmithOneDigitKernel
import CubicTenVariables.MatrixSmithResidualRank

/-!
# A fixed translated rank bound for one Smith-profile digit

Integral left/right diagonalization, exact modular kernel fibres and a
finite-field block-rank inequality give the one-digit transition. The
translation is chosen from the old matrix before the perturbation matrix.
No symmetry or odd-characteristic hypothesis is needed.
-/

noncomputable section
namespace CubicTenVariables.MatrixSmithOneDigit
open Matrix MatrixSmithProfileInvariant MatrixSmithResidualRank PrimePowerKernelProfile
open scoped BigOperators

variable {n : ℕ}

theorem not_pow_dvd_iff (p : ℕ) (hp : p.Prime) (m : ℕ) (hm : 1 ≤ m) (a : ℤ) :
    ¬ (p : ℤ)^m ∣ a ↔ a ≠ 0 ∧ a.natAbs.factorization p ≤ m-1 := by
  constructor
  · intro ha
    obtain ⟨ha0, hv⟩ := PrimePowerScalarFibers.valuation_lt p m hp a ha
    exact ⟨ha0, by omega⟩
  · rintro ⟨ha0, hv⟩ hdiv
    have hn : p^m ∣ a.natAbs := Int.natCast_dvd.mp (by
      simpa only [Nat.cast_pow] using hdiv)
    have hm' := (hp.pow_dvd_iff_le_factorization (Int.natAbs_ne_zero.mpr ha0)).mp hn
    omega

/-- The old-pivot count is exactly the preceding cumulative profile entry. -/
theorem card_oldIndices_eq_diagonalEntry (p : ℕ) (hp : p.Prime)
    (m : ℕ) (hm : 1 ≤ m) (d : Fin n → ℤ) :
    Fintype.card (oldIndices p m d) = diagonalEntry d p (m-1) := by
  classical
  simp only [oldIndices, Fintype.card_subtype, diagonalEntry]
  congr 1
  apply Finset.filter_congr
  intro i _
  exact not_pow_dvd_iff p hp m hm (d i)

/-- A perturbation by the old modulus leaves the old residue matrix fixed. -/
theorem perturbed_map_eq (A B : Matrix (Fin n) (Fin n) ℤ) (p m : ℕ) :
    (A + (p : ℤ)^m • B).map (Int.castRingHom (ZMod (p^m))) =
      A.map (Int.castRingHom (ZMod (p^m))) := by
  ext i j
  change ((A i j + (p : ℤ)^m * B i j : ℤ) : ZMod (p^m)) = (A i j : ZMod (p^m))
  rw [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast, ← Nat.cast_pow,
    ZMod.natCast_self, zero_mul, add_zero]

/-- Integral invertible row and column changes preserve every profile entry. -/
theorem entry_mul_units (A : Matrix (Fin n) (Fin n) ℤ)
    (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ) (p : ℕ) (hp : p.Prime) (i : ℕ) :
    entry ((U : Matrix (Fin n) (Fin n) ℤ) * A * (V : Matrix (Fin n) (Fin n) ℤ)) p i = entry A p i := by
  have hk (t : ℕ) :
      kernelCard ((U : Matrix (Fin n) (Fin n) ℤ) * A * (V : Matrix (Fin n) (Fin n) ℤ)) p t = kernelCard A p t :=
    MatrixSmithKernel.card_kernel_int_mul_units (p^t) A U V
  have he (t : ℕ) :
      kernelExponent ((U : Matrix (Fin n) (Fin n) ℤ) * A * (V : Matrix (Fin n) (Fin n) ℤ)) p t =
        kernelExponent A p t := by
    apply Nat.pow_right_injective hp.two_le
    exact (kernelCard_eq_pow _ p hp t).symm.trans ((hk t).trans (kernelCard_eq_pow _ p hp t))
  have h := kernelExponent_succ_add_entry ((U : Matrix (Fin n) (Fin n) ℤ) * A * (V : Matrix (Fin n) (Fin n) ℤ)) p i
  rw [he (i+1), he i] at h
  have hA := kernelExponent_succ_add_entry A p i
  omega

/-- The new cumulative entry is the old-pivot count plus the rank of the
literal affine residual block. This includes zero entries and p=2. -/
theorem entry_perturbed_diagonal (p : ℕ) (hp : p.Prime) (m : ℕ)
    (d : Fin n → ℤ) (E : Matrix (Fin n) (Fin n) ℤ) :
    entry (Matrix.diagonal d + (p : ℤ)^m • E) p m =
      Fintype.card (oldIndices p m d) + (residualMatrix p m d E).rank := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hcards : Fintype.card (tailIndices p m d) + Fintype.card (oldIndices p m d) = n := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using
      Fintype.card_congr (Equiv.sumCompl (fun i : Fin n => (p : ℤ)^m ∣ d i))
  have hr := Matrix.rank_le_card_width (residualMatrix p m d E)
  apply entry_eq_of_kernel_growth _ p hp m
    (Fintype.card (oldIndices p m d) + (residualMatrix p m d E).rank) (by omega)
  have hk : kernelCard (Matrix.diagonal d + (p : ℤ)^m • E) p m =
      kernelCard (Matrix.diagonal d) p m := by
    unfold kernelCard
    rw [perturbed_map_eq]
  rw [hk]
  have h := DiagonalSmithOneDigitKernel.card_kernel_eq_diagonal_mul p m d E
  change kernelCard (Matrix.diagonal d + (p : ℤ)^m • E) p (m+1) =
    kernelCard (Matrix.diagonal d) p m *
      p^(Fintype.card (tailIndices p m d) - (residualMatrix p m d E).rank) at h
  convert h using 1
  congr 1
  congr 1
  omega

/-- A single translation, fixed by the old matrix and old precision,
controls every possible next matrix digit, in every prime characteristic. -/
theorem exists_translated_rank_bound (A : Matrix (Fin n) (Fin n) ℤ)
    (p : ℕ) (hp : p.Prime) (m : ℕ) (hm : 1 ≤ m) :
    ∃ T : Matrix (Fin n) (Fin n) (ZMod p),
      ∀ B : Matrix (Fin n) (Fin n) ℤ,
        (T + B.map (Int.castRingHom (ZMod p))).rank ≤
          entry A p (m-1) + entry (A + (p : ℤ)^m • B) p m := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, V, d, hD⟩ := MatrixSmithExistence.exists_integer_diagonalization A
  refine ⟨translatedMatrix p m d U V, ?_⟩
  intro B
  let E := (U : Matrix (Fin n) (Fin n) ℤ) * B * (V : Matrix (Fin n) (Fin n) ℤ)
  have hnew : (U : Matrix (Fin n) (Fin n) ℤ) * (A + (p : ℤ)^m • B) * (V : Matrix (Fin n) (Fin n) ℤ) =
      Matrix.diagonal d + (p : ℤ)^m • E := by
    rw [mul_add, add_mul, hD, Matrix.mul_smul, Matrix.smul_mul]
  have hold : entry A p (m-1) = Fintype.card (oldIndices p m d) := by
    rw [entry_eq_of_diagonalization A d U V hD p hp (m-1)]
    exact (card_oldIndices_eq_diagonalEntry p hp m hm d).symm
  have hnext : entry (A + (p : ℤ)^m • B) p m =
      Fintype.card (oldIndices p m d) + (residualMatrix p m d E).rank := by
    rw [← entry_mul_units (A + (p : ℤ)^m • B) U V p hp m, hnew]
    exact entry_perturbed_diagonal p hp m d E
  have h := rank_translatedMatrix_add_le p m d U V B
  change (translatedMatrix p m d U V + B.map (Int.castRingHom (ZMod p))).rank ≤
    2 * Fintype.card (oldIndices p m d) + (residualMatrix p m d E).rank at h
  rw [hold, hnext]
  omega

end CubicTenVariables.MatrixSmithOneDigit
