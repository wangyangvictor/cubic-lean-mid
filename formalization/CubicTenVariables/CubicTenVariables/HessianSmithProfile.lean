import CubicTenVariables.PrimePowerKernelProfile
import CubicTenVariables.SmithProfileNumerics

/-! Actual cumulative diagonal valuations give one of the finite monotone
ten-variable profiles used by the already proved numerical optimization.
The profile entries and penalties are identified exactly, not just bounded.
-/

noncomputable section
namespace CubicTenVariables.HessianSmithProfile
open SmithProfileMultiplicity SmithProfileNumerics PrimePowerKernelProfile
open scoped BigOperators

/-- The literal cumulative counts, as a finite monotone ten-variable profile. -/
def ofValuations (a : ℕ) (j : Fin 10 → ℕ) : Profile a :=
  ⟨fun i => ⟨profile j i, lt_of_le_of_lt (profile_le j i) (by norm_num)⟩,
    fun _ _ h => profile_mono j h⟩

theorem entry_ofValuations (a : ℕ) (j : Fin 10 → ℕ) (i : ℕ) (hi : i < a) :
    entry (ofValuations a j) i = profile j i := by
  simp only [entry, dif_pos hi, ofValuations]

/-- The optimization penalty equals the literal sum of rank multiplicities. -/
theorem penalty_ofValuations (a t : ℕ) (j : Fin 10 → ℕ) :
    penalty (ofValuations a j) t =
      ∑ i ∈ Finset.range a, penaltyWeight a t i * (profile j i : ℚ) := by
  unfold penalty
  apply Finset.sum_congr rfl
  intro i hi
  rw [entry_ofValuations a j i (Finset.mem_range.mp hi)]

theorem penalty_ofValuations_real (a t : ℕ) (j : Fin 10 → ℕ) :
    (penalty (ofValuations a j) t : ℝ) =
      ∑ i ∈ Finset.range a, (penaltyWeight a t i : ℝ) * (profile j i : ℝ) := by
  rw [penalty_ofValuations]
  push_cast
  rfl

/-- The finite profile associated to one actual integral diagonal. -/
def ofDiagonal (p a : ℕ) (d : Fin 10 → ℤ) : Profile a :=
  ofValuations a (fun ν => truncatedValuation p a (d ν))

theorem entry_ofDiagonal (p a : ℕ) (d : Fin 10 → ℤ) (i : ℕ) (hi : i < a) :
    entry (ofDiagonal p a d) i =
      (Finset.univ.filter (fun ν => truncatedValuation p a (d ν) ≤ i)).card :=
  entry_ofValuations a _ i hi

theorem penalty_ofDiagonal_real (p a t : ℕ) (d : Fin 10 → ℤ) :
    (penalty (ofDiagonal p a d) t : ℝ) =
      ∑ i ∈ Finset.range a, (penaltyWeight a t i : ℝ) *
        (profile (fun ν => truncatedValuation p a (d ν)) i : ℝ) :=
  penalty_ofValuations_real a t _

end CubicTenVariables.HessianSmithProfile
