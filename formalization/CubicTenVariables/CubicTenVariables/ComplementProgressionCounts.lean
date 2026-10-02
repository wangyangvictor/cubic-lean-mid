import CubicTenVariables.ComplementFrequencyPieces
import CubicTenVariables.ProgressionHeightRemoval

/-! The exact progression exponents 10,8,7,5,4 for the five literal
complement pieces. The extra first promotion open is counted through its
actual finite homogeneous component models of dimension at most eight.
The varying progression modulus is removed from the height loss by the
proved small-box/large-modulus argument. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace CubicTenVariables.ComplementProgressionCounts
open MvPolynomial HessianTheorem11 TranslatedDepthSeven
open MicrolocalPromotedPartition MicrolocalPartitionCounts ComplementFrequencyPieces
open ConeComponentProgressionCount StratifiedSieveData
attribute [local instance] MvPolynomial.gradedAlgebra

variable {t : ℕ} {F : MvPolynomial (Fin 10) ℤ}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
  {tables : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)}

/-- Index i is source level r=i+2. -/
def profile : Fin 5 → ℕ := ![10,8,7,5,4]

theorem profile_values : profile 0 = 10 ∧ profile 1 = 8 ∧ profile 2 = 7 ∧
    profile 3 = 5 ∧ profile 4 = 4 := by decide

/-- The incoming level-one open has a uniform T⁸ count from its actual
prime homogeneous component ideals. No extra dimension assumption is used. -/
theorem first_open_progression
    (tables : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)) :
    ProgressionHypothesis {v : Fin 10 → ℤ | (fun a => (v a : ℚ)) ∈ (tables 0).open} 8 := by
  let I := fun i => PolynomialExponentialFamily.baseIdeal ((tables 0).G i)
  have hdim : ∀ i, ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸ I i) ≤ (8 : WithBot ℕ∞) := by
    intro i
    simpa using (tables 0).dimension i
  obtain ⟨C,hC,hcount⟩ := exists_ordinary_bound I
    (fun i => ((tables 0).prime i).ne_top) (tables 0).homogeneous 8 hdim
  apply ProgressionHeightRemoval.of_uniform_bound (tables 0).open 8
  refine ⟨C,hC,hcount _ ?_⟩
  rintro x ⟨i,hi,_⟩
  exact ⟨i,hi⟩

private theorem prime_part_progression {N B : ℕ}
    (hP : MicrolocalRationalPartition.Conclusion F f N B tables) (j : Fin 6) :
    ProgressionHypothesis {v : Fin 10 → ℤ | (fun a => (v a : ℚ)) ∈
      part f (promotionFamily (fun a => (tables a).open)) j}
        (MicrolocalUniformPartitionCount.profile j : ℝ) := by
  apply ProgressionHeightRemoval.progressionHypothesis _ (MicrolocalUniformPartitionCount.profile j)
  intro ε hε
  obtain ⟨C,hC,hcount⟩ := hP.uniform_counts ε hε
  exact ⟨C,hC,hcount j⟩

/-- Each actual complement piece satisfies the full sieve progression
hypothesis. Its constant precedes every center, radius, positive modulus,
residue class and finite subset, with height (L+norm(center))^ε. -/
theorem progressionHypothesis {N B : ℕ}
    (hP : MicrolocalRationalPartition.Conclusion F f N B tables) (i : Fin 5) :
    ProgressionHypothesis {v : Fin 10 → ℤ | (fun a => (v a : ℚ)) ∈ piece F f tables i}
      (profile i : ℝ) := by
  fin_cases i
  · have hp := prime_part_progression hP 0
    simp only [MicrolocalUniformPartitionCount.profile,profile,Fin.isValue,
      Matrix.cons_val_zero,Nat.cast_ofNat] at hp ⊢
    apply ProgressionHeightRemoval.mono _ hp
    intro v hv
    change (fun a => (v a : ℚ)) ∈ piece F f tables 0 at hv
    rw [(piece_values tables).1] at hv
    exact hv.1
  · have hp : ProgressionHypothesis {v : Fin 10 → ℤ | (fun a => (v a : ℚ)) ∈
        part f (promotionFamily (fun a => (tables a).open)) 1} 8 := by
      simpa [MicrolocalUniformPartitionCount.profile] using prime_part_progression hP 1
    have hu := ProgressionHeightRemoval.union hp (first_open_progression tables)
    simp only [profile]
    apply ProgressionHeightRemoval.mono _ hu
    intro v hv
    change (fun a => (v a : ℚ)) ∈ piece F f tables 1 at hv
    rw [(piece_values tables).2.1] at hv
    exact hv.1
  · have hp := prime_part_progression hP 2
    norm_num only [MicrolocalUniformPartitionCount.profile,profile,Matrix.cons_val_succ,
      Matrix.cons_val_zero,Nat.cast_ofNat] at hp ⊢
    apply ProgressionHeightRemoval.mono _ hp
    intro v hv
    change (fun a => (v a : ℚ)) ∈ piece F f tables 2 at hv
    rw [(piece_values tables).2.2.1] at hv
    exact hv.1
  · have hp := prime_part_progression hP 3
    norm_num only [MicrolocalUniformPartitionCount.profile,profile,Matrix.cons_val_succ,
      Matrix.cons_val_zero,Nat.cast_ofNat] at hp ⊢
    apply ProgressionHeightRemoval.mono _ hp
    intro v hv
    change (fun a => (v a : ℚ)) ∈ piece F f tables 3 at hv
    rw [(piece_values tables).2.2.2.1] at hv
    exact hv.1
  · have hp := prime_part_progression hP 4
    norm_num only [MicrolocalUniformPartitionCount.profile,profile,Matrix.cons_val_succ,
      Matrix.cons_val_zero,Nat.cast_ofNat] at hp ⊢
    apply ProgressionHeightRemoval.mono _ hp
    intro v hv
    change (fun a => (v a : ℚ)) ∈ piece F f tables 4 at hv
    rw [(piece_values tables).2.2.2.2] at hv
    exact hv.1

end CubicTenVariables.ComplementProgressionCounts
