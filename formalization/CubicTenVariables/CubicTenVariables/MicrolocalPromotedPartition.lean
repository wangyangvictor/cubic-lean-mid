import CubicTenVariables.PromotedFrequencyPartition
import CubicTenVariables.MicrolocalRationalComponents
import CubicTenVariables.MicrolocalTerminalDepth
import CubicTenVariables.ConeComponentProgressionCount

/-! The source's promoted rational-frequency sets for the actual microlocal
depth filtration. The promotion subsets are explicit parameters here;
their construction and improved trace bounds are separate obligations.
Ordinary progression estimates are proved using actual component equations,
with constants uniform in the chosen compatible promotion subsets. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.MicrolocalPromotedPartition
open MvPolynomial HessianTheorem11
open ProjectiveMicrolocalData ProjectiveMicrolocalModels RationalConeClosure
open BihomogeneousIncidenceFamily TranslatedDepthSeven
attribute [local instance] MvPolynomial.gradedAlgebra

variable {t : ℕ} {F : MvPolynomial (Fin 10) ℤ}
  {f : Fin t → Polynomial 10 10}

/-- Level zero is all rational frequencies; positive levels are the actual
rational points of the geometric fiber-depth loci. -/
def filtration (f : Fin t → Polynomial 10 10) (j : ℕ) : Set (Fin 10 → ℚ) :=
  if j = 0 then Set.univ else rationalPoints (ProjectiveMicrolocalDepth.depth f j)

@[simp] theorem filtration_zero : filtration f 0 = Set.univ := by simp [filtration]

theorem filtration_antitone : Antitone (filtration f) := by
  intro i j hij
  by_cases hi : i = 0
  · subst i
    rw [filtration_zero]
    exact Set.subset_univ _
  · have hj : j ≠ 0 := by omega
    intro x hx
    simp only [filtration,if_neg hi,if_neg hj] at hx ⊢
    exact ProjectiveMicrolocalDepth.depth_antitone hij hx

/-- The supplied rational promotion sets must lie in their actual old
layers; the two boundary opens are empty. -/
def Compatible (f : Fin t → Polynomial 10 10) (U : ℕ → Set (Fin 10 → ℚ)) : Prop :=
  U 0 = ∅ ∧ U 5 = ∅ ∧
    ∀ j, j ≤ 5 → U j ⊆ PromotedFrequencyPartition.layer (filtration f) j

def part (f : Fin t → Polynomial 10 10) (U : ℕ → Set (Fin 10 → ℚ))
    (j : Fin 6) : Set (Fin 10 → ℚ) :=
  PromotedFrequencyPartition.part (filtration f) U j

/-- Literal formula for P0,...,P4, including the incoming promoted open. -/
theorem part_eq_source (U : ℕ → Set (Fin 10 → ℚ)) (j : Fin 6) (hj : j.val < 5) :
    part f U j = (((filtration f j.val \ filtration f (j.val+1)) \ U j.val) ∪
      U (j.val+1)) \ {0} := by
  simp only [part,PromotedFrequencyPartition.part,PromotedFrequencyPartition.promoted,
    PromotedFrequencyPartition.layer,if_pos hj]

theorem part_five (U : ℕ → Set (Fin 10 → ℚ)) :
    part f U ⟨5,by decide⟩ = rationalPoints (ProjectiveMicrolocalDepth.depth f 5) \ {0} := by
  simp [part,PromotedFrequencyPartition.part,PromotedFrequencyPartition.promoted,filtration]

theorem existsUnique_level (U : ℕ → Set (Fin 10 → ℚ)) (hU : Compatible f U)
    (x : Fin 10 → ℚ) (hx : x ≠ 0) : ∃! j : Fin 6, x ∈ part f U j :=
  PromotedFrequencyPartition.existsUnique_part (filtration f) U filtration_zero
    filtration_antitone hU.2.2 hU.1 hU.2.1 x hx

theorem union_parts (U : ℕ → Set (Fin 10 → ℚ)) (hU : Compatible f U) :
    (⋃ j : Fin 6, part f U j) = {x | x ≠ 0} :=
  PromotedFrequencyPartition.union_parts (filtration f) U filtration_zero hU.1

theorem union_with_origin (U : ℕ → Set (Fin 10 → ℚ)) (hU : Compatible f U) :
    (⋃ j : Fin 6, part f U j) ∪ {0} = Set.univ :=
  PromotedFrequencyPartition.union_parts_with_origin (filtration f) U filtration_zero hU.1

/-- Positive promoted levels stay in the actual corresponding rational
exceptional locus, even when their points came from the next level. -/
theorem part_subset_rationalDepth (h : Geometry F f)
    (U : ℕ → Set (Fin 10 → ℚ)) (hU : Compatible f U) (j : Fin 6) (hj : 0 < j.val) :
    part f U j ⊆ rationalPoints (rationalDepth f j.val) := by
  intro x hx
  have hz := PromotedFrequencyPartition.promoted_subset (filtration f) U
    filtration_antitone hU.2.2 (by omega : j.val ≤ 5) hx.1
  rw [rationalDepth_points h hj]
  simpa only [filtration,if_neg hj.ne'] using hz

/-- Actual finite component models give the ordinary progression bound.
The constant is fixed before all compatible promotion sets and box data. -/
theorem exists_ordinary_part_bound (h : Geometry F f)
    (hF : Anisotropic (map (Int.castRingHom ℚ) F)) (j : Fin 6) (hj : 0 < j.val)
    (r : ℕ) (hdim : affineDimension (rationalDepth f j.val) ≤ (r : Dimension)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (U : ℕ → Set (Fin 10 → ℚ)), Compatible f U →
      ∀ (u : Fin 10 → ℝ) (L : ℝ), 0 ≤ L →
      ∀ (m : ℕ), 0 < m → ∀ b : Fin 10 → ℤ,
        ((ConeComponentProgressionCount.points (part f U j) u L m b).card : ℝ) ≤
          C*(1+L/(m : ℝ))^r := by
  classical
  obtain ⟨c,Y,s,G,d,hcover,hcomp⟩ :=
    MicrolocalRationalComponents.exists_components h hF hj (by omega : j.val < 10)
  let I : Fin c → Ideal (MvPolynomial (Fin 10) ℚ) :=
    fun i => IntegralModelDimension.rationalIdeal (G i)
  have hproper : ∀ i, I i ≠ ⊤ := fun i => (hcomp i).2.2.2.2.1.ne_top
  have hhom : ∀ i, (I i).IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ) :=
    fun i => (hcomp i).2.2.2.2.2.2.1
  have hd : ∀ i, ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸ I i) ≤ (r : Dimension) := by
    intro i
    change ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸ IntegralModelDimension.rationalIdeal (G i)) ≤ _
    rw [(hcomp i).2.2.2.2.2.2.2.1]
    exact (affineDimension_mono (hcomp i).1.subset).trans hdim
  obtain ⟨C,hC,hcount⟩ := ConeComponentProgressionCount.exists_ordinary_bound I hproper hhom r hd
  refine ⟨C,hC,?_⟩
  intro U hU
  apply hcount
  intro x hx
  have hR := part_subset_rationalDepth h U hU j hj hx
  change rationalEmbedding x ∈ rationalDepth f j.val at hR
  rw [hcover] at hR
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hR
  refine ⟨i,?_⟩
  change ∀ P ∈ IntegralModelDimension.rationalIdeal (G i), eval x P = 0
  rw [(hcomp i).2.2.1]
  intro P hP
  exact hP x hi

/-- The selected ordinary level-one and level-two bounds are T^8,T^7. -/
theorem exists_low_level_bound (h : Geometry F f)
    (hF : Anisotropic (map (Int.castRingHom ℚ) F)) (j : Fin 6)
    (hj : j.val = 1 ∨ j.val = 2) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (U : ℕ → Set (Fin 10 → ℚ)), Compatible f U →
      ∀ (u : Fin 10 → ℝ) (L : ℝ), 0 ≤ L →
      ∀ (m : ℕ), 0 < m → ∀ b : Fin 10 → ℤ,
        ((ConeComponentProgressionCount.points (part f U j) u L m b).card : ℝ) ≤
          C*(1+L/(m : ℝ))^(9-j.val) := by
  apply exists_ordinary_part_bound h hF j (by omega) (9-j.val)
  have hd := rationalDepth_dimension_le h hF (j:=j.val) (by omega) (by omega)
  simpa only [show 10-(j.val+1) = 9-j.val by omega] using hd

/-- The actual terminal rational part has the required linear progression
bound, using the stronger terminal geometry rather than the general gain. -/
theorem exists_terminal_bound (h : Geometry F f) (hhom : F.IsHomogeneous 3)
    (hF : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (U : ℕ → Set (Fin 10 → ℚ)), Compatible f U →
      ∀ (u : Fin 10 → ℝ) (L : ℝ), 0 ≤ L →
      ∀ (m : ℕ), 0 < m → ∀ b : Fin 10 → ℤ,
        ((ConeComponentProgressionCount.points (part f U ⟨5,by decide⟩) u L m b).card : ℝ) ≤
          C*(1+L/(m : ℝ)) := by
  simpa only [pow_one] using exists_ordinary_part_bound h hF ⟨5,by decide⟩ (by decide) 1
    (MicrolocalTerminalDepth.rationalDepth_five_dimension_le_one h hhom hF)

end CubicTenVariables.MicrolocalPromotedPartition
