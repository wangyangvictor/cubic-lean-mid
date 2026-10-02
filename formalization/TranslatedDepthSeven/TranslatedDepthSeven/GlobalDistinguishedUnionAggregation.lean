import TranslatedDepthSeven.PersistentSingleMarkResidual

/-!
# One distinguished union before summing local errors

This is the finite-set bookkeeping needed after applying a proper-cut
estimate to each retained record.  The distinguished degree-one pieces are
first united as sets.  Only the complements inside the individual record
cells are then added, so a point lying on several retained lines is never
charged with the multiplicity of those lines or records.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- If every local cell is bounded by its distinguished subset plus a local
error, then removing the *one global union* of all distinguished subsets
from any covered point set leaves at most the sum of the local errors.

No disjointness of the cells or distinguished subsets is assumed. -/
theorem card_sdiff_globalDistinguished_le_sum_errors
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (points : Finset α) (records : Finset ι)
    (cell distinguished : ι → Finset α) (error : ι → ℝ)
    (hcover : points ⊆ records.biUnion cell)
    (hdistinguished : ∀ i ∈ records, distinguished i ⊆ cell i)
    (hlocal : ∀ i ∈ records,
      ((cell i).card : ℝ) ≤ ((distinguished i).card : ℝ) + error i) :
    (((points \ records.biUnion distinguished).card : ℕ) : ℝ) ≤
      ∑ i ∈ records, error i := by
  classical
  have hresidualCover :
      points \ records.biUnion distinguished ⊆
        records.biUnion (fun i ↦ cell i \ distinguished i) := by
    intro z hz
    obtain ⟨hzPoints, hzNotDistinguished⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨i, hi, hzCell⟩ := Finset.mem_biUnion.mp (hcover hzPoints)
    apply Finset.mem_biUnion.mpr
    refine ⟨i, hi, Finset.mem_sdiff.mpr ⟨hzCell, ?_⟩⟩
    intro hzDistinguished
    exact hzNotDistinguished
      (Finset.mem_biUnion.mpr ⟨i, hi, hzDistinguished⟩)
  have hcardNat :
      (points \ records.biUnion distinguished).card ≤
        ∑ i ∈ records, (cell i \ distinguished i).card :=
    (Finset.card_le_card hresidualCover).trans Finset.card_biUnion_le
  have hcardReal :
      (((points \ records.biUnion distinguished).card : ℕ) : ℝ) ≤
        ∑ i ∈ records, (((cell i \ distinguished i).card : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  apply hcardReal.trans
  exact Finset.sum_le_sum fun i hi ↦
    card_sdiff_cast_le_of_card_le_add
      (cell i) (distinguished i) (hdistinguished i hi) (error i)
        (hlocal i hi)

/-- Cardinal form of the same bookkeeping.  The global distinguished union
appears exactly once; all record dependence is confined to the sum of local
errors. -/
theorem card_le_globalDistinguished_add_sum_errors
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (points : Finset α) (records : Finset ι)
    (cell distinguished : ι → Finset α) (error : ι → ℝ)
    (hcover : points ⊆ records.biUnion cell)
    (hdistinguished : ∀ i ∈ records, distinguished i ⊆ cell i)
    (hlocal : ∀ i ∈ records,
      ((cell i).card : ℝ) ≤ ((distinguished i).card : ℝ) + error i) :
    (points.card : ℝ) ≤ ((records.biUnion distinguished).card : ℝ) +
      ∑ i ∈ records, error i := by
  classical
  let globalDistinguished := records.biUnion distinguished
  have hsplit : points ⊆ globalDistinguished ∪
      (points \ globalDistinguished) := by
    intro z hz
    by_cases hzd : z ∈ globalDistinguished
    · exact Finset.mem_union_left _ hzd
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hz, hzd⟩)
  have hcardNat : points.card ≤ globalDistinguished.card +
      (points \ globalDistinguished).card :=
    (Finset.card_le_card hsplit).trans
      (Finset.card_union_le globalDistinguished
        (points \ globalDistinguished))
  have hcardReal : (points.card : ℝ) ≤ (globalDistinguished.card : ℝ) +
      ((points \ globalDistinguished).card : ℝ) := by
    exact_mod_cast hcardNat
  apply hcardReal.trans
  have hresidual :=
    card_sdiff_globalDistinguished_le_sum_errors points records cell
      distinguished error hcover hdistinguished hlocal
  dsimp only [globalDistinguished]
  exact add_le_add_right hresidual _

end

end TranslatedDepthSeven
