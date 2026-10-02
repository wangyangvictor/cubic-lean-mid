import TranslatedDepthSeven.RankSevenDegreeOneSelectedUnion

/-!
# A set-level linear/nonlinear component cover

The componentwise Pila estimate is often used only after taking
cardinalities.  For the rank-seven line ledger this loses essential
information: the degree-one pieces belonging to different records can
overlap.  This file retains the literal set cover.  Thus all degree-one
points can subsequently be counted through one finite union, while only the
nonlinear residuals are added component by component.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

/-- The literal subset of `X` lying on a minimal component which is not a
degree-one affine curve. -/
def finitePointsOnNonlinearAffineComponents {N : ℕ}
    (J : Ideal (MvPolynomial (Fin N) ℝ))
    (X : Finset (IntVector N)) : Finset (IntVector N) := by
  classical
  exact (nonlinearAffineComponents J).biUnion fun Q ↦
    finitePointsOnAffineIdeal X Q

/-- Every finite set of real zeros of `J` is covered by the literal
degree-one contribution and the literal nonlinear residual. -/
theorem finiteSet_subset_linear_union_nonlinearComponents
    {N : ℕ} (J : Ideal (MvPolynomial (Fin N) ℝ))
    (X : Finset (IntVector N))
    (hXzero : ∀ z ∈ X,
      (fun i ↦ (z i : ℝ)) ∈ affineIdealZeroLocus J) :
    X ⊆ finitePointsOnLinearCurveComponents J X ∪
      finitePointsOnNonlinearAffineComponents J X := by
  classical
  intro z hz
  let T : Ideal (MvPolynomial (Fin N) ℝ) :=
    RingHom.ker (MvPolynomial.eval (fun i ↦ (z i : ℝ)))
  letI : T.IsPrime := RingHom.ker_isPrime _
  have hJT : J ≤ T := by
    intro f hf
    exact RingHom.mem_ker.mpr (hXzero z hz f hf)
  obtain ⟨Q, hQ, hQT⟩ := exists_finiteMinimalPrime_le hJT
  by_cases hlinear : HasAffineHilbertDimensionDegree Q 1 1
  · apply Finset.mem_union_left
    rw [finitePointsOnLinearCurveComponents]
    refine Finset.mem_biUnion.mpr ⟨Q, hQ, ?_⟩
    simp only [if_pos hlinear]
    exact (mem_finitePointsOnAffineIdeal_iff X Q z).mpr
      ⟨hz, fun f hf ↦ RingHom.mem_ker.mp (hQT hf)⟩
  · apply Finset.mem_union_right
    rw [finitePointsOnNonlinearAffineComponents]
    refine Finset.mem_biUnion.mpr ⟨Q, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨hQ, hlinear⟩
    · exact (mem_finitePointsOnAffineIdeal_iff X Q z).mpr
        ⟨hz, fun f hf ↦ RingHom.mem_ker.mp (hQT hf)⟩

/-- The selected underlying line union is exactly the union of the literal
degree-one contributions over the record family. -/
theorem underlyingLinearContributionPoints_eq_biUnion
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N)) :
    underlyingLinearContributionPoints J X =
      (Finset.univ : Finset ι).biUnion fun i ↦
        finitePointsOnLinearCurveComponents (J i) (X i) := by
  classical
  ext z
  simp only [mem_underlyingLinearContributionPoints_iff,
    Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.1, x.2.2⟩
  · rintro ⟨i, hz⟩
    exact ⟨⟨i, ⟨z, hz⟩⟩, rfl⟩

/-- A finite union of cells is covered by one multiplicity-free degree-one
union and the union of the nonlinear residuals. -/
theorem biUnion_subset_underlyingLinear_union_nonlinearComponents
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N))
    (hXzero : ∀ i z, z ∈ X i →
      (fun j ↦ (z j : ℝ)) ∈ affineIdealZeroLocus (J i)) :
    (Finset.univ : Finset ι).biUnion X ⊆
      underlyingLinearContributionPoints J X ∪
        ((Finset.univ : Finset ι).biUnion fun i ↦
          finitePointsOnNonlinearAffineComponents (J i) (X i)) := by
  classical
  intro z hz
  obtain ⟨i, _hi, hzi⟩ := Finset.mem_biUnion.mp hz
  have hsplit := finiteSet_subset_linear_union_nonlinearComponents
    (J i) (X i) (hXzero i) hzi
  rcases Finset.mem_union.mp hsplit with hlinear | hnonlinear
  · apply Finset.mem_union_left
    rw [underlyingLinearContributionPoints_eq_biUnion]
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hlinear⟩
  · apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hnonlinear⟩

/-- The cardinal form of the literal family cover.  Only the nonlinear
residuals are summed; all degree-one points remain in a single union. -/
theorem card_biUnion_le_underlyingLinear_add_sum_nonlinearComponents
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N))
    (hXzero : ∀ i z, z ∈ X i →
      (fun j ↦ (z j : ℝ)) ∈ affineIdealZeroLocus (J i)) :
    ((Finset.univ : Finset ι).biUnion X).card ≤
      (underlyingLinearContributionPoints J X).card +
        ∑ i : ι,
          (finitePointsOnNonlinearAffineComponents (J i) (X i)).card := by
  classical
  let nonlinearUnion : Finset (IntVector N) :=
    (Finset.univ : Finset ι).biUnion fun i ↦
      finitePointsOnNonlinearAffineComponents (J i) (X i)
  have hcover := biUnion_subset_underlyingLinear_union_nonlinearComponents
    J X hXzero
  have hnonlinear : nonlinearUnion.card ≤
      ∑ i : ι,
        (finitePointsOnNonlinearAffineComponents (J i) (X i)).card := by
    simpa only [nonlinearUnion] using
      (Finset.card_biUnion_le
        (s := (Finset.univ : Finset ι))
        (t := fun i ↦ finitePointsOnNonlinearAffineComponents (J i) (X i)))
  calc
    ((Finset.univ : Finset ι).biUnion X).card ≤
        (underlyingLinearContributionPoints J X ∪ nonlinearUnion).card :=
      Finset.card_le_card hcover
    _ ≤ (underlyingLinearContributionPoints J X).card + nonlinearUnion.card :=
      Finset.card_union_le _ _
    _ ≤ (underlyingLinearContributionPoints J X).card +
        ∑ i : ι,
          (finitePointsOnNonlinearAffineComponents (J i) (X i)).card :=
      Nat.add_le_add_left hnonlinear _

end

end TranslatedDepthSeven
