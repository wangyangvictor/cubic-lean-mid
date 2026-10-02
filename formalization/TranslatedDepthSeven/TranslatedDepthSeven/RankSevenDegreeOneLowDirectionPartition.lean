import TranslatedDepthSeven.RankSevenDegreeOneProperStarActualNonvertex

/-!
# Static partition of the actual low projective directions

Each member of the literal low-direction finset is represented by one
actual active component occurrence.  According to that fixed
representative, the direction lies in exactly one of three disjoint sets:

* a projective-vertex direction;
* a Jacobian-regular nonvertex direction;
* a Jacobian-nonregular nonvertex direction.

This is a finite-set partition only.  It contains no estimate for any of
the three sets or for any fibre.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

local instance rankSevenLowDirectionPartitionDecidableEq :
    DecidableEq (Projectivization ℚ (Fin 13 → ℚ)) := Classical.decEq _

/-- One actual active component occurrence representing a member of the
literal low-direction image. -/
def activeLowDirectionRepresentativeOccurrence
    {ι : Type*} [Fintype ι]
    (J : ι → Ideal (MvPolynomial (Fin 13) ℝ))
    (Y : ι → Finset (IntVector 13))
    (direction : TaggedLinearComponent J → IntVector 13)
    (T : NNReal)
    (h : {h // h ∈ activeLowProjectiveDirections J Y direction T}) :
    TaggedLinearComponent J :=
  Classical.choose (Finset.mem_image.mp h.2)

/-- The chosen representative is active. -/
theorem activeLowDirectionRepresentativeOccurrence_mem_active
    {ι : Type*} [Fintype ι]
    (J : ι → Ideal (MvPolynomial (Fin 13) ℝ))
    (Y : ι → Finset (IntVector 13))
    (direction : TaggedLinearComponent J → IntVector 13)
    (T : NNReal)
    (h : {h // h ∈ activeLowProjectiveDirections J Y direction T}) :
    activeLowDirectionRepresentativeOccurrence J Y direction T h ∈
      activeTaggedLinearComponents J Y := by
  classical
  have hs := Classical.choose_spec (Finset.mem_image.mp h.2)
  exact (Finset.mem_filter.mp hs.1).1

/-- The chosen representative satisfies the literal low-height cutoff. -/
theorem activeLowDirectionRepresentativeOccurrence_height
    {ι : Type*} [Fintype ι]
    (J : ι → Ideal (MvPolynomial (Fin 13) ℝ))
    (Y : ι → Finset (IntVector 13))
    (direction : TaggedLinearComponent J → IntVector 13)
    (T : NNReal)
    (h : {h // h ∈ activeLowProjectiveDirections J Y direction T}) :
    directionHeight
        (direction (activeLowDirectionRepresentativeOccurrence
          J Y direction T h)) ≤
      lowDirectionNaturalRadius T := by
  classical
  have hs := Classical.choose_spec (Finset.mem_image.mp h.2)
  exact (Finset.mem_filter.mp hs.1).2

/-- The chosen occurrence represents precisely the given projective
direction. -/
theorem activeLowDirectionRepresentativeOccurrence_class
    {ι : Type*} [Fintype ι]
    (J : ι → Ideal (MvPolynomial (Fin 13) ℝ))
    (Y : ι → Finset (IntVector 13))
    (direction : TaggedLinearComponent J → IntVector 13)
    (T : NNReal)
    (h : {h // h ∈ activeLowProjectiveDirections J Y direction T}) :
    integralProjectiveClassOrFirstRankSeven
        (direction (activeLowDirectionRepresentativeOccurrence
          J Y direction T h)) = h.1 := by
  classical
  exact Classical.choose_spec (Finset.mem_image.mp h.2) |>.2

/-- Low directions whose fixed representative lies in the geometric
projective vertex. -/
def activeLowVertexDirections
    {ι : Type*} [Fintype ι]
    (J : ι → Ideal (MvPolynomial (Fin 13) ℝ))
    (Y : ι → Finset (IntVector 13))
    (direction : TaggedLinearComponent J → IntVector 13)
    (T : NNReal)
    (I : Ideal (MvPolynomial (Fin 13) ℚ)) :
    Finset {h // h ∈ activeLowProjectiveDirections J Y direction T} := by
  classical
  exact (activeLowProjectiveDirections J Y direction T).attach.filter fun h ↦
    LiesInGeometricProjectiveVertex
      (direction (activeLowDirectionRepresentativeOccurrence
        J Y direction T h)) I

/-- Jacobian-regular low directions outside the projective vertex. -/
def activeLowRegularNonvertexDirections
    {ι : Type*} [Fintype ι]
    (J : ι → Ideal (MvPolynomial (Fin 13) ℝ))
    (Y : ι → Finset (IntVector 13))
    (direction : TaggedLinearComponent J → IntVector 13)
    (T : NNReal)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (I : Ideal (MvPolynomial (Fin 13) ℚ)) :
    Finset {h // h ∈ activeLowProjectiveDirections J Y direction T} := by
  classical
  exact (activeLowProjectiveDirections J Y direction T).attach.filter fun h ↦
    ¬ LiesInGeometricProjectiveVertex
        (direction (activeLowDirectionRepresentativeOccurrence
          J Y direction T h)) I ∧
      IsDepthSevenJacobianRegularAt equations
        (direction (activeLowDirectionRepresentativeOccurrence
          J Y direction T h))

/-- Jacobian-nonregular low directions outside the projective vertex. -/
def activeLowNonregularNonvertexDirections
    {ι : Type*} [Fintype ι]
    (J : ι → Ideal (MvPolynomial (Fin 13) ℝ))
    (Y : ι → Finset (IntVector 13))
    (direction : TaggedLinearComponent J → IntVector 13)
    (T : NNReal)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (I : Ideal (MvPolynomial (Fin 13) ℚ)) :
    Finset {h // h ∈ activeLowProjectiveDirections J Y direction T} := by
  classical
  exact (activeLowProjectiveDirections J Y direction T).attach.filter fun h ↦
    ¬ LiesInGeometricProjectiveVertex
        (direction (activeLowDirectionRepresentativeOccurrence
          J Y direction T h)) I ∧
      ¬ IsDepthSevenJacobianRegularAt equations
        (direction (activeLowDirectionRepresentativeOccurrence
          J Y direction T h))

/-- The three displayed low-direction sets form an exact disjoint
classification.  The priority given to the vertex makes no unproved
regularity assertion about vertex points necessary. -/
theorem mem_exactly_one_activeLowDirection_class
    {ι : Type*} [Fintype ι]
    (J : ι → Ideal (MvPolynomial (Fin 13) ℝ))
    (Y : ι → Finset (IntVector 13))
    (direction : TaggedLinearComponent J → IntVector 13)
    (T : NNReal)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (I : Ideal (MvPolynomial (Fin 13) ℚ))
    (h : {h // h ∈ activeLowProjectiveDirections J Y direction T}) :
    (h ∈ activeLowVertexDirections J Y direction T I ∧
      h ∉ activeLowRegularNonvertexDirections
        J Y direction T equations I ∧
      h ∉ activeLowNonregularNonvertexDirections
        J Y direction T equations I) ∨
    (h ∉ activeLowVertexDirections J Y direction T I ∧
      h ∈ activeLowRegularNonvertexDirections
        J Y direction T equations I ∧
      h ∉ activeLowNonregularNonvertexDirections
        J Y direction T equations I) ∨
    (h ∉ activeLowVertexDirections J Y direction T I ∧
      h ∉ activeLowRegularNonvertexDirections
        J Y direction T equations I ∧
      h ∈ activeLowNonregularNonvertexDirections
        J Y direction T equations I) := by
  classical
  simp only [activeLowVertexDirections,
    activeLowRegularNonvertexDirections,
    activeLowNonregularNonvertexDirections, Finset.mem_filter,
    Finset.mem_attach, true_and]
  by_cases hv : LiesInGeometricProjectiveVertex
      (direction (activeLowDirectionRepresentativeOccurrence
        J Y direction T h)) I
  · exact Or.inl ⟨hv, by simp [hv], by simp [hv]⟩
  · by_cases hr : IsDepthSevenJacobianRegularAt equations
        (direction (activeLowDirectionRepresentativeOccurrence
          J Y direction T h))
    · exact Or.inr (Or.inl ⟨hv, ⟨hv, hr⟩, by simp [hr]⟩)
    · exact Or.inr (Or.inr ⟨hv, by simp [hr], ⟨hv, hr⟩⟩)

/-- Finset form of the exhaustive classification. -/
theorem activeLowDirections_attach_eq_three_classes
    {ι : Type*} [Fintype ι]
    (J : ι → Ideal (MvPolynomial (Fin 13) ℝ))
    (Y : ι → Finset (IntVector 13))
    (direction : TaggedLinearComponent J → IntVector 13)
    (T : NNReal)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (I : Ideal (MvPolynomial (Fin 13) ℚ)) :
    (activeLowProjectiveDirections J Y direction T).attach =
      activeLowVertexDirections J Y direction T I ∪
        (activeLowRegularNonvertexDirections
          J Y direction T equations I ∪
        activeLowNonregularNonvertexDirections
          J Y direction T equations I) := by
  classical
  ext h
  simp only [Finset.mem_attach, Finset.mem_union, true_iff]
  rcases mem_exactly_one_activeLowDirection_class
    J Y direction T equations I h with hv | hr | hs
  · exact Or.inl hv.1
  · exact Or.inr (Or.inl hr.2.1)
  · exact Or.inr (Or.inr hs.2.2)

end

end TranslatedDepthSeven
