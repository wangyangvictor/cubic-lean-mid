import HessianTheorem11.BibleProjectiveGeometry
import HessianTheorem11.ReducedChartScaling
import HessianTheorem11.ReducedMaximalComponent

/-! The affine cone/projective-chart dimension theorem is derived from
generic rank.  The only input is `GenericRankOpenInput`; product geometry,
finite irreducible decomposition, and the finite-union dimension formula
are proved in the imported development. -/

noncomputable section
namespace HessianTheorem11.ReducedProjectiveDimension
open MvPolynomial Module BibleProjectiveGeometry ReducedChartScaling

theorem scaledImage_mono {n : ℕ} {S T : Set (GeometricPoint n)}
    (h : S ⊆ T) : scaledImage S ⊆ scaledImage T := by
  rintro x ⟨s, hs, a, rfl⟩
  exact ⟨s, h hs, a, rfl⟩

theorem scaledImage_iUnion {n : ℕ} {ι : Type*}
    (S : ι → Set (GeometricPoint n)) :
    scaledImage (⋃ i, S i) = ⋃ i, scaledImage (S i) := by
  ext x
  constructor
  · rintro ⟨s, hs, a, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hs
    exact Set.mem_iUnion.mpr ⟨i, s, hi, a, rfl⟩
  · intro hx
    obtain ⟨i, s, hs, a, rfl⟩ := Set.mem_iUnion.mp hx
    exact ⟨s, Set.mem_iUnion.mpr ⟨i, hs⟩, a, rfl⟩

@[simp] theorem scaledImage_empty {n : ℕ} :
    scaledImage (∅ : Set (GeometricPoint n)) = ∅ := by
  ext x
  simp [scaledImage]

/-- The scaling dimension formula also holds for a reducible normalized
closed slice, by actual finite irreducible decomposition. -/
theorem scaledImage_dimension (GR : GenericRankOpenInput) {n : ℕ}
    (S : Set (GeometricPoint n)) (hS : AlgebraicallyClosedSet S)
    (i : Fin n) (hnorm : ∀ s ∈ S, s i = 1) :
    affineDimension (scaledImage S) = affineDimension S + 1 := by
  classical
  by_cases hne : S.Nonempty
  · apply le_antisymm
    · obtain ⟨c, C, hcover, hC⟩ := ReducedMaximalComponent.finite_components S hS
      rw [hcover, scaledImage_iUnion]
      apply affineDimension_fintype_union_le
      intro j
      rw [scaledImage_dimension_irreducible GR (C j) (hC j).closed
        (hC j).irreducible i (fun s hs => hnorm s ((hC j).subset hs))]
      apply add_le_add_left
      exact affineDimension_mono (by rw [← hcover]; exact (hC j).subset)
    · obtain ⟨C, hC, hd⟩ :=
        ReducedMaximalComponent.maximal_dimension_component S hS hne
      rw [← hd, ← scaledImage_dimension_irreducible GR C hC.closed
        hC.irreducible i (fun s hs => hnorm s (hC.subset hs))]
      exact affineDimension_mono (scaledImage_mono hC.subset)
  · have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [he, affineDimension_empty]

theorem affineChart_closed {n : ℕ} (Z : Set (GeometricPoint n))
    (hZ : AlgebraicallyClosedSet Z) (i : Fin n) :
    AlgebraicallyClosedSet (affineChart Z i) := by
  apply Set.Subset.antisymm _ (subset_geometricClosure _)
  intro x hx
  refine ⟨geometricClosure_subset_closed (fun y hy => hy.1) hZ hx, ?_⟩
  have he := hx (X i - 1) (by
    intro y hy
    change eval y (X i - 1) = 0
    simp [hy.2])
  change eval x (X i - 1) = 0 at he
  simpa only [eval_sub, eval_X, map_one, sub_eq_zero] using he

theorem scaledChart_subset {n : ℕ} (Z : Set (GeometricPoint n))
    (hcone : IsAffineCone Z) (i : Fin n) :
    scaledImage (affineChart Z i) ⊆ Z := by
  rintro x ⟨s, hs, a, rfl⟩
  exact hcone a s hs.1

theorem normalized_mem_chart {n : ℕ} (Z : Set (GeometricPoint n))
    (hcone : IsAffineCone Z) (x : GeometricPoint n) (hx : x ∈ Z)
    (i : Fin n) (hi : x i ≠ 0) :
    (x i)⁻¹ • x ∈ affineChart Z i := by
  exact ⟨hcone _ x hx, by simp [hi]⟩

/-- The actual scaled charts cover the whole nontrivial cone, including
the vertex (obtained by using scalar zero in any nonempty chart). -/
theorem cone_eq_iUnion_scaledChart {n : ℕ} (Z : Set (GeometricPoint n))
    (hcone : IsAffineCone Z) (hnonzero : ∃ x ∈ Z, x ≠ 0) :
    Z = ⋃ i : Fin n, scaledImage (affineChart Z i) := by
  obtain ⟨u, hu, hu0⟩ := hnonzero
  have hcoord : ∀ x : GeometricPoint n, x ≠ 0 → ∃ i, x i ≠ 0 := by
    intro x hx
    by_contra hn
    push_neg at hn
    exact hx (funext hn)
  apply Set.Subset.antisymm
  · intro x hx
    by_cases hx0 : x = 0
    · obtain ⟨i, hi⟩ := hcoord u hu0
      exact Set.mem_iUnion.mpr ⟨i, (u i)⁻¹ • u,
        normalized_mem_chart Z hcone u hu i hi, 0, by simp [hx0]⟩
    · obtain ⟨i, hi⟩ := hcoord x hx0
      exact Set.mem_iUnion.mpr ⟨i, (x i)⁻¹ • x,
        normalized_mem_chart Z hcone x hx i hi, x i, by simp [smul_smul, hi]⟩
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact scaledChart_subset Z hcone i hi

/-- The former AP input, proved for every closed affine cone from GR alone. -/
theorem dimension_cone (GR : GenericRankOpenInput) {n : ℕ}
    (Z : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z)
    (hcone : IsAffineCone Z) (hnonzero : ∃ x ∈ Z, x ≠ 0) :
    affineDimension Z = projectiveDimension Z + 1 := by
  classical
  have hscale (i : Fin n) := scaledImage_dimension GR (affineChart Z i)
    (affineChart_closed Z hZ i) i (fun s hs => hs.2)
  apply le_antisymm
  · conv_lhs => rw [cone_eq_iUnion_scaledChart Z hcone hnonzero]
    apply affineDimension_fintype_union_le
    intro i
    rw [hscale]
    apply add_le_add_left
    exact le_iSup (fun j => affineDimension (affineChart Z j)) i
  · obtain ⟨x, hx, hx0⟩ := hnonzero
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact hx0 (funext hn)
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ
      (show (Finset.univ : Finset (Fin n)).Nonempty from ⟨j, Finset.mem_univ j⟩)
      (fun i => affineDimension (affineChart Z i))
    have he : Finset.univ.sup (fun i => affineDimension (affineChart Z i)) =
        projectiveDimension Z := by
      simp only [Finset.sup_eq_iSup, Finset.mem_univ, iSup_true, projectiveDimension]
    rw [← he, hi, ← hscale]
    exact affineDimension_mono (scaledChart_subset Z hcone i)

def affineProjectiveDimensionInput (GR : GenericRankOpenInput) :
    AffineProjectiveDimensionInput where
  dimension_cone := dimension_cone GR

end HessianTheorem11.ReducedProjectiveDimension
