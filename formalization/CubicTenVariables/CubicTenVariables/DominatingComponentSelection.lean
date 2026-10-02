import CubicTenVariables.FiniteDenseOpen
import CubicTenVariables.GenericWholeFiberDimension
import HessianTheorem11.ReducedMaximalComponent

/-!
Large fibers on a Zariski-dense set of parameters force an actual sufficiently
large dominating irreducible component. The source may be reducible. The
proof uses the proved generic whole-source fiber bounds and finite unions;
no properness or fiber semicontinuity statement is assumed.
-/

noncomputable section
namespace CubicTenVariables.DominatingComponentSelection
open MvPolynomial HessianTheorem11

/-- A literal fiber of a finite union is the union of the literal fibers. -/
theorem fiber_iUnion {n m : ℕ} {ι : Type*}
    (P : Fin m → GeometricPolynomial n) (C : ι → Set (GeometricPoint n))
    (v : GeometricPoint m) :
    {x | x ∈ ⋃ i, C i ∧ polynomialMap P x = v} =
      ⋃ i, {x | x ∈ C i ∧ polynomialMap P x = v} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  aesop

/-- A dense set of actual large fibers, rather than a semicontinuity
hypothesis, supplies the needed dominating component of the actual source. -/
theorem exists_large_dominating_component {n m s k : ℕ}
    (P : Fin m → GeometricPolynomial n)
    (T : Set (GeometricPoint n)) (hT : AlgebraicallyClosedSet T)
    (Z A : Set (GeometricPoint m)) (hZ : AlgebraicallyClosedSet Z)
    (hiZ : GeometricallyIrreducible Z)
    (himage : polynomialMap P '' T ⊆ Z)
    (hs : affineDimension Z = (s : Dimension))
    (hA : geometricClosure A = Z) (hk : 0 < k)
    (hlarge : ∀ v ∈ A,
      (k : Dimension) ≤ affineDimension {x | x ∈ T ∧ polynomialMap P x = v}) :
    ∃ Y, IsIrreducibleComponent T Y ∧
      geometricClosure (polynomialMap P '' Y) = Z ∧
      ((s + k : ℕ) : Dimension) ≤ affineDimension Y := by
  classical
  obtain ⟨c, C, hcover, hC⟩ := ReducedMaximalComponent.finite_components T hT
  by_contra hnone
  have hopen : ∀ i : Fin c, ∃ O, RelativelyOpenSet Z O ∧ O.Nonempty ∧
      ∀ v ∈ O, affineDimension {x | x ∈ C i ∧ polynomialMap P x = v} ≤
        ((k - 1 : ℕ) : Dimension) := by
    intro i
    let Zi := geometricClosure (polynomialMap P '' C i)
    have hZi : AlgebraicallyClosedSet Zi := algebraicallyClosedSet_geometricClosure _
    have hZiZ : Zi ⊆ Z := geometricClosure_subset_closed
      ((Set.image_mono (hC i).subset).trans himage) hZ
    by_cases hdom : Zi = Z
    · obtain ⟨d, hd⟩ := ReducedComponentDimension.finite_dimension (C i)
        (hC i).irreducible.nonempty
      have his : affineDimension (geometricClosure (polynomialMap P '' C i)) =
          (s : Dimension) := by
        change affineDimension Zi = (s : Dimension)
        rw [hdom]
        exact hs
      obtain ⟨O, hO, hnO, _, hb⟩ :=
        GenericWholeFiberDimension.exists_dense_open_whole_fiber_dimension_le
          P (C i) (hC i).closed (hC i).irreducible d s hd his
      rw [show geometricClosure (polynomialMap P '' C i) = Z from hdom] at hO
      have hnot : ¬ ((s + k : ℕ) : Dimension) ≤ affineDimension (C i) :=
        fun he => hnone ⟨C i, hC i, hdom, he⟩
      rw [hd] at hnot
      have hds : d < s + k := by exact_mod_cast lt_of_not_ge hnot
      have hdsub : d - s ≤ k - 1 := by omega
      refine ⟨O, hO, hnO, ?_⟩
      intro v hv
      exact (hb v hv).trans (by exact_mod_cast hdsub)
    · have hnot : ¬ Z ⊆ Zi := by
        intro hsub
        exact hdom (Set.Subset.antisymm hZiZ hsub)
      refine ⟨Z \ Zi, ⟨Zi, hZi, rfl⟩, Set.diff_nonempty.mpr hnot, ?_⟩
      intro v hv
      have hf : {x | x ∈ C i ∧ polynomialMap P x = v} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        apply hv.2
        rw [← hx.2]
        exact subset_geometricClosure _ ⟨x, hx.1, rfl⟩
      rw [hf, affineDimension_empty]
      exact bot_le
  choose O hO hnO hb using hopen
  obtain ⟨U, hU, hnU, _, hsub⟩ :=
    FiniteDenseOpen.exists_common_dense_open Z hZ hiZ O hO hnO
  obtain ⟨v, hvA, hvU⟩ :=
    ReducedGenericImageTangent.dense_inter_open_nonempty hA hU hnU
  have hu : affineDimension {x | x ∈ T ∧ polynomialMap P x = v} ≤
      ((k - 1 : ℕ) : Dimension) := by
    rw [hcover, fiber_iUnion]
    exact affineDimension_fintype_union_le _ (fun i => hb i v (hsub i hvU))
  have hh : k ≤ k - 1 := by exact_mod_cast (hlarge v hvA).trans hu
  omega

end CubicTenVariables.DominatingComponentSelection
