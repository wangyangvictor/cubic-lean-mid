import CubicTenVariables.GenericOpenFiberDimension
import CubicTenVariables.FiniteDenseOpen
import HessianTheorem11.ReducedStrictDimension
import HessianTheorem11.UnconditionalChevalleyOpen

/-!
# Generic dimensions of the literal whole-source fibers

The upper bound is proved by strong induction on the dimension of the
closed irreducible source. The generic-rank source-open has the expected
fiber bound. Each irreducible component of its closed complement has
strictly smaller dimension. Dominating components are treated recursively;
the proper image closures of the other components are removed from the
base. A finite intersection of the resulting dense opens controls the
whole source fiber. No semicontinuity or fiber-dimension package is assumed.
-/

noncomputable section
namespace CubicTenVariables.GenericWholeFiberDimension

open MvPolynomial HessianTheorem11 Module

/-- On a nonempty dense relative open of the actual image closure, all
literal fibers of the whole closed irreducible source have the expected
upper bound, including empty fibers. -/
theorem exists_dense_open_whole_fiber_dimension_le {n m : ℕ}
    (P : Fin m → GeometricPolynomial n) (Y : Set (GeometricPoint n))
    (hY : AlgebraicallyClosedSet Y) (hiY : GeometricallyIrreducible Y)
    (d s : ℕ) (hd : affineDimension Y = (d : Dimension))
    (hs : affineDimension (geometricClosure (polynomialMap P '' Y)) = (s : Dimension)) :
    ∃ O : Set (GeometricPoint m),
      RelativelyOpenSet (geometricClosure (polynomialMap P '' Y)) O ∧ O.Nonempty ∧
      geometricClosure O = geometricClosure (polynomialMap P '' Y) ∧
      ∀ v ∈ O, affineDimension {x | x ∈ Y ∧ polynomialMap P x = v} ≤
        ((d - s : ℕ) : Dimension) := by
  classical
  induction d using Nat.strong_induction_on generalizing Y s with
  | h d ih =>
    let Z := geometricClosure (polynomialMap P '' Y)
    have hZ : AlgebraicallyClosedSet Z := algebraicallyClosedSet_geometricClosure _
    have hiZ : GeometricallyIrreducible Z :=
      (geometricallyIrreducible_closure_iff _).mpr (hiY.polynomialMap_image P)
    obtain ⟨G⟩ := Unconditional.genericRankOpen.choose Y hY hiY P
      (0 : GeometricPoint n →ₗ[GeometricField] Matrix (Fin 0) (Fin 0) GeometricField)
    have hGd : G.baseDimension = d := by exact_mod_cast G.dimension_base.symm.trans hd
    have hGs : G.imageDimension = s := by exact_mod_cast G.dimension_image.symm.trans hs
    obtain ⟨D, hD, hGD⟩ := G.isOpen
    let E := Y ∩ D
    have hE : AlgebraicallyClosedSet E := by
      apply Set.Subset.antisymm _ (subset_geometricClosure _)
      exact fun x hx => ⟨geometricClosure_subset_closed Set.inter_subset_left hY hx,
        geometricClosure_subset_closed Set.inter_subset_right hD hx⟩
    obtain ⟨c, K, hcover, hK⟩ := ReducedMaximalComponent.finite_components E hE
    have hproper (i : Fin c) : K i ⊂ Y := by
      refine ⟨(hK i).subset.trans Set.inter_subset_left, ?_⟩
      intro hback
      obtain ⟨x, hx⟩ := G.nonempty
      have hxD := ((hK i).subset (hback (G.subset hx))).2
      exact (hGD ▸ hx).2 hxD
    have each (i : Fin c) : ∃ V : Set (GeometricPoint m),
        RelativelyOpenSet Z V ∧ V.Nonempty ∧
        ∀ v ∈ V, affineDimension {x | x ∈ K i ∧ polynomialMap P x = v} ≤
          ((d - s : ℕ) : Dimension) := by
      let Zi := geometricClosure (polynomialMap P '' K i)
      have hZi : AlgebraicallyClosedSet Zi := algebraicallyClosedSet_geometricClosure _
      have hZiZ : Zi ⊆ Z := geometricClosure_mono
        (Set.image_mono ((hK i).subset.trans Set.inter_subset_left))
      by_cases hdom : Zi = Z
      · obtain ⟨di, hdi⟩ := ReducedComponentDimension.finite_dimension (K i)
          (hK i).irreducible.nonempty
        have hdrop := ReducedStrictDimension.proper_closed (K i) Y
          (hK i).closed hY hiY (hproper i)
        rw [hdi, hd] at hdrop
        have hlt : di < d := by exact_mod_cast hdrop
        have hdimZi : affineDimension (geometricClosure (polynomialMap P '' K i)) =
            (s : Dimension) := by change affineDimension Zi = _; rw [hdom]; exact hs
        obtain ⟨V, hV, hnV, _, hbound⟩ := ih di hlt (K i) (hK i).closed
          (hK i).irreducible s hdi hdimZi
        refine ⟨V, ?_, hnV, ?_⟩
        · change RelativelyOpenSet Zi V at hV
          rwa [hdom] at hV
        · intro v hv
          exact (hbound v hv).trans (by exact_mod_cast (Nat.sub_le_sub_right hlt.le s))
      · have hnot : ¬ Z ⊆ Zi := fun hh => hdom (Set.Subset.antisymm hZiZ hh)
        obtain ⟨v, hvZ, hvZi⟩ := Set.not_subset.mp hnot
        refine ⟨Z \ Zi, ⟨Zi, hZi, rfl⟩, ⟨v, hvZ, hvZi⟩, ?_⟩
        intro w hw
        have hempty : {x | x ∈ K i ∧ polynomialMap P x = w} = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          rintro x ⟨hx, hxw⟩
          exact hw.2 (subset_geometricClosure _ ⟨x, hx, hxw⟩)
        rw [hempty, affineDimension_empty]
        exact bot_le
    choose V hV hnV hboundV using each
    obtain ⟨O, hO, hnO, hdO, hOV⟩ :=
      FiniteDenseOpen.exists_common_dense_open Z hZ hiZ V hV hnV
    refine ⟨O, hO, hnO, hdO, ?_⟩
    intro v hv
    have hdecomp : Y = G.openSet ∪ ⋃ i, K i := by
      rw [← hcover, hGD]
      change Y = (Y \ D) ∪ (Y ∩ D)
      ext x
      simp only [Set.mem_union, Set.mem_diff, Set.mem_inter_iff]
      tauto
    have hsplit : {x | x ∈ Y ∧ polynomialMap P x = v} =
        {x | x ∈ G.openSet ∧ polynomialMap P x = v} ∪
        ⋃ i, {x | x ∈ K i ∧ polynomialMap P x = v} := by
      ext x
      have hmem := Set.ext_iff.mp hdecomp x
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion] at hmem ⊢
      constructor
      · rintro ⟨hx, he⟩
        rcases hmem.mp hx with hx | ⟨i, hx⟩
        · exact Or.inl ⟨hx, he⟩
        · exact Or.inr ⟨i, hx, he⟩
      · rintro (⟨hx, he⟩ | ⟨i, hx, he⟩)
        · exact ⟨hmem.mpr (Or.inl hx), he⟩
        · exact ⟨hmem.mpr (Or.inr ⟨i, hx⟩), he⟩
    rw [hsplit, affineDimension_union]
    apply max_le
    · simpa only [hGd, hGs] using
        GenericOpenFiberDimension.generic_open_fiber_dimension_le hY G v
    · exact affineDimension_fintype_union_le _ (fun i => hboundV i v (hOV i hv))

/-- The image dimension cannot exceed the source dimension. This follows
from the actual generic differential and rank-nullity. -/
theorem image_dimension_le_source {n m : ℕ}
    (P : Fin m → GeometricPolynomial n) (Y : Set (GeometricPoint n))
    (hY : AlgebraicallyClosedSet Y) (hiY : GeometricallyIrreducible Y)
    (d s : ℕ) (hd : affineDimension Y = (d : Dimension))
    (hs : affineDimension (geometricClosure (polynomialMap P '' Y)) = (s : Dimension)) :
    s ≤ d := by
  obtain ⟨G⟩ := Unconditional.genericRankOpen.choose Y hY hiY P
    (0 : GeometricPoint n →ₗ[GeometricField] Matrix (Fin 0) (Fin 0) GeometricField)
  obtain ⟨x, hx⟩ := G.nonempty
  have hr := ((polynomialMapDifferential P x).domRestrict
    (affineTangentSpace Y x)).finrank_range_add_finrank_ker
  rw [G.differential_rank x hx, G.smooth x hx] at hr
  have hGd : G.baseDimension = d := by exact_mod_cast G.dimension_base.symm.trans hd
  have hGs : G.imageDimension = s := by exact_mod_cast G.dimension_image.symm.trans hs
  rw [hGd, hGs] at hr
  omega

/-- An expected upper bound becomes equality whenever the literal fiber
is nonempty, by the proved pointwise lower fiber inequality. -/
theorem whole_fiber_dimension_eq_of_nonempty {n m : ℕ}
    (P : Fin m → GeometricPolynomial n) (Y : Set (GeometricPoint n))
    (hY : AlgebraicallyClosedSet Y) (hiY : GeometricallyIrreducible Y)
    (d s : ℕ) (hd : affineDimension Y = (d : Dimension))
    (hs : affineDimension (geometricClosure (polynomialMap P '' Y)) = (s : Dimension))
    (v : GeometricPoint m)
    (hne : {x | x ∈ Y ∧ polynomialMap P x = v}.Nonempty)
    (hupper : affineDimension {x | x ∈ Y ∧ polynomialMap P x = v} ≤
      ((d - s : ℕ) : Dimension)) :
    affineDimension {x | x ∈ Y ∧ polynomialMap P x = v} =
      ((d - s : ℕ) : Dimension) := by
  obtain ⟨k, hk⟩ := ReducedComponentDimension.finite_dimension _ hne
  obtain ⟨x, hx, hxv⟩ := hne
  have hlow := UnconditionalFiberDimension.open_fiber_dimension P Y Y hY hiY
    (FiniteDenseOpen.relativelyOpen_self Y) x hx
  have himage : affineDimension (polynomialMap P '' Y) = (s : Dimension) :=
    (affineDimension_closure _).symm.trans hs
  rw [hxv, hd, himage, hk] at hlow
  rw [hk] at hupper ⊢
  have hu : k ≤ d - s := by exact_mod_cast hupper
  have hl : d ≤ s + k := by exact_mod_cast hlow
  congr 1
  omega

/-- A nonempty dense base-open contained in the actual image has
nonempty whole-source fibers of exactly the expected dimension at every
one of its geometric points. Chevalley's proved image-open theorem is
used only to ensure those fibers are nonempty. -/
theorem exists_dense_open_whole_fiber_dimension_eq {n m : ℕ}
    (P : Fin m → GeometricPolynomial n) (Y : Set (GeometricPoint n))
    (hY : AlgebraicallyClosedSet Y) (hiY : GeometricallyIrreducible Y)
    (d s : ℕ) (hd : affineDimension Y = (d : Dimension))
    (hs : affineDimension (geometricClosure (polynomialMap P '' Y)) = (s : Dimension)) :
    ∃ O : Set (GeometricPoint m),
      RelativelyOpenSet (geometricClosure (polynomialMap P '' Y)) O ∧ O.Nonempty ∧
      geometricClosure O = geometricClosure (polynomialMap P '' Y) ∧
      O ⊆ polynomialMap P '' Y ∧
      ∀ v ∈ O, affineDimension {x | x ∈ Y ∧ polynomialMap P x = v} =
        ((d - s : ℕ) : Dimension) := by
  obtain ⟨U, hU, _, hdU, hbound⟩ :=
    exists_dense_open_whole_fiber_dimension_le P Y hY hiY d s hd hs
  obtain ⟨V, hV, hnV, _, himage⟩ :=
    UnconditionalChevalleyOpen.exists_dense_open_subset_image_of_open P Y Y hY hiY
      (FiniteDenseOpen.relativelyOpen_self Y) hiY.nonempty
  have hopen := hU.inter hV
  have hne := ReducedGenericImageTangent.dense_inter_open_nonempty hdU hV hnV
  have hdense := hopen.dense_of_nonempty (algebraicallyClosedSet_geometricClosure _)
    ((geometricallyIrreducible_closure_iff _).mpr (hiY.polynomialMap_image P)) hne
  refine ⟨U ∩ V, hopen, hne, hdense, fun _ hv => himage hv.2, ?_⟩
  intro v hv
  obtain ⟨x, hx, hxv⟩ := himage hv.2
  exact whole_fiber_dimension_eq_of_nonempty P Y hY hiY d s hd hs v
    ⟨x, hx, hxv⟩ (hbound v hv.1)

end CubicTenVariables.GenericWholeFiberDimension
