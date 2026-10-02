import HessianTheorem11.ReducedGenericImageTangent

/-! Finite nonempty relative opens on an actual irreducible affine set have
an actual common nonempty dense relative open. No topological or generic-open
interface is assumed. -/

noncomputable section
namespace CubicTenVariables.FiniteDenseOpen
open MvPolynomial HessianTheorem11

/-- The whole set is relatively open in itself. -/
theorem relativelyOpen_self {n : ℕ} (Z : Set (GeometricPoint n)) :
    RelativelyOpenSet Z Z := by
  refine ⟨∅, ?_, by simp⟩
  change geometricClosure (∅ : Set (GeometricPoint n)) = ∅
  simp only [geometricClosure, vanishingIdeal_empty, zeroLocus_top]
  rfl

/-- Finite intersection, retaining an explicit subset witness for every open. -/
theorem exists_common_dense_open_finset {n : ℕ} {ι : Type*}
    (Z : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z)
    (hiZ : GeometricallyIrreducible Z) (s : Finset ι)
    (O : ι → Set (GeometricPoint n))
    (hO : ∀ i ∈ s, RelativelyOpenSet Z (O i)) (hne : ∀ i ∈ s, (O i).Nonempty) :
    ∃ U, RelativelyOpenSet Z U ∧ U.Nonempty ∧ geometricClosure U = Z ∧
      ∀ i ∈ s, U ⊆ O i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨Z, relativelyOpen_self Z, hiZ.nonempty, hZ, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨U, hU, hnU, hdU, hsub⟩ := ih
      (fun j hj => hO j (Finset.mem_insert_of_mem hj))
      (fun j hj => hne j (Finset.mem_insert_of_mem hj))
    have hOi := hO i (Finset.mem_insert_self i s)
    have hnOi := hne i (Finset.mem_insert_self i s)
    have hopen := hU.inter hOi
    have hn := ReducedGenericImageTangent.dense_inter_open_nonempty hdU hOi hnOi
    refine ⟨U ∩ O i, hopen, hn, hopen.dense_of_nonempty hZ hiZ hn, ?_⟩
    intro j hj x hx
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hx.2
    · exact hsub j hj hx.1

/-- The finite-type version used for actual irreducible components. -/
theorem exists_common_dense_open {n : ℕ} {ι : Type*} [Fintype ι]
    (Z : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z)
    (hiZ : GeometricallyIrreducible Z) (O : ι → Set (GeometricPoint n))
    (hO : ∀ i, RelativelyOpenSet Z (O i)) (hne : ∀ i, (O i).Nonempty) :
    ∃ U, RelativelyOpenSet Z U ∧ U.Nonempty ∧ geometricClosure U = Z ∧
      ∀ i, U ⊆ O i := by
  simpa only [Finset.mem_univ, forall_const] using
    exists_common_dense_open_finset Z hZ hiZ Finset.univ O
      (fun i _ => hO i) (fun i _ => hne i)

end CubicTenVariables.FiniteDenseOpen
