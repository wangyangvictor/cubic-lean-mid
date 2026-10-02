import CubicTenVariables.ComplementAllocationSamples
import CubicTenVariables.ComplementMergedMultiplicity
import CubicTenVariables.ComplementSieveProfileBridge

/-! The actual split-allocation image has at most D^ε times as many
points as its merged image. Each fiber retains its original frequency;
only the finite choices of splitting squarefree factors are counted. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ComplementAllocationFibers
open MvPolynomial NumericalPrimeDepth NumericalDepthAllocation ComplementAllocationSamples
open scoped BigOperators
variable {F : MvPolynomial (Fin 10) ℤ} {C : ℝ}

/-- The product of all actual merged tail factors is bounded by the
original cube-free modulus, with its square on the square-prime slot. -/
theorem merged_product_le (h : CoarseBounds F C) (i : Fin 5) (x : Sample)
    (ha : 0 < x.1.1) (hb : 0 < x.1.2) :
    (∏ k, (ComplementMergedSieve.mergedTuple h i x).1 k) ≤ x.1.1*x.1.2^2 := by
  change (∏ k : Fin (5-i.val), mergedPart h x.1.1 x.1.2 x.2 (i.val+k.val+2)) ≤ _
  rw [show (∏ k : Fin (5-i.val), mergedPart h x.1.1 x.1.2 x.2 (i.val+k.val+2)) =
      ∏ j ∈ Finset.Icc (i.val+2) 6, mergedPart h x.1.1 x.1.2 x.2 j from
    ComplementSieveProfileBridge.prod_depth i (mergedPart h x.1.1 x.1.2 x.2)]
  apply le_trans _ (deepModulus_le h x.1.1 x.1.2 ha hb x.2 (i.val+2))
  apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
  intro j hj
  dsimp [mergedPart]
  have hp : 1 ≤ squarePart h x.1.2 x.2 j := (parts_pos h x.1.1 x.1.2 x.2 j).2
  exact Nat.mul_le_mul_left _ (by nlinarith)

/-- Squarefreeness and distinct-depth coprimality hold for the literal
merged vector of every admissible original pair. -/
theorem merged_properties (h : CoarseBounds F C) (i : Fin 5) (x : Sample)
    (ha : Squarefree x.1.1) (hb : Squarefree x.1.2) (hab : x.1.1.Coprime x.1.2) :
    (∀ k, Squarefree ((ComplementMergedSieve.mergedTuple h i x).1 k)) ∧
      Pairwise (fun k l => ((ComplementMergedSieve.mergedTuple h i x).1 k).Coprime
        ((ComplementMergedSieve.mergedTuple h i x).1 l)) := by
  refine ⟨fun k => merged_squarefree h x.1.1 x.1.2 ha hb hab x.2 _,?_⟩
  intro k l hkl
  apply merged_coprime h x.1.1 x.1.2 hab x.2
  intro he
  apply hkl
  apply Fin.ext
  omega

/-- One constant is chosen before the modulus size and every finite
sample family. No multiplicity estimate or geometric hypothesis is supplied. -/
theorem exists_bound (h : CoarseBounds F C) (i : Fin 5) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ D : ℝ, 1 ≤ D → ∀ E : Finset Sample,
      (∀ x ∈ E, Squarefree x.1.1 ∧ Squarefree x.1.2 ∧ x.1.1.Coprime x.1.2 ∧
        (x.1.1 : ℝ)*(x.1.2 : ℝ)^2 ≤ 2*D) →
      ((E.image (allocationTuple h i)).card : ℝ) ≤
        K*D^ε*((E.image (ComplementMergedSieve.mergedTuple h i)).card : ℝ) := by
  classical
  obtain ⟨K,hK,hbound⟩ := ComplementMergedMultiplicity.exists_uniform_bound
    (ι := Fin (5-i.val)) ε hε
  refine ⟨K,hK,?_⟩
  intro D hD E hE
  let A := E.image (allocationTuple h i)
  let B := E.image (ComplementMergedSieve.mergedTuple h i)
  have hfiber (z) (hz : z ∈ B) :
      ((A.filter (fun y => mergeAllocation i y=z)).card : ℝ) ≤ K*D^ε := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    have hxprop := hE x hx
    have hprops := merged_properties h i x hxprop.1 hxprop.2.1 hxprop.2.2.1
    have hsize : ((∏ k, (ComplementMergedSieve.mergedTuple h i x).1 k : ℕ) : ℝ) ≤ 2*D := by
      have hh : ((∏ k, (ComplementMergedSieve.mergedTuple h i x).1 k : ℕ) : ℝ) ≤
          (x.1.1 : ℝ)*(x.1.2 : ℝ)^2 := by
        exact_mod_cast merged_product_le h i x (Nat.pos_of_ne_zero hxprop.1.ne_zero)
          (Nat.pos_of_ne_zero hxprop.2.1.ne_zero)
      exact hh.trans hxprop.2.2.2
    let V := A.filter (fun y => mergeAllocation i y=ComplementMergedSieve.mergedTuple h i x)
    have hinj : Set.InjOn Prod.fst (↑V : Set (Allocation i)) := by
      intro y hy z hz he
      apply Prod.ext he
      have hy' := congrArg Prod.snd (Finset.mem_filter.mp hy).2
      have hz' := congrArg Prod.snd (Finset.mem_filter.mp hz).2
      exact hy'.trans hz'.symm
    have hcard : (V.image Prod.fst).card=V.card := Finset.card_image_of_injOn hinj
    have hm : ∀ y ∈ V.image Prod.fst, ∀ k,
        y.1 k*y.2 k=(ComplementMergedSieve.mergedTuple h i x).1 k := by
      intro y hy k
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy
      exact congrFun (congrArg Prod.fst (Finset.mem_filter.mp hz).2) k
    have hb := hbound D hD (ComplementMergedSieve.mergedTuple h i x).1
      hprops.1 hprops.2 hsize (V.image Prod.fst) hm
    rwa [hcard] at hb
  have hmap : (↑A : Set (Allocation i)).MapsTo (mergeAllocation i) B := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    rw [merge_allocationTuple]
    exact Finset.mem_image_of_mem _ hx
  have hcard := Finset.card_eq_sum_card_fiberwise hmap
  change (A.card : ℝ) ≤ K*D^ε*(B.card : ℝ)
  rw [hcard,Nat.cast_sum]
  calc
    _ ≤ ∑ z ∈ B, K*D^ε := Finset.sum_le_sum hfiber
    _ = _ := by simp [Finset.sum_const]; ring

end CubicTenVariables.ComplementAllocationFibers
