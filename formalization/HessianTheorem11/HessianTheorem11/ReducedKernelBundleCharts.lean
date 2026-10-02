import HessianTheorem11.ReducedAffineProduct
import HessianTheorem11.KernelAnnihilatorProjector
import HessianTheorem11.ReducedDeterminantalDifferential
import HessianTheorem11.ReducedGenericImageTangent

/-! Polynomial adjugate-projector charts for the actual constant-rank
kernel bundle. Their common dense overlaps prove irreducibility without
any vector-bundle or other external geometry input. -/
noncomputable section
set_option maxHeartbeats 2400000
namespace HessianTheorem11.ReducedKernelBundleCharts
open MvPolynomial Module Matrix ReducedAffineProduct KernelAnnihilatorProjector
  ReducedDeterminantal

variable {n a b r : ℕ}

def fiberMap (A : Matrix (Fin b) (Fin b) (GeometricPolynomial n)) :
    (Fin n ⊕ Fin b) → MvPolynomial (Fin n ⊕ Fin b) GeometricField :=
  Sum.elim (fun i => X (Sum.inl i))
    (fun j => ∑ k, rename Sum.inl (A j k) * X (Sum.inr k))

@[simp] theorem eval_fiberMap (A : Matrix (Fin b) (Fin b) (GeometricPolynomial n))
    (p : PairPoint n b) : polynomialMap (fiberMap A) p =
      pairPoint (pairLeft p) ((A.map (eval (pairLeft p))).mulVec (pairRight p)) := by
  ext (i|j) <;>
    simp [fiberMap, polynomialMap, pairPoint, pairLeft, pairRight, eval_rename,
      Matrix.mulVec, dotProduct]

def minorPolynomial
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
    (rows : Fin r → Fin a) (cols : Fin r → Fin b) : GeometricPolynomial n :=
  ((pencilPolynomial M).submatrix rows cols).det

@[simp] theorem eval_pencil
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
    (x : GeometricPoint n) : (pencilPolynomial M).map (eval x) = M x := by
  ext i j
  exact eval_pencilPolynomial M x i j

@[simp] theorem eval_minorPolynomial
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
    (rows : Fin r → Fin a) (cols : Fin r → Fin b) (x : GeometricPoint n) :
    eval x (minorPolynomial M rows cols) = ((M x).submatrix rows cols).det := by
  have h := (eval x).map_det ((pencilPolynomial M).submatrix rows cols)
  change eval x (minorPolynomial M rows cols) =
    (((pencilPolynomial M).map (eval x)).submatrix rows cols).det at h
  rwa [eval_pencil] at h

def chartMap
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
    (rows : Fin r → Fin a) (cols : Fin r → Fin b) :
    (Fin n ⊕ Fin b) → MvPolynomial (Fin n ⊕ Fin b) GeometricField :=
  fiberMap (projector (pencilPolynomial M) rows cols)

@[simp] theorem eval_chartMap
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
    (rows : Fin r → Fin a) (cols : Fin r → Fin b) (p : PairPoint n b) :
    polynomialMap (chartMap M rows cols) p =
      pairPoint (pairLeft p) ((projector (M (pairLeft p)) rows cols).mulVec (pairRight p)) := by
  simp only [chartMap, eval_fiberMap, projector_map, eval_pencil]

/-- The polynomial projector parametrizes the entire fiber, not just a
selected subspace, on its actual nonzero-minor chart. -/
theorem chart_image
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
    (rows : Fin r → Fin a) (cols : Fin r → Fin b)
    (V : Set (GeometricPoint n))
    (hdet : ∀ x ∈ V, eval x (minorPolynomial M rows cols) ≠ 0)
    (hrank : ∀ x ∈ V, (M x).rank ≤ r) :
    polynomialMap (chartMap M rows cols) '' affineProduct V = kernelBundle M V := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    rw [eval_chartMap]
    refine ⟨hq,?_⟩
    exact projector_mem_ker _ _ _ (by simpa using hdet _ hq) (hrank _ hq) _
  · intro hp
    have hrange := range_projector (M (pairLeft p)) rows cols
      (by simpa using hdet _ hp.1) (hrank _ hp.1)
    have hmem : pairRight p ∈ LinearMap.range (projector (M (pairLeft p)) rows cols).mulVecLin :=
      hrange.symm ▸ hp.2
    obtain ⟨v,hv⟩ := hmem
    refine ⟨pairPoint (pairLeft p) v,hp.1,?_⟩
    rw [eval_chartMap, pairLeft_pairPoint, pairRight_pairPoint]
    exact congrArg (pairPoint (pairLeft p)) hv |>.trans (pairPoint_projections p)

def minorOpen (O : Set (GeometricPoint n)) (q : GeometricPolynomial n) :
    Set (GeometricPoint n) := {x | x ∈ O ∧ eval x q ≠ 0}

theorem minorOpen_isOpen {U O : Set (GeometricPoint n)}
    (hO : RelativelyOpenSet U O) (q : GeometricPolynomial n) :
    RelativelyOpenSet U (minorOpen O q) := by
  obtain ⟨C,hC,rfl⟩ := hO
  refine ⟨C ∪ zeroLocus GeometricField (Ideal.span {q}),
    hC.union (algebraicallyClosedSet_zeroLocus _),?_⟩
  ext x
  simp [minorOpen,zeroLocus_span,Set.mem_diff,Set.mem_union, and_assoc]
  tauto

theorem open_subset {U O : Set (GeometricPoint n)}
    (hO : RelativelyOpenSet U O) : O ⊆ U := by
  obtain ⟨C,hC,rfl⟩ := hO
  exact Set.diff_subset

/-- Every chart has the same image closure as the full bundle. The proof
uses actual common dense base opens and polynomial continuity. -/
theorem kernel_closure_eq_chart
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
    (U O : Set (GeometricPoint n)) (hU : AlgebraicallyClosedSet U)
    (hi : GeometricallyIrreducible U) (hO : RelativelyOpenSet U O)
    (rows : Fin r → Fin a) (cols : Fin r → Fin b)
    (hrank : ∀ x ∈ O, (M x).rank = r)
    (hne : (minorOpen O (minorPolynomial M rows cols)).Nonempty) :
    geometricClosure (kernelBundle M O) =
      geometricClosure (polynomialMap (chartMap M rows cols) '' affineProduct U) := by
  let V := minorOpen O (minorPolynomial M rows cols)
  have hVO : V ⊆ O := fun _ hx => hx.1
  have hVU := hVO.trans (open_subset hO)
  have hoV : RelativelyOpenSet U V := minorOpen_isOpen hO _
  have hdV : geometricClosure V = U := hoV.dense_of_nonempty hU hi hne
  have hVimage : polynomialMap (chartMap M rows cols) '' affineProduct V = kernelBundle M V :=
    chart_image M rows cols V (fun _ hx => hx.2) (fun x hx => (hrank x hx.1).le)
  have hclosureV : geometricClosure (kernelBundle M V) =
      geometricClosure (polynomialMap (chartMap M rows cols) '' affineProduct U) := by
    rw [← hVimage, ← geometricClosure_polynomialMap_image_closure,
      closure_affineProduct,hdV]
  apply le_antisymm
  · rw [← hclosureV]
    apply geometricClosure_subset_closed _ (algebraicallyClosedSet_geometricClosure _)
    intro p hp
    let x := pairLeft p
    obtain ⟨rs,cs,hminor⟩ := MatrixRankMinors.exists_rank_minor (M x)
    let W := minorOpen O (minorPolynomial M rs cs)
    have hW : RelativelyOpenSet U W := minorOpen_isOpen hO _
    have hxW : x ∈ W := ⟨hp.1,by simpa using hminor⟩
    have hWimage : polynomialMap (chartMap M rs cs) '' affineProduct W = kernelBundle M W :=
      chart_image M rs cs W (fun _ hx => hx.2) (by
        intro y hy
        rw [hrank y hy.1,hrank x hp.1])
    let T := V ∩ W
    have hnT : T.Nonempty :=
      ReducedGenericImageTangent.dense_inter_open_nonempty hdV hW ⟨x,hxW⟩
    have hdT : geometricClosure T = U := (hoV.inter hW).dense_of_nonempty hU hi hnT
    have hpimage : p ∈ polynomialMap (chartMap M rs cs) '' affineProduct W := by
      rw [hWimage]
      exact ⟨hxW,hp.2⟩
    obtain ⟨z,hz,hzp⟩ := hpimage
    have hzU : z ∈ affineProduct U := open_subset hW hz
    have hzcl : z ∈ geometricClosure (affineProduct (τ := Fin b) T) := by
      rw [closure_affineProduct,hdT]
      exact hzU
    have hc := polynomialMap_image_closure_subset (chartMap M rs cs) (affineProduct T)
      (Set.mem_image_of_mem _ hzcl)
    rw [hzp] at hc
    apply geometricClosure_mono (B := kernelBundle M V) ?_ hc
    rintro _ ⟨z,hz,rfl⟩
    have hh : polynomialMap (chartMap M rs cs) z ∈ kernelBundle M W := by
      rw [← hWimage]
      exact ⟨z,hz.2,rfl⟩
    rw [eval_chartMap] at hh ⊢
    exact ⟨hz.1,hh.2⟩
  · rw [← hclosureV]
    apply geometricClosure_mono
    intro p hp
    exact ⟨hVO hp.1,hp.2⟩

/-- The entire irreducibility field of KernelBundleInput, with no external
mathematical premise. Constant nullity is used to identify chart ranks. -/
theorem kernel_bundle_closure_irreducible
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
    (U O : Set (GeometricPoint n)) (hU : AlgebraicallyClosedSet U)
    (hi : GeometricallyIrreducible U) (hO : RelativelyOpenSet U O)
    (hdense : geometricClosure O = U) (ell : ℕ)
    (hnull : ∀ x ∈ O, finrank GeometricField (LinearMap.ker (M x).mulVecLin) = ell) :
    GeometricallyIrreducible (geometricClosure (kernelBundle M O)) := by
  have hnO : O.Nonempty := by
    by_contra hn
    have he : O = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    have hu : U = ∅ := by
      rw [he] at hdense
      simpa only [geometricClosure,vanishingIdeal_empty,zeroLocus_top] using hdense.symm
    exact hi.nonempty.ne_empty hu
  obtain ⟨x,hx⟩ := hnO
  obtain ⟨rows,cols,hdet⟩ := MatrixRankMinors.exists_rank_minor (M x)
  have hrank (y) (hy : y ∈ O) : (M y).rank = (M x).rank := by
    have ha := (M y).mulVecLin.finrank_range_add_finrank_ker
    have hb := (M x).mulVecLin.finrank_range_add_finrank_ker
    change (M y).rank + _ = _ at ha
    change (M x).rank + _ = _ at hb
    rw [hnull y hy] at ha
    rw [hnull x hx] at hb
    omega
  rw [kernel_closure_eq_chart M U O hU hi hO rows cols hrank
    ⟨x,hx,by simpa using hdet⟩]
  exact (geometricallyIrreducible_closure_iff _).mpr
    ((affineProduct_irreducible U hi).polynomialMap_image _)

end HessianTheorem11.ReducedKernelBundleCharts
