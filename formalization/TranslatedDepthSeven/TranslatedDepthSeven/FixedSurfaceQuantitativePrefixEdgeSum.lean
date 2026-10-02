import TranslatedDepthSeven.FixedSurfaceQuantitativePrefixPartition
import TranslatedDepthSeven.ComparablePrimePool

/-!
# Global sum of the quantitative prefix edge cells

The fixed-surface prefix theorem bounds each ordered pair of vertices.  This
file removes the resulting double sum.  Nonedges contribute zero, while on
an edge the least common multiple is the larger prefix modulus.  Thus its
number of prime factors is at most the prefix depth and its size is at most
the depth-th power of the largest prime in the pool.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra

local instance fixedSurfacePrefixEdgeSumPropDecidable
    (p : Prop) : Decidable p := Classical.propDecidable p

namespace PrimeSubsetPrefix

/-- Ordered adjacent pairs in the prefix graph. -/
def directedEdges (P : Finset ℕ) (depth : ℕ) :
    Finset (Vertex P depth × Vertex P depth) :=
  Finset.univ.filter fun e ↦ (graph P depth).Adj e.1 e.2

/-- The literal directed-edge count is at most the square of the vertex
count. -/
theorem card_directedEdges_le_vertex_sq (P : Finset ℕ) (depth : ℕ) :
    (directedEdges P depth).card ≤
      Fintype.card (Vertex P depth) ^ 2 := by
  calc
    (directedEdges P depth).card ≤
        (Finset.univ : Finset (Vertex P depth × Vertex P depth)).card :=
      Finset.card_filter_le _ _
    _ = Fintype.card (Vertex P depth) ^ 2 := by
      simp [pow_two]

/-- Adjoin a prime when the resulting subset is still a prefix vertex;
otherwise return the root.  The fallback is irrelevant on the insertion
records below. -/
def insertVertex (P : Finset ℕ) (depth : ℕ) (v : Vertex P depth) (p : ℕ) :
    Vertex P depth :=
  if h : insert p v.1 ∈ vertices P depth then ⟨insert p v.1, h⟩
  else root P depth

/-- All admissible one-prime insertions, before choosing an orientation. -/
def insertionRecords (P : Finset ℕ) (depth : ℕ) :
    Finset (Vertex P depth × ℕ) :=
  ((Finset.univ : Finset (Vertex P depth)).product P).filter fun vp ↦
    vp.2 ∉ vp.1.1 ∧ insert vp.2 vp.1.1 ∈ vertices P depth

theorem directedEdges_subset_orientedInsertionImages
    (P : Finset ℕ) (depth : ℕ) :
    directedEdges P depth ⊆
      (insertionRecords P depth).image
          (fun vp ↦ (vp.1, insertVertex P depth vp.1 vp.2)) ∪
        (insertionRecords P depth).image
          (fun vp ↦ (insertVertex P depth vp.1 vp.2, vp.1)) := by
  intro e he
  have hadj : (graph P depth).Adj e.1 e.2 := (Finset.mem_filter.mp he).2
  rcases hadj with hforward | hreverse
  · obtain ⟨p, hpnot, heq⟩ := hforward
    have hpP : p ∈ P := (mem_vertices.mp e.2.2).1 (by
      rw [heq]
      exact Finset.mem_insert_self _ _)
    have hinsert : insert p e.1.1 ∈ vertices P depth := by
      simpa only [heq] using e.2.2
    have hrecord : (e.1, p) ∈ insertionRecords P depth := by
      simp [insertionRecords, hpP, hpnot, hinsert]
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨(e.1, p), hrecord, ?_⟩
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp [insertVertex, hinsert, heq]
  · obtain ⟨p, hpnot, heq⟩ := hreverse
    have hpP : p ∈ P := (mem_vertices.mp e.1.2).1 (by
      rw [heq]
      exact Finset.mem_insert_self _ _)
    have hinsert : insert p e.2.1 ∈ vertices P depth := by
      simpa only [heq] using e.1.2
    have hrecord : (e.2, p) ∈ insertionRecords P depth := by
      simp [insertionRecords, hpP, hpnot, hinsert]
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨(e.2, p), hrecord, ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      simp [insertVertex, hinsert, heq]
    · rfl

/-- The number of ordered prefix edges is bounded by two orientations times
one choice of a vertex and one choice of a pool prime. -/
theorem card_directedEdges_le_two_mul_vertex_mul_pool
    (P : Finset ℕ) (depth : ℕ) :
    (directedEdges P depth).card ≤
      2 * (Fintype.card (Vertex P depth) * P.card) := by
  let R := insertionRecords P depth
  let A := R.image (fun vp ↦ (vp.1, insertVertex P depth vp.1 vp.2))
  let B := R.image (fun vp ↦ (insertVertex P depth vp.1 vp.2, vp.1))
  have hR : R.card ≤ Fintype.card (Vertex P depth) * P.card := by
    calc
      R.card ≤ ((Finset.univ : Finset (Vertex P depth)).product P).card :=
        Finset.card_filter_le _ _
      _ = Fintype.card (Vertex P depth) * P.card := by simp
  calc
    (directedEdges P depth).card ≤ (A ∪ B).card :=
      Finset.card_le_card (directedEdges_subset_orientedInsertionImages P depth)
    _ ≤ A.card + B.card := Finset.card_union_le _ _
    _ ≤ R.card + R.card :=
      Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = 2 * R.card := by omega
    _ ≤ 2 * (Fintype.card (Vertex P depth) * P.card) :=
      Nat.mul_le_mul_left 2 hR

/-- A sharper closed prefix-graph bound than the ambient vertex-square
estimate: each edge changes one of the pool primes. -/
theorem card_directedEdges_le_two_mul_two_pow_mul_card
    (P : Finset ℕ) (depth : ℕ) :
    (directedEdges P depth).card ≤ 2 * (2 ^ P.card * P.card) := by
  exact (card_directedEdges_le_two_mul_vertex_mul_pool P depth).trans
    (Nat.mul_le_mul_left 2
      (Nat.mul_le_mul_right P.card (card_vertices_le_two_pow P depth)))

/-- A closed, premise-free bound for the directed prefix graph. -/
theorem card_directedEdges_le_four_pow (P : Finset ℕ) (depth : ℕ) :
    (directedEdges P depth).card ≤ 4 ^ P.card := by
  calc
    (directedEdges P depth).card ≤
        Fintype.card (Vertex P depth) ^ 2 :=
      card_directedEdges_le_vertex_sq P depth
    _ ≤ (2 ^ P.card) ^ 2 :=
      Nat.pow_le_pow_left (card_vertices_le_two_pow P depth) 2
    _ = 4 ^ P.card := by
      rw [← pow_mul, show P.card * 2 = 2 * P.card by omega, pow_mul]
      norm_num

/-- The maximum prime in the pool, with value zero for the empty pool. -/
def primeCap (P : Finset ℕ) : ℕ := P.sup id

theorem le_primeCap {P : Finset ℕ} {p : ℕ} (hp : p ∈ P) :
    p ≤ primeCap P := by
  exact Finset.le_sup (f := id) hp

theorem primeCap_le {P : Finset ℕ} {U : ℕ}
    (hU : ∀ p ∈ P, p ≤ U) : primeCap P ≤ U := by
  exact Finset.sup_le hU

/-- A surviving subset of a comparable prime pool has the same dyadic upper
cap as the original pool. -/
theorem primeCap_le_floor_two_mul_of_subset_comparablePrimePool
    {x : ℝ} {M : ℕ}
    {hM : M ≤ (comparablePrimeCandidates x).card}
    {P : Finset ℕ} (hsub : P ⊆ comparablePrimePool x M hM) :
    primeCap P ≤ ⌊2 * x⌋₊ := by
  apply primeCap_le
  intro p hp
  exact (bounds_of_mem_comparablePrimePool (hsub hp)).2

/-- Along a prefix edge, the lcm has no more prime factors than the allowed
prefix depth. -/
theorem card_primeFactors_lcm_adjacent_le
    {P : Finset ℕ} {depth : ℕ} (hP : ∀ p ∈ P, p.Prime)
    {v w : Vertex P depth} (hvw : (graph P depth).Adj v w) :
    (Nat.lcm (modulus v) (modulus w)).primeFactors.card ≤ depth := by
  obtain ⟨p, hp, hfactor⟩ := adjacent_modulus_factor hvw
  rcases hfactor with ⟨_hw, hlcm⟩ | ⟨_hv, hlcm⟩
  · rw [hlcm, modulus, primeFactors_primeProduct]
    · exact (mem_vertices.mp w.2).2
    · intro q hq
      exact hP q ((mem_vertices.mp w.2).1 hq)
  · rw [hlcm, modulus, primeFactors_primeProduct]
    · exact (mem_vertices.mp v.2).2
    · intro q hq
      exact hP q ((mem_vertices.mp v.2).1 hq)

/-- Along a prefix edge, the lcm is the product of at most `depth` pool
primes and hence is bounded by `primeCap P ^ depth`. -/
theorem lcm_adjacent_le_primeCap_pow
    {P : Finset ℕ} {depth : ℕ} (hP : ∀ p ∈ P, p.Prime)
    {v w : Vertex P depth} (hvw : (graph P depth).Adj v w) :
    Nat.lcm (modulus v) (modulus w) ≤ primeCap P ^ depth := by
  obtain ⟨p, hp, hfactor⟩ := adjacent_modulus_factor hvw
  have hcapPos : 0 < primeCap P :=
    lt_of_lt_of_le (hP p hp).pos (le_primeCap hp)
  have boundVertex (t : Vertex P depth) :
      modulus t ≤ primeCap P ^ depth := by
    have hprod : modulus t ≤ primeCap P ^ t.1.card := by
      exact Finset.prod_le_pow_card t.1 id (primeCap P) fun q hq ↦
        le_primeCap ((mem_vertices.mp t.2).1 hq)
    exact hprod.trans
      (Nat.pow_le_pow_right hcapPos ((mem_vertices.mp t.2).2))
  rcases hfactor with ⟨_hw, hlcm⟩ | ⟨_hv, hlcm⟩
  · rw [hlcm]
    exact boundVertex w
  · rw [hlcm]
    exact boundVertex v

end PrimeSubsetPrefix

/-- A quantitative prefix cell is empty unless its two vertices are joined
by an edge. -/
theorem quantitativePrefixChangedEdgeCell_eq_empty_of_not_adjacent
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    {P : Finset ℕ} {depth : ℕ}
    (auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
        MvPolynomial (Fin 4) ℚ)
    (u : Fin 3 → ℤ) (m : ℕ) (X : Finset (Fin 3 → ℤ))
    (allowed : (Fin 3 → ℤ) → Finset ℕ)
    (v w : PrimeSubsetPrefix.Vertex P depth)
    (hvw : ¬ (PrimeSubsetPrefix.graph P depth).Adj v w) :
    quantitativePrefixChangedEdgeCell sourceEquations auxiliary
      u m X allowed v w = ∅ := by
  ext z
  simp [quantitativePrefixChangedEdgeCell, hvw]

/-- The double sum of changed-edge cardinalities is exactly the sum over
the literal directed edges of the prefix graph. -/
theorem sum_card_quantitativePrefixChangedEdgeCell_eq_directedEdges
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    {P : Finset ℕ} {depth : ℕ}
    (auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
        MvPolynomial (Fin 4) ℚ)
    (u : Fin 3 → ℤ) (m : ℕ) (X : Finset (Fin 3 → ℤ))
    (allowed : (Fin 3 → ℤ) → Finset ℕ) :
    (∑ v : PrimeSubsetPrefix.Vertex P depth,
      ∑ w : PrimeSubsetPrefix.Vertex P depth,
        (quantitativePrefixChangedEdgeCell sourceEquations auxiliary
          u m X allowed v w).card) =
      ∑ e ∈ PrimeSubsetPrefix.directedEdges P depth,
        (quantitativePrefixChangedEdgeCell sourceEquations auxiliary
          u m X allowed e.1 e.2).card := by
  classical
  have hproduct :
      (∑ v : PrimeSubsetPrefix.Vertex P depth,
        ∑ w : PrimeSubsetPrefix.Vertex P depth,
          (quantitativePrefixChangedEdgeCell sourceEquations auxiliary
            u m X allowed v w).card) =
        ∑ e ∈ ((Finset.univ :
            Finset (PrimeSubsetPrefix.Vertex P depth)).product
          (Finset.univ : Finset (PrimeSubsetPrefix.Vertex P depth))),
          (quantitativePrefixChangedEdgeCell sourceEquations auxiliary
            u m X allowed e.1 e.2).card := by
    symm
    simpa using Finset.sum_product
      (Finset.univ : Finset (PrimeSubsetPrefix.Vertex P depth))
      (Finset.univ : Finset (PrimeSubsetPrefix.Vertex P depth))
      (fun e ↦ (quantitativePrefixChangedEdgeCell sourceEquations auxiliary
        u m X allowed e.1 e.2).card)
  rw [hproduct]
  simp only [PrimeSubsetPrefix.directedEdges, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hadj : (PrimeSubsetPrefix.graph P depth).Adj e.1 e.2
  · simp [hadj]
  · simp [hadj,
      quantitativePrefixChangedEdgeCell_eq_empty_of_not_adjacent
        sourceEquations auxiliary u m X allowed e.1 e.2 hadj]

/-- The uniform natural degree obtained directly from the sharp
inverse-modulus estimate.  The root modulus one is the worst case. -/
def quantitativePrefixUniformBlockDegree
    (H B : ℕ) (η a : ℝ) : ℕ :=
  ⌈2 * (H : ℝ) ^ η * (1 + (B : ℝ) ^ a)⌉₊

theorem blockDegree_le_quantitativePrefixUniformBlockDegree
    {P : Finset ℕ} {depth H B : ℕ} {η a : ℝ}
    (hP : ∀ p ∈ P, p.Prime)
    (blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ)
    (hblock : ∀ v,
      ((blockDegree v : ℕ) : ℝ) ≤ 2 * (H : ℝ) ^ η *
        (1 + (B : ℝ) ^ a /
          (PrimeSubsetPrefix.modulus v : ℝ)))
    (v : PrimeSubsetPrefix.Vertex P depth) :
    blockDegree v ≤ quantitativePrefixUniformBlockDegree H B η a := by
  have hvP : v.1 ⊆ P := (PrimeSubsetPrefix.mem_vertices.mp v.2).1
  have hvPrime : ∀ p ∈ v.1, p.Prime := fun p hp ↦ hP p (hvP hp)
  have hqNat : 0 < PrimeSubsetPrefix.modulus v :=
    Nat.pos_of_ne_zero (primeProduct_ne_zero hvPrime)
  have hq : (1 : ℝ) ≤ (PrimeSubsetPrefix.modulus v : ℝ) := by
    exact_mod_cast hqNat
  have hBa : 0 ≤ (B : ℝ) ^ a := by positivity
  have hdiv : (B : ℝ) ^ a /
      (PrimeSubsetPrefix.modulus v : ℝ) ≤ (B : ℝ) ^ a := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hfactor :
      0 ≤ 2 * (H : ℝ) ^ η := by positivity
  have hsum : 1 + (B : ℝ) ^ a /
      (PrimeSubsetPrefix.modulus v : ℝ) ≤ 1 + (B : ℝ) ^ a := by
    linarith
  have huniformReal : ((blockDegree v : ℕ) : ℝ) ≤
      2 * (H : ℝ) ^ η * (1 + (B : ℝ) ^ a) :=
    (hblock v).trans (mul_le_mul_of_nonneg_left
      hsum hfactor)
  rw [quantitativePrefixUniformBlockDegree]
  exact_mod_cast huniformReal.trans (Nat.le_ceil _)

/-- A premise-free majorant for the geometric factor on every directed
prefix edge. -/
def quantitativePrefixEdgeMajorant
    (F : MvPolynomial (Fin 4) ℤ) (P : Finset ℕ) (depth d b H B : ℕ)
    (η a : ℝ) : ℕ :=
  (max 1 (surfaceHypersurfaceFirstChartDehomogenize F).totalDegree) ^ depth *
    (PrimeSubsetPrefix.primeCap P ^ depth) ^ 2 *
    (d * (b + quantitativePrefixUniformBlockDegree H B η a)) ^ 2

/-- Replace the intrinsic pool maximum in the edge majorant by any supplied
upper cap.  In particular, `U = floor (2*x)` applies to every surviving
subset of a comparable prime pool. -/
theorem quantitativePrefixEdgeMajorant_le_of_primeCap_le
    (F : MvPolynomial (Fin 4) ℤ) (P : Finset ℕ)
    (depth d b H B U : ℕ) (η a : ℝ)
    (hcap : PrimeSubsetPrefix.primeCap P ≤ U) :
    quantitativePrefixEdgeMajorant F P depth d b H B η a ≤
      (max 1 (surfaceHypersurfaceFirstChartDehomogenize F).totalDegree) ^ depth *
        (U ^ depth) ^ 2 *
        (d * (b + quantitativePrefixUniformBlockDegree H B η a)) ^ 2 := by
  dsimp only [quantitativePrefixEdgeMajorant]
  exact Nat.mul_le_mul
    (Nat.mul_le_mul le_rfl
      (Nat.pow_le_pow_left (Nat.pow_le_pow_left hcap depth) 2))
    le_rfl

theorem quantitativePrefixEdgeMajorant_le_comparablePrimePool
    (F : MvPolynomial (Fin 4) ℤ)
    {x : ℝ} {M : ℕ}
    {hM : M ≤ (comparablePrimeCandidates x).card}
    {P : Finset ℕ} (hsub : P ⊆ comparablePrimePool x M hM)
    (depth d b H B : ℕ) (η a : ℝ) :
    quantitativePrefixEdgeMajorant F P depth d b H B η a ≤
      (max 1 (surfaceHypersurfaceFirstChartDehomogenize F).totalDegree) ^ depth *
        (⌊2 * x⌋₊ ^ depth) ^ 2 *
        (d * (b + quantitativePrefixUniformBlockDegree H B η a)) ^ 2 :=
  quantitativePrefixEdgeMajorant_le_of_primeCap_le
    F P depth d b H B ⌊2 * x⌋₊ η a
      (PrimeSubsetPrefix.primeCap_le_floor_two_mul_of_subset_comparablePrimePool
        hsub)

/-- The exact changed-edge double sum is bounded by the literal number of
directed prefix edges times one explicit uniform cell majorant.  The only
inputs are the already supplied sharp block-degree estimates and the
already proved pointwise cell estimates. -/
theorem sum_card_quantitativePrefixChangedEdgeCell_le_directedEdges_mul
    {d b H B : ℕ} {η a : ℝ}
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    (F : MvPolynomial (Fin 4) ℤ)
    (P : Finset ℕ) (depth : ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (u : Fin 3 → ℤ) (m : ℕ) (X : Finset (Fin 3 → ℤ))
    (allowed : (Fin 3 → ℤ) → Finset ℕ)
    (blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ)
    (auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
        MvPolynomial (Fin 4) ℚ)
    (hblock : ∀ v,
      ((blockDegree v : ℕ) : ℝ) ≤ 2 * (H : ℝ) ^ η *
        (1 + (B : ℝ) ^ a /
          (PrimeSubsetPrefix.modulus v : ℝ)))
    (hcell : ∀ v w : PrimeSubsetPrefix.Vertex P depth,
      (quantitativePrefixChangedEdgeCell sourceEquations auxiliary
        u m X allowed v w).card ≤
        ((surfaceHypersurfaceFirstChartDehomogenize F).totalDegree ^
          (Nat.lcm (PrimeSubsetPrefix.modulus v)
            (PrimeSubsetPrefix.modulus w)).primeFactors.card *
          (Nat.lcm (PrimeSubsetPrefix.modulus v)
            (PrimeSubsetPrefix.modulus w)) ^ 2) *
          ((d * (b + blockDegree v)) *
            (d * (b + blockDegree w)))) :
    (∑ v : PrimeSubsetPrefix.Vertex P depth,
      ∑ w : PrimeSubsetPrefix.Vertex P depth,
        (quantitativePrefixChangedEdgeCell sourceEquations auxiliary
          u m X allowed v w).card) ≤
      (PrimeSubsetPrefix.directedEdges P depth).card *
        quantitativePrefixEdgeMajorant F P depth d b H B η a := by
  classical
  rw [sum_card_quantitativePrefixChangedEdgeCell_eq_directedEdges]
  apply (Finset.sum_le_card_nsmul
    (PrimeSubsetPrefix.directedEdges P depth)
    (fun e ↦ (quantitativePrefixChangedEdgeCell sourceEquations auxiliary
      u m X allowed e.1 e.2).card)
    (quantitativePrefixEdgeMajorant F P depth d b H B η a))
  intro e he
  have hadj : (PrimeSubsetPrefix.graph P depth).Adj e.1 e.2 :=
    (Finset.mem_filter.mp he).2
  have hpf := PrimeSubsetPrefix.card_primeFactors_lcm_adjacent_le hP hadj
  have hlcm := PrimeSubsetPrefix.lcm_adjacent_le_primeCap_pow hP hadj
  have hdegV := blockDegree_le_quantitativePrefixUniformBlockDegree
    hP blockDegree hblock e.1
  have hdegW := blockDegree_le_quantitativePrefixUniformBlockDegree
    hP blockDegree hblock e.2
  let Δ := (surfaceHypersurfaceFirstChartDehomogenize F).totalDegree
  let E := quantitativePrefixUniformBlockDegree H B η a
  have hΔ : Δ ≤ max 1 Δ := le_max_right _ _
  have hΔpos : 0 < max 1 Δ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hpow : Δ ^
      (Nat.lcm (PrimeSubsetPrefix.modulus e.1)
        (PrimeSubsetPrefix.modulus e.2)).primeFactors.card ≤
      (max 1 Δ) ^ depth := by
    calc
      Δ ^ (Nat.lcm (PrimeSubsetPrefix.modulus e.1)
          (PrimeSubsetPrefix.modulus e.2)).primeFactors.card ≤
          (max 1 Δ) ^ (Nat.lcm (PrimeSubsetPrefix.modulus e.1)
            (PrimeSubsetPrefix.modulus e.2)).primeFactors.card :=
        Nat.pow_le_pow_left hΔ _
      _ ≤ (max 1 Δ) ^ depth := Nat.pow_le_pow_right hΔpos hpf
  have hlcmSq :
      (Nat.lcm (PrimeSubsetPrefix.modulus e.1)
          (PrimeSubsetPrefix.modulus e.2)) ^ 2 ≤
        (PrimeSubsetPrefix.primeCap P ^ depth) ^ 2 :=
    Nat.pow_le_pow_left hlcm 2
  have hdegreeProduct :
      (d * (b + blockDegree e.1)) *
          (d * (b + blockDegree e.2)) ≤
        (d * (b + E)) ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul
      (Nat.mul_le_mul_left d (Nat.add_le_add_left hdegV b))
      (Nat.mul_le_mul_left d (Nat.add_le_add_left hdegW b))
  exact (hcell e.1 e.2).trans <| by
    dsimp only [quantitativePrefixEdgeMajorant]
    change (Δ ^ _ * _ * _) ≤ (max 1 Δ) ^ depth * _ * _
    exact Nat.mul_le_mul (Nat.mul_le_mul hpow hlcmSq) hdegreeProduct

/-- Direct squarefree-residual form of the global estimate.  This is the
aggregate companion to `card_quantitativePrefixChangedEdgeCell_le_squarefree`:
it has the same geometric and modular inputs and no separate pointwise-bound
premise. -/
theorem sum_card_quantitativePrefixChangedEdgeCell_le_squarefree
    {d b H B : ℕ} {η a : ℝ}
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    (hgeometricPrime : ((finiteEquationIdeal sourceEquations).map
      (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime)
    (hhom : (finiteEquationIdeal sourceEquations).IsHomogeneous
      (homogeneousSubmodule (Fin 4) ℚ))
    (hdegree : HasProjectiveDimensionDegree
      (finiteEquationIdeal sourceEquations) 2 d)
    (F : MvPolynomial (Fin 4) ℤ)
    (P : Finset ℕ) (depth : ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (m : ℕ) (hm : 0 < m) (hPm : ∀ p ∈ P, ¬ p ∣ m)
    (u : Fin 3 → ℤ) (X : Finset (Fin 3 → ℤ))
    (allowed : (Fin 3 → ℤ) → Finset ℕ)
    (blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ)
    (auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
        MvPolynomial (Fin 4) ℚ)
    (hblock : ∀ v,
      ((blockDegree v : ℕ) : ℝ) ≤ 2 * (H : ℝ) ^ η *
        (1 + (B : ℝ) ^ a /
          (PrimeSubsetPrefix.modulus v : ℝ)))
    (hauxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      ∀ ρ ∈ occupiedIntegralResidues (PrimeSubsetPrefix.modulus v) X,
        (auxiliary v ρ).IsHomogeneous (b + blockDegree v) ∧
          auxiliary v ρ ∉ finiteEquationIdeal sourceEquations)
    (hauxZero : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      ∀ z ∈ X, MvPolynomial.eval
        (fun i => (progressionHomogeneousPoint u m z i : ℚ))
          (auxiliary v (integralResidueVector z)) = 0)
    (hsource : ∀ z ∈ X,
      (fun i => (progressionHomogeneousPoint u m z i : ℚ)) ∈
        finiteAffineCommonZeroLocus sourceEquations)
    (hzero : ∀ z ∈ X,
      MvPolynomial.eval (progressionHomogeneousPoint u m z) F = 0)
    (hsmooth : ∀ z ∈ X, ∀ p ∈ P, ∃ i,
      (MvPolynomial.eval (fun j => u j + (m : ℤ) * z j)
        (MvPolynomial.pderiv i
          (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0) :
    (∑ v : PrimeSubsetPrefix.Vertex P depth,
      ∑ w : PrimeSubsetPrefix.Vertex P depth,
        (quantitativePrefixChangedEdgeCell sourceEquations auxiliary
          u m X allowed v w).card) ≤
      (PrimeSubsetPrefix.directedEdges P depth).card *
        quantitativePrefixEdgeMajorant F P depth d b H B η a := by
  apply sum_card_quantitativePrefixChangedEdgeCell_le_directedEdges_mul
    sourceEquations F P depth hP u m X allowed blockDegree auxiliary hblock
  intro v w
  exact card_quantitativePrefixChangedEdgeCell_le_squarefree
    sourceEquations hgeometricPrime hhom hdegree F P depth hP m hm hPm
      u X allowed blockDegree auxiliary hauxiliary hauxZero hsource
      hzero hsmooth v w

/-- Fully closed graph-size form of the preceding aggregate estimate.  The
factor is linear in `P.card` times the number of all subsets, rather than the
square of that number. -/
theorem sum_card_quantitativePrefixChangedEdgeCell_le_two_mul_two_pow_mul_card
    {d b H B : ℕ} {η a : ℝ}
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    (F : MvPolynomial (Fin 4) ℤ)
    (P : Finset ℕ) (depth : ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (u : Fin 3 → ℤ) (m : ℕ) (X : Finset (Fin 3 → ℤ))
    (allowed : (Fin 3 → ℤ) → Finset ℕ)
    (blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ)
    (auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
        MvPolynomial (Fin 4) ℚ)
    (hblock : ∀ v,
      ((blockDegree v : ℕ) : ℝ) ≤ 2 * (H : ℝ) ^ η *
        (1 + (B : ℝ) ^ a /
          (PrimeSubsetPrefix.modulus v : ℝ)))
    (hcell : ∀ v w : PrimeSubsetPrefix.Vertex P depth,
      (quantitativePrefixChangedEdgeCell sourceEquations auxiliary
        u m X allowed v w).card ≤
        ((surfaceHypersurfaceFirstChartDehomogenize F).totalDegree ^
          (Nat.lcm (PrimeSubsetPrefix.modulus v)
            (PrimeSubsetPrefix.modulus w)).primeFactors.card *
          (Nat.lcm (PrimeSubsetPrefix.modulus v)
            (PrimeSubsetPrefix.modulus w)) ^ 2) *
          ((d * (b + blockDegree v)) *
            (d * (b + blockDegree w)))) :
    (∑ v : PrimeSubsetPrefix.Vertex P depth,
      ∑ w : PrimeSubsetPrefix.Vertex P depth,
        (quantitativePrefixChangedEdgeCell sourceEquations auxiliary
          u m X allowed v w).card) ≤
      (2 * (2 ^ P.card * P.card)) *
        quantitativePrefixEdgeMajorant F P depth d b H B η a := by
  exact (sum_card_quantitativePrefixChangedEdgeCell_le_directedEdges_mul
    sourceEquations F P depth hP u m X allowed blockDegree auxiliary
      hblock hcell).trans
    (Nat.mul_le_mul_right _
      (PrimeSubsetPrefix.card_directedEdges_le_two_mul_two_pow_mul_card
        P depth))

/-- The fixed-surface construction with the pointwise residual estimates and
their global directed-edge sum returned together.  This is the form intended
for the fixed-surface Salberger endpoint. -/
theorem exists_fixedSurface_quantitative_prefixGeometricPartition_with_globalEdgeSum
    {d : ℕ} (hd : 0 < d)
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    (hprime : (finiteEquationIdeal sourceEquations).IsPrime)
    (hgeometricPrime : ((finiteEquationIdeal sourceEquations).map
      (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime)
    (hhom : (finiteEquationIdeal sourceEquations).IsHomogeneous
      (homogeneousSubmodule (Fin 4) ℚ))
    (hchart : MvPolynomial.X 0 ∉ finiteEquationIdeal sourceEquations)
    (hdegree : HasProjectiveDimensionDegree
      (finiteEquationIdeal sourceEquations) 2 d)
    (F : MvPolynomial (Fin 4) ℤ)
    (K : ℝ) (hK : 1 ≤ K) (Aex : ℕ)
    (η a : ℝ) (hη : 0 < η)
    (ha : Real.sqrt K / Real.sqrt (d : ℝ) < a) :
    ∃ b D A H₀ : ℕ, ∃ C : ℝ,
      1 ≤ D ∧ 2 ≤ A ∧ 2 ≤ H₀ ∧ 0 ≤ C ∧
      ∀ (P : Finset ℕ) (depth H B m Dex : ℕ)
        (u : Fin 3 → ℤ) (X : Finset (Fin 3 → ℤ))
        (allowed : (Fin 3 → ℤ) → Finset ℕ) (z₀ : Fin 3 → ℤ),
      (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, ¬ p ∣ m) →
      H₀ ≤ H → 1 ≤ B →
      0 < Dex → Dex ≤ H ^ Aex → m * primeProduct P ∣ Dex →
      m ≠ 0 →
      z₀ ∈ X →
      (∀ z ∈ X, allowed z ⊆ P) →
      (∀ p, p.Prime → ¬ p ∣ Dex →
        (Nat.card (SurfaceReductionZeroPoint p
          (surfaceHypersurfaceFirstChartDehomogenize F)) : ℝ) ≤
            K * (p : ℝ) ^ 2) →
      (∀ z ∈ X, ∀ i,
        (progressionHomogeneousPoint u m z i).natAbs ≤ H) →
      (∀ z ∈ X, ∀ i, (z i).natAbs ≤ B) →
      (∀ z ∈ X,
        MvPolynomial.eval (progressionHomogeneousPoint u m z) F = 0) →
      (∀ z ∈ X, ∃ v, MvPolynomial.eval
        (fun i => u i + (m : ℤ) * z i)
        (MvPolynomial.pderiv v
          (surfaceHypersurfaceFirstChartDehomogenize F)) ≠ 0) →
      (∀ z ∈ X, ∀ p ∈ P, ∃ v,
        (MvPolynomial.eval (fun i => u i + (m : ℤ) * z i)
          (MvPolynomial.pderiv v
            (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0) →
      (∀ z ∈ X,
        (fun i => (progressionHomogeneousPoint u m z i : ℚ)) ∈
          finiteAffineCommonZeroLocus sourceEquations) →
      ∃ blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ,
        ∃ auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
          (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
            MvPolynomial (Fin 4) ℚ,
        (∀ v : PrimeSubsetPrefix.Vertex P depth,
          0 < blockDegree v ∧
          ((blockDegree v : ℕ) : ℝ) ≤ 2 * (H : ℝ) ^ η *
            (1 + (B : ℝ) ^ a /
              (PrimeSubsetPrefix.modulus v : ℝ)) ∧
          (∀ ρ ∈ occupiedIntegralResidues
              (PrimeSubsetPrefix.modulus v) X,
            (auxiliary v ρ).IsHomogeneous (b + blockDegree v) ∧
              auxiliary v ρ ∉ finiteEquationIdeal sourceEquations) ∧
          ∀ z ∈ X, MvPolynomial.eval
            (fun i => (progressionHomogeneousPoint u m z i : ℚ))
              (auxiliary v (integralResidueVector z)) = 0) ∧
        (let root := PrimeSubsetPrefix.root P depth
         let G₀ := MvPolynomial.map (algebraMap ℚ Qbar)
           (auxiliary root (integralResidueVector z₀))
         X.card ≤
            (∑ v : PrimeSubsetPrefix.Vertex P depth,
              ∑ w : PrimeSubsetPrefix.Vertex P depth,
                (quantitativePrefixChangedEdgeCell sourceEquations auxiliary
                  u m X allowed v w).card) +
            (∑ o ∈ finiteEquationComponentOptions
                (finiteEquationFamilyUnion
                  (qbarSurfaceEquationFamily sourceEquations) {G₀}),
              (X.filter fun z =>
                o ≠ none ∧ ∀ v ∈
                  PrimeSubsetPrefix.survivingVertices P (allowed z) depth,
                  selectedFiniteEquationComponent
                      (quantitativePrefixCutEquations
                        sourceEquations auxiliary z v)
                      (quantitativePrefixCoordinate u m z) = o).card) ∧
          (finiteEquationComponentOptions
            (finiteEquationFamilyUnion
              (qbarSurfaceEquationFamily sourceEquations) {G₀})).card ≤
            d * (b + blockDegree root)) ∧
        (∀ v w : PrimeSubsetPrefix.Vertex P depth,
          (quantitativePrefixChangedEdgeCell sourceEquations auxiliary
            u m X allowed v w).card ≤
            ((surfaceHypersurfaceFirstChartDehomogenize F).totalDegree ^
              (Nat.lcm (PrimeSubsetPrefix.modulus v)
                (PrimeSubsetPrefix.modulus w)).primeFactors.card *
              (Nat.lcm (PrimeSubsetPrefix.modulus v)
                (PrimeSubsetPrefix.modulus w)) ^ 2) *
              ((d * (b + blockDegree v)) *
                (d * (b + blockDegree w)))) ∧
        (∑ v : PrimeSubsetPrefix.Vertex P depth,
          ∑ w : PrimeSubsetPrefix.Vertex P depth,
            (quantitativePrefixChangedEdgeCell sourceEquations auxiliary
              u m X allowed v w).card) ≤
          (PrimeSubsetPrefix.directedEdges P depth).card *
            quantitativePrefixEdgeMajorant
              F P depth d b H B η a := by
  obtain ⟨b, D, A, H₀, C, hD, hA, hH₀, hC, hmain⟩ :=
    exists_fixedSurface_quantitative_prefixGeometricPartition
      hd sourceEquations hprime hgeometricPrime hhom hchart hdegree
        F K hK Aex η a hη ha
  refine ⟨b, D, A, H₀, C, hD, hA, hH₀, hC, ?_⟩
  intro P depth H B m Dex u X allowed z₀ hP hPm hH hB hDex
    hDexHeight hmPDex hm hz₀ hallowed hpoints hheight hbox hzero
    hgradient hsmooth hsource
  obtain ⟨blockDegree, auxiliary, hauxiliary, hpartition, hcell⟩ :=
    hmain P depth H B m Dex u X allowed z₀ hP hPm hH hB hDex
      hDexHeight hmPDex hm hz₀ hallowed hpoints hheight hbox hzero
      hgradient hsmooth hsource
  refine ⟨blockDegree, auxiliary, hauxiliary, hpartition, hcell, ?_⟩
  exact sum_card_quantitativePrefixChangedEdgeCell_le_directedEdges_mul
    sourceEquations F P depth hP u m X allowed blockDegree auxiliary
      (fun v ↦ (hauxiliary v).2.1) hcell

end

end TranslatedDepthSeven
