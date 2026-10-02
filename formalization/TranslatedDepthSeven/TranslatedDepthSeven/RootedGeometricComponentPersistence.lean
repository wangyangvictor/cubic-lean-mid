import TranslatedDepthSeven.PrimeSubsetPrefixGraph
import TranslatedDepthSeven.PointwiseRootedComponentPartition
import TranslatedDepthSeven.ProperHomogeneousHypersurfaceCertificatesFieldInternal
import TranslatedDepthSeven.ProjectiveHilbertDegreeCertificationInternal

/-!
# Geometric components persistent from a common root cut

The prime-prefix graph has the empty prefix as a common surviving root after
every point-dependent deletion.  This file identifies the labels at that
root with literal minimal primes of one fixed hypersurface cut of the source
surface.  Consequently there are at most `degree(source) * degree(root cut)`
possible nonempty persistent labels.

The final theorem also records the complementary terminal fact: if a label
persists to a displayed proper terminal cut, the same literal prime ideal is
a component of that cut and has degree at most the corresponding Bezout
mass.  No catalogue of synthetic components and no geometric axiom is used.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

local instance rootedGeometricComponentPersistence_propDecidable
    (p : Prop) : Decidable p := Classical.propDecidable p

/-- The nonempty option labels attached to the literal minimal primes of an
equation family.  This is the natural codomain for selected-component labels. -/
def finiteEquationComponentOptions
    {K σ : Type*} [Field K] [Fintype σ]
    (equations : Finset (MvPolynomial σ K)) :
    Finset (Option (Ideal (MvPolynomial σ K))) := by
  classical
  exact (finiteEquationMinimalPrimes equations).image some

@[simp]
theorem mem_finiteEquationComponentOptions_iff
    {K σ : Type*} [Field K] [Fintype σ]
    (equations : Finset (MvPolynomial σ K))
    (o : Option (Ideal (MvPolynomial σ K))) :
    o ∈ finiteEquationComponentOptions equations ↔
      ∃ Q ∈ finiteEquationMinimalPrimes equations, some Q = o := by
  classical
  simp [finiteEquationComponentOptions]

@[simp]
theorem card_finiteEquationComponentOptions
    {K σ : Type*} [Field K] [Fintype σ]
    (equations : Finset (MvPolynomial σ K)) :
    (finiteEquationComponentOptions equations).card =
      (finiteEquationMinimalPrimes equations).card := by
  classical
  exact Finset.card_image_of_injective _ (Option.some_injective _)

/-- A proper homogeneous cut of a prime surface has literal minimal-prime
curve components, total degree at most the Bezout product, and therefore at
most that many nonempty option labels. -/
theorem exists_geometricSurfaceRootComponentData
    {K : Type*} [Field K] [CharZero K]
    {N d e₀ : ℕ}
    (sourceEquations : Finset (MvPolynomial (Fin (N + 1)) K))
    (hprime : (finiteEquationIdeal sourceEquations).IsPrime)
    (hhom : (finiteEquationIdeal sourceEquations).IsHomogeneous
      (homogeneousSubmodule (Fin (N + 1)) K))
    (hdegree : HasProjectiveDimensionDegree
      (finiteEquationIdeal sourceEquations) 2 d)
    (G₀ : MvPolynomial (Fin (N + 1)) K)
    (hG₀hom : G₀.IsHomogeneous e₀)
    (hG₀not : G₀ ∉ finiteEquationIdeal sourceEquations) :
    ∃ degree : Ideal (MvPolynomial (Fin (N + 1)) K) → ℕ,
      (∀ Q ∈ finiteEquationMinimalPrimes
          (finiteEquationFamilyUnion sourceEquations {G₀}),
        Q.IsPrime ∧
        Q.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K) ∧
        finiteEquationIdeal sourceEquations ≤ Q ∧
        HasProjectiveDimensionDegree Q 1 (degree Q)) ∧
      (∑ Q ∈ finiteEquationMinimalPrimes
          (finiteEquationFamilyUnion sourceEquations {G₀}), degree Q) ≤ d * e₀ ∧
      (finiteEquationMinimalPrimes
          (finiteEquationFamilyUnion sourceEquations {G₀})).card ≤ d * e₀ ∧
      (finiteEquationComponentOptions
          (finiteEquationFamilyUnion sourceEquations {G₀})).card ≤ d * e₀ := by
  classical
  let I := finiteEquationIdeal sourceEquations
  let E₀ := finiteEquationFamilyUnion sourceEquations {G₀}
  have hid : finiteEquationIdeal E₀ = I ⊔ Ideal.span ({G₀} : Set _) := by
    rw [finiteEquationIdeal_union]
    simp only [finiteEquationIdeal, Finset.coe_singleton, I]
  obtain ⟨degree, hcomponentDegree, hmass⟩ :=
    properHomogeneousHypersurface_componentDimensionDegreeMass_over_field
      (projectiveHilbertDegreeCertification_internal K) I G₀
      hprime hhom hdegree hG₀hom hG₀not
  have hcutHom : (I ⊔ Ideal.span ({G₀} : Set _)).IsHomogeneous
      (homogeneousSubmodule (Fin (N + 1)) K) := by
    apply hhom.sup
    apply Ideal.homogeneous_span
    intro f hf
    obtain rfl := Set.mem_singleton_iff.mp hf
    exact ⟨e₀, hG₀hom⟩
  have hdata (Q) (hQ : Q ∈ finiteEquationMinimalPrimes E₀) :
      Q.IsPrime ∧
      Q.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K) ∧
      I ≤ Q ∧ HasProjectiveDimensionDegree Q 1 (degree Q) := by
    have hQ' : Q ∈ finiteMinimalPrimes (I ⊔ Ideal.span ({G₀} : Set _)) := by
      simpa only [finiteEquationMinimalPrimes, hid] using hQ
    exact ⟨isPrime_of_mem_finiteMinimalPrimes hQ',
      isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous hcutHom
        ((mem_finiteMinimalPrimes_iff _ _).mp hQ'),
      le_sup_left.trans (le_of_mem_finiteMinimalPrimes hQ'),
      hcomponentDegree Q hQ'⟩
  have hmassE : (∑ Q ∈ finiteEquationMinimalPrimes E₀, degree Q) ≤ d * e₀ := by
    simpa only [finiteEquationMinimalPrimes, hid] using hmass
  have hcard : (finiteEquationMinimalPrimes E₀).card ≤ d * e₀ := by
    calc
      (finiteEquationMinimalPrimes E₀).card =
          ∑ _Q ∈ finiteEquationMinimalPrimes E₀, 1 := by simp
      _ ≤ ∑ Q ∈ finiteEquationMinimalPrimes E₀, degree Q := by
        exact Finset.sum_le_sum fun Q hQ ↦ (hdata Q hQ).2.2.2.2.1
      _ ≤ d * e₀ := hmassE
  refine ⟨degree, hdata, hmassE, hcard, ?_⟩
  simpa only [card_finiteEquationComponentOptions] using hcard

/-- If at least `k` primes survive, the point-dependent prefix graph contains
an actual surviving vertex of full depth `k`.  Thus the terminal-cut theorem
below needs only the later arithmetic estimate that enough good primes remain. -/
theorem exists_fullDepth_survivingPrefix
    (P Q : Finset ℕ) (k : ℕ) (hQP : Q ⊆ P) (hk : k ≤ Q.card) :
    ∃ v ∈ PrimeSubsetPrefix.survivingVertices P Q k, v.1.card = k := by
  classical
  obtain ⟨s, hsQ, hscard⟩ := Finset.exists_subset_card_eq hk
  have hsP : s ⊆ P := hsQ.trans hQP
  have hsvertex : s ∈ PrimeSubsetPrefix.vertices P k :=
    PrimeSubsetPrefix.mem_vertices.mpr ⟨hsP, hscard.le⟩
  let v : PrimeSubsetPrefix.Vertex P k := ⟨s, hsvertex⟩
  refine ⟨v, ?_, hscard⟩
  simp only [PrimeSubsetPrefix.survivingVertices, Finset.mem_filter,
    Finset.mem_univ, true_and, v]
  exact hsQ

/-- Point-dependent prime deletion leaves a connected prefix graph with a
common root.  If every surviving auxiliary vanishes, the points split into
changed-edge cells and persistent cells indexed only by actual components of
the fixed root equation family. -/
theorem card_prefixPoints_le_changedEdges_add_rootPersistent
    {Point K σ : Type*} [Field K] [Fintype σ]
    [DecidableEq Point]
    (P : Finset ℕ) (k : ℕ)
    (X : Finset Point) (allowed : Point → Finset ℕ)
    (equations : Point → PrimeSubsetPrefix.Vertex P k →
      Finset (MvPolynomial σ K))
    (coordinate : Point → σ → K)
    (rootEquations : Finset (MvPolynomial σ K))
    (hallowed : ∀ x ∈ X, allowed x ⊆ P)
    (hrootEquations : ∀ x ∈ X,
      equations x (PrimeSubsetPrefix.root P k) = rootEquations)
    (hzero : ∀ x ∈ X, ∀ v ∈
      PrimeSubsetPrefix.survivingVertices P (allowed x) k,
      coordinate x ∈ finiteAffineCommonZeroLocus (equations x v)) :
    X.card ≤
      (∑ v : PrimeSubsetPrefix.Vertex P k,
        ∑ w : PrimeSubsetPrefix.Vertex P k,
        (X.filter fun x ↦
          v ∈ PrimeSubsetPrefix.survivingVertices P (allowed x) k ∧
          w ∈ PrimeSubsetPrefix.survivingVertices P (allowed x) k ∧
          (PrimeSubsetPrefix.graph P k).Adj v w ∧
          selectedFiniteEquationComponent (equations x v) (coordinate x) ≠
            selectedFiniteEquationComponent (equations x w) (coordinate x)).card) +
      (∑ o ∈ finiteEquationComponentOptions rootEquations,
        (X.filter fun x ↦
          o ≠ none ∧ ∀ v ∈
            PrimeSubsetPrefix.survivingVertices P (allowed x) k,
            selectedFiniteEquationComponent (equations x v) (coordinate x) = o).card) := by
  classical
  let vertices : Point → Finset (PrimeSubsetPrefix.Vertex P k) := fun x ↦
    PrimeSubsetPrefix.survivingVertices P (allowed x) k
  let label : Point → PrimeSubsetPrefix.Vertex P k →
      Option (Ideal (MvPolynomial σ K)) := fun x v ↦
    selectedFiniteEquationComponent (equations x v) (coordinate x)
  have hroot : ∀ x ∈ X, PrimeSubsetPrefix.root P k ∈ vertices x := by
    intro x _hx
    exact PrimeSubsetPrefix.root_mem_surviving P (allowed x) k
  have hconnected : ∀ x ∈ X,
      ((PrimeSubsetPrefix.graph P k).induce
        (↑(vertices x) : Set (PrimeSubsetPrefix.Vertex P k))).Connected := by
    intro x hx
    exact PrimeSubsetPrefix.surviving_connected P (allowed x) k (hallowed x hx)
  have hnonempty : ∀ x ∈ X, ∀ v ∈ vertices x, label x v ≠ none := by
    intro x hx v hv hnone
    exact ((selectedFiniteEquationComponent_eq_none_iff
      (equations x v) (coordinate x)).mp hnone) (hzero x hx v hv)
  have hpartition := card_le_sum_pointwiseConnected_edge_persistent_at_root
    (PrimeSubsetPrefix.graph P k) (PrimeSubsetPrefix.root P k)
    X vertices label hroot hconnected hnonempty
  have hlabelSubset : X.image (fun x ↦ label x (PrimeSubsetPrefix.root P k)) ⊆
      finiteEquationComponentOptions rootEquations := by
    intro o ho
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ho
    have hne : label x (PrimeSubsetPrefix.root P k) ≠ none :=
      hnonempty x hx (PrimeSubsetPrefix.root P k) (hroot x hx)
    obtain ⟨Q, hQ⟩ := Option.ne_none_iff_exists'.mp hne
    have hQroot : selectedFiniteEquationComponent rootEquations (coordinate x) = some Q := by
      simpa only [label, hrootEquations x hx] using hQ
    exact (mem_finiteEquationComponentOptions_iff rootEquations _).mpr
      ⟨Q, (selectedFiniteEquationComponent_spec
        rootEquations (coordinate x) hQroot).1, hQ.symm⟩
  have hpersistent :
      (∑ o ∈ X.image (fun x ↦ label x (PrimeSubsetPrefix.root P k)),
        (X.filter fun x ↦
          o ≠ none ∧ ∀ v ∈ vertices x, label x v = o).card) ≤
      (∑ o ∈ finiteEquationComponentOptions rootEquations,
        (X.filter fun x ↦
          o ≠ none ∧ ∀ v ∈ vertices x, label x v = o).card) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hlabelSubset (by intros; omega)
  exact hpartition.trans (Nat.add_le_add_left hpersistent _)

/-- Geometric specialization of the rooted prefix partition.  The same
literal root-component option set both indexes every persistent cell and has
cardinality at most the degree product of the fixed source surface and the
single modulus-one auxiliary cut. -/
theorem geometricSurface_prefix_partition_with_rootLabelBound
    {Point K : Type*} [Field K] [CharZero K]
    [DecidableEq Point]
    {N d e₀ : ℕ}
    (sourceEquations : Finset (MvPolynomial (Fin (N + 1)) K))
    (hprime : (finiteEquationIdeal sourceEquations).IsPrime)
    (hhom : (finiteEquationIdeal sourceEquations).IsHomogeneous
      (homogeneousSubmodule (Fin (N + 1)) K))
    (hdegree : HasProjectiveDimensionDegree
      (finiteEquationIdeal sourceEquations) 2 d)
    (G₀ : MvPolynomial (Fin (N + 1)) K)
    (hG₀hom : G₀.IsHomogeneous e₀)
    (hG₀not : G₀ ∉ finiteEquationIdeal sourceEquations)
    (P : Finset ℕ) (k : ℕ)
    (X : Finset Point) (allowed : Point → Finset ℕ)
    (equations : Point → PrimeSubsetPrefix.Vertex P k →
      Finset (MvPolynomial (Fin (N + 1)) K))
    (coordinate : Point → Fin (N + 1) → K)
    (hallowed : ∀ x ∈ X, allowed x ⊆ P)
    (hrootEquations : ∀ x ∈ X,
      equations x (PrimeSubsetPrefix.root P k) =
        finiteEquationFamilyUnion sourceEquations {G₀})
    (hzero : ∀ x ∈ X, ∀ v ∈
      PrimeSubsetPrefix.survivingVertices P (allowed x) k,
      coordinate x ∈ finiteAffineCommonZeroLocus (equations x v)) :
    X.card ≤
      (∑ v : PrimeSubsetPrefix.Vertex P k,
        ∑ w : PrimeSubsetPrefix.Vertex P k,
        (X.filter fun x ↦
          v ∈ PrimeSubsetPrefix.survivingVertices P (allowed x) k ∧
          w ∈ PrimeSubsetPrefix.survivingVertices P (allowed x) k ∧
          (PrimeSubsetPrefix.graph P k).Adj v w ∧
          selectedFiniteEquationComponent (equations x v) (coordinate x) ≠
            selectedFiniteEquationComponent (equations x w) (coordinate x)).card) +
      (∑ o ∈ finiteEquationComponentOptions
          (finiteEquationFamilyUnion sourceEquations {G₀}),
        (X.filter fun x ↦
          o ≠ none ∧ ∀ v ∈
            PrimeSubsetPrefix.survivingVertices P (allowed x) k,
            selectedFiniteEquationComponent (equations x v) (coordinate x) = o).card) ∧
    (finiteEquationComponentOptions
      (finiteEquationFamilyUnion sourceEquations {G₀})).card ≤ d * e₀ := by
  constructor
  · exact card_prefixPoints_le_changedEdges_add_rootPersistent
      P k X allowed equations coordinate
      (finiteEquationFamilyUnion sourceEquations {G₀})
      hallowed hrootEquations hzero
  · obtain ⟨_degree, _hdata, _hmass, _hcard, hoptions⟩ :=
      exists_geometricSurfaceRootComponentData sourceEquations
        hprime hhom hdegree G₀ hG₀hom hG₀not
    exact hoptions

/-- A persistent nonempty selected label which reaches a displayed terminal
proper cut is literally a component of that cut.  Its Hilbert degree is at
most the terminal Bezout mass `d * e`. -/
theorem persistentSelectedComponent_terminalDegree_le
    {Point Vertex K : Type*} [Field K] [CharZero K]
    {N d e : ℕ}
    (sourceEquations : Finset (MvPolynomial (Fin (N + 1)) K))
    (hprime : (finiteEquationIdeal sourceEquations).IsPrime)
    (hhom : (finiteEquationIdeal sourceEquations).IsHomogeneous
      (homogeneousSubmodule (Fin (N + 1)) K))
    (hdegree : HasProjectiveDimensionDegree
      (finiteEquationIdeal sourceEquations) 2 d)
    (equations : Point → Vertex →
      Finset (MvPolynomial (Fin (N + 1)) K))
    (coordinate : Point → Fin (N + 1) → K)
    (vertices : Point → Finset Vertex)
    (x : Point) (v : Vertex) (o : Option (Ideal (MvPolynomial (Fin (N + 1)) K)))
    (G : MvPolynomial (Fin (N + 1)) K)
    (hv : v ∈ vertices x)
    (ho : o ≠ none)
    (hpersistent : ∀ w ∈ vertices x,
      selectedFiniteEquationComponent (equations x w) (coordinate x) = o)
    (hequations : equations x v =
      finiteEquationFamilyUnion sourceEquations {G})
    (hGhom : G.IsHomogeneous e)
    (hGnot : G ∉ finiteEquationIdeal sourceEquations) :
    ∃ Q degreeQ,
      o = some Q ∧
      Q ∈ finiteEquationMinimalPrimes
        (finiteEquationFamilyUnion sourceEquations {G}) ∧
      HasProjectiveDimensionDegree Q 1 degreeQ ∧
      degreeQ ≤ d * e := by
  classical
  obtain ⟨Q, hQo⟩ := Option.ne_none_iff_exists'.mp ho
  have hselected : selectedFiniteEquationComponent
      (finiteEquationFamilyUnion sourceEquations {G}) (coordinate x) = some Q := by
    rw [← hequations]
    exact (hpersistent v hv).trans hQo
  have hQ := (selectedFiniteEquationComponent_spec _ _ hselected).1
  let I := finiteEquationIdeal sourceEquations
  have hid : finiteEquationIdeal
      (finiteEquationFamilyUnion sourceEquations {G}) =
      I ⊔ Ideal.span ({G} : Set _) := by
    rw [finiteEquationIdeal_union]
    simp only [finiteEquationIdeal, Finset.coe_singleton, I]
  obtain ⟨terminalDegree, hterminalDegree, hmass⟩ :=
    properHomogeneousHypersurface_componentDimensionDegreeMass_over_field
      (projectiveHilbertDegreeCertification_internal K) I G
      hprime hhom hdegree hGhom hGnot
  have hQ' : Q ∈ finiteMinimalPrimes (I ⊔ Ideal.span ({G} : Set _)) := by
    simpa only [finiteEquationMinimalPrimes, hid] using hQ
  refine ⟨Q, terminalDegree Q, hQo, hQ,
    hterminalDegree Q hQ', ?_⟩
  exact (Finset.single_le_sum (fun R _ ↦ Nat.zero_le (terminalDegree R)) hQ').trans hmass

end

end TranslatedDepthSeven
