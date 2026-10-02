import TranslatedDepthSeven.RankSevenPersistentPlaneVertexSpan
import TranslatedDepthSeven.ProjectiveConeMinimalPrimeStructure

/-!
# The translated-cone vertex in every source-section component

When all four cutting rows contain the translated vertex, the complete
source-section ideal becomes a polynomial extension after sending that
vertex to the extra coordinate.  Minimal primes of a polynomial extension
are extensions of minimal primes downstairs.  Hence every actual source
component contains the vertex.  This proves the previously isolated
component-incidence interface internally.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 5000000

/-- A ring equivalence between possibly differently presented polynomial
rings carries minimal primes to minimal primes. -/
theorem map_mem_minimalPrimes_of_ringEquiv_between
    {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) {I P : Ideal R}
    (hP : P ∈ I.minimalPrimes) :
    P.map e ∈ (I.map e).minimalPrimes := by
  letI : P.IsPrime := Ideal.minimalPrimes_isPrime hP
  letI : (P.map e).IsPrime := Ideal.map_isPrime_of_equiv e
  refine ⟨⟨inferInstance, Ideal.map_mono hP.1.2⟩, ?_⟩
  intro Q hQ hQP
  have hcomPrime : (Q.comap e).IsPrime := hQ.1.comap e
  have hIcom : I ≤ Q.comap e :=
    (Ideal.map_le_iff_le_comap).mp hQ.2
  have hcomP : Q.comap e ≤ P := by
    intro f hf
    have hef : e f ∈ P.map e := hQP hf
    exact (Ideal.apply_mem_of_equiv_iff).mp hef
  have hPcom : P ≤ Q.comap e := hP.2 ⟨hcomPrime, hIcom⟩ hcomP
  exact (Ideal.map_le_iff_le_comap).mpr hPcom

/-- The lifted integral equation family is exactly the extra-coordinate
extension of the rationalized family. -/
theorem projectiveConeLiftEquationFamily_eq_renameSome_rationalized
    {N : ℕ} (equations : Finset (MvPolynomial (Fin N) ℤ)) :
    projectiveConeLiftEquationFamily equations =
      renameSomeEquationFinset (rationalizedEquationFinset equations) := by
  classical
  ext g
  simp only [projectiveConeLiftEquationFamily, projectiveConeLiftEquation,
    renameSomeEquationFinset, rationalizedEquationFinset, Finset.mem_image]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨MvPolynomial.map (Int.castRingHom ℚ) f, ⟨f, hf, rfl⟩, rfl⟩
  · rintro ⟨q, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨f, hf, rfl⟩

/-- Mapping a finite family through a variable-renaming equivalence maps
its generated ideal. -/
theorem finiteEquationIdeal_image_renameEquiv
    {N : ℕ}
    (equations : Finset (MvPolynomial (Option (Fin N)) ℚ)) :
    finiteEquationIdeal
        (equations.image
          (MvPolynomial.rename (_root_.finSuccEquiv N).symm)) =
      (finiteEquationIdeal equations).map
        (MvPolynomial.renameEquiv ℚ (_root_.finSuccEquiv N).symm) := by
  classical
  unfold finiteEquationIdeal
  rw [Ideal.map_span]
  change Ideal.span
      (↑(equations.image
        (MvPolynomial.rename (_root_.finSuccEquiv N).symm)) :
          Set (MvPolynomial (Fin (N + 1)) ℚ)) = _
  rw [Finset.coe_image]
  rfl

/-- Renaming a displayed family to consecutive homogeneous coordinates and
then renaming back restores its generated ideal. -/
theorem map_finiteEquationIdeal_image_finSuccRename_back
    {N : ℕ}
    (equations : Finset (MvPolynomial (Option (Fin N)) ℚ)) :
    (finiteEquationIdeal
      (equations.image (MvPolynomial.rename (_root_.finSuccEquiv N).symm))).map
        (MvPolynomial.renameEquiv ℚ (_root_.finSuccEquiv N)) =
      finiteEquationIdeal equations := by
  calc
    (finiteEquationIdeal
        (equations.image
          (MvPolynomial.rename (_root_.finSuccEquiv N).symm))).map
          (MvPolynomial.renameEquiv ℚ (_root_.finSuccEquiv N)) =
        ((finiteEquationIdeal equations).map
          (MvPolynomial.renameEquiv ℚ (_root_.finSuccEquiv N).symm)).map
            (MvPolynomial.renameEquiv ℚ (_root_.finSuccEquiv N)) := by
      exact congrArg
        (fun J : Ideal (MvPolynomial (Fin (N + 1)) ℚ) ↦
          J.map (MvPolynomial.renameEquiv ℚ (_root_.finSuccEquiv N)))
        (finiteEquationIdeal_image_renameEquiv equations)
    _ = finiteEquationIdeal equations :=
      Ideal.map_of_equiv
        (MvPolynomial.renameEquiv ℚ
          (_root_.finSuccEquiv N).symm).toRingEquiv

/-- The finite row family and the range-generated row ideal are literally
the same ideal. -/
theorem finiteEquationIdeal_rationalMatrixRowLinearEquationFamily_eq
    {c N : ℕ} (A : Matrix (Fin c) (Fin N) ℚ) :
    finiteEquationIdeal (rationalMatrixRowLinearEquationFamily A) =
      matrixRowLinearIdeal A := by
  classical
  unfold finiteEquationIdeal rationalMatrixRowLinearEquationFamily
    matrixRowLinearIdeal
  apply congrArg Ideal.span
  ext f
  simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and,
    Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, by rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, by rfl⟩

/-- The complete source-section ideal, in the extra-coordinate indexing,
is the translated cone over the rationalized original ideal together with
the reindexed row ideal. -/
theorem map_rankSevenSourceSectionIdeal_finSuccRename
    (x₀ : IntVector 13) (m : ℕ) (hm : 0 < m)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (A : Matrix (Fin 4) (Fin 14) ℚ) :
    (rankSevenSourceSectionIdeal x₀ m hm equations A).map
        (MvPolynomial.renameEquiv ℚ (_root_.finSuccEquiv 13)) =
      translatedProjectiveConeIdeal
          (fun j ↦ (x₀ j : ℚ)) (m : ℚ) (by exact_mod_cast hm.ne')
          (finiteEquationIdeal (rationalizedEquationFinset equations)) ⊔
        indexedMatrixRowLinearIdeal (finSuccReindexedMatrix A) := by
  let b : Fin 13 → ℚ := fun j ↦ (x₀ j : ℚ)
  let hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  let coneFamily := translatedProjectiveConeLiftEquationFamily
    b (m : ℚ) hmQ equations
  rw [rankSevenSourceSectionIdeal, rankSevenSourceSectionEquationFinset,
    finiteEquationIdeal_union_rowLinearEquationFamily, Ideal.map_sup]
  have hcone :
      (finiteEquationIdeal
        (coneFamily.image
          (MvPolynomial.rename (_root_.finSuccEquiv 13).symm))).map
          (MvPolynomial.renameEquiv ℚ (_root_.finSuccEquiv 13)) =
        translatedProjectiveConeIdeal b (m : ℚ) hmQ
          (finiteEquationIdeal (rationalizedEquationFinset equations)) := by
    calc
      (finiteEquationIdeal
          (coneFamily.image
            (MvPolynomial.rename (_root_.finSuccEquiv 13).symm))).map
            (MvPolynomial.renameEquiv ℚ (_root_.finSuccEquiv 13)) =
          finiteEquationIdeal coneFamily :=
        map_finiteEquationIdeal_image_finSuccRename_back
          (N := 13) coneFamily
      _ = translatedProjectiveConeIdeal b (m : ℚ) hmQ
          (finiteEquationIdeal (rationalizedEquationFinset equations)) := by
        change finiteEquationIdeal
          (finiteFamilyHomogeneousAffineChange b (m : ℚ) hmQ
            (projectiveConeLiftEquationFamily equations)) = _
        rw [projectiveConeLiftEquationFamily_eq_renameSome_rationalized]
        exact finiteEquationIdeal_translated_renameSomeEquationFinset
          b (m : ℚ) hmQ (rationalizedEquationFinset equations)
  have hrows :
      (finiteEquationIdeal
        (rationalMatrixRowLinearEquationFamily A)).map
          (MvPolynomial.renameEquiv ℚ (_root_.finSuccEquiv 13)) =
        indexedMatrixRowLinearIdeal (finSuccReindexedMatrix A) := by
    rw [finiteEquationIdeal_rationalMatrixRowLinearEquationFamily_eq,
      map_matrixRowLinearIdeal_renameEquiv_finSucc]
  simpa only [b, hmQ, coneFamily] using congrArg₂ (· ⊔ ·) hcone hrows

/-- Reindexing the four rows preserves the exact translated-vertex
evaluation. -/
theorem finSuccReindexedMatrix_mulVec_translatedJoinVertex
    (A : Matrix (Fin 4) (Fin 14) ℚ)
    (x₀ : Fin 13 → ℚ) (m : ℚ) :
    Matrix.mulVec (finSuccReindexedMatrix A)
        (fun j : Option (Fin 13) ↦ j.elim m (fun i ↦ -x₀ i)) =
      Matrix.mulVec A (translatedJoinVertexFinVector x₀ m) := by
  funext i
  unfold Matrix.mulVec dotProduct finSuccReindexedMatrix
  rw [← (_root_.finSuccEquiv 13).sum_comp]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [Matrix.submatrix_apply, id_eq, Equiv.symm_apply_apply]
  congr 1
  cases j using Fin.cases with
  | zero => simp [translatedJoinVertexFinVector,
      translatedProjectiveConeVertexVector]
  | succ j => simp [translatedJoinVertexFinVector,
      translatedProjectiveConeVertexVector]

/-- The source-section component incidence required by the persistent-plane
argument follows from the internal polynomial-extension calculation. -/
theorem rankFourTranslatedConeVertexComponentIncidence_internal :
    StandardAG.RankFourTranslatedConeVertexComponentIncidence := by
  intro x₀ m hm equations A P hhomogeneous _hArank hP hvertex
  let b : Fin 13 → ℚ := fun j ↦ (x₀ j : ℚ)
  let hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  let E := MvPolynomial.renameEquiv ℚ (_root_.finSuccEquiv 13)
  let A' := finSuccReindexedMatrix A
  let I := finiteEquationIdeal (rationalizedEquationFinset equations)
  have hsource : (rankSevenSourceSectionIdeal x₀ m hm equations A).map E =
      translatedProjectiveConeIdeal b (m : ℚ) hmQ I ⊔
        indexedMatrixRowLinearIdeal A' := by
    exact map_rankSevenSourceSectionIdeal_finSuccRename
      x₀ m hm equations A
  have hPmin : P ∈
      (rankSevenSourceSectionIdeal x₀ m hm equations A).minimalPrimes :=
    (mem_finiteMinimalPrimes_iff _ _).mp hP
  have hPmap : P.map E ∈
      (translatedProjectiveConeIdeal b (m : ℚ) hmQ I ⊔
        indexedMatrixRowLinearIdeal A').minimalPrimes := by
    rw [← hsource]
    exact map_mem_minimalPrimes_of_ringEquiv_between E.toRingEquiv hPmin
  have hvertex' : Matrix.mulVec A'
      (fun j : Option (Fin 13) ↦ j.elim (m : ℚ) (fun i ↦ -b i)) = 0 := by
    rw [finSuccReindexedMatrix_mulVec_translatedJoinVertex A b (m : ℚ),
      hvertex]
  obtain ⟨Q, hQ, hPeq⟩ :=
    exists_minimalPrime_translatedCone_sup_vertexContainedRows_eq
      I b (m : ℚ) hmQ A' hvertex' (P.map E) hPmap
  have hIhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ) := by
    apply Ideal.homogeneous_span
    intro q hq
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨e, he⟩ := hhomogeneous f hf
    exact ⟨e, he.map (Int.castRingHom ℚ)⟩
  have hbaseHomogeneous :
      (I ⊔ indexedMatrixRowLinearIdeal
        (vertexContainedBaseMatrix b (m : ℚ) A')).IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ) :=
    hIhomogeneous.sup (indexedMatrixRowLinearIdeal_isHomogeneous _)
  have hQprime : Q.IsPrime := Ideal.minimalPrimes_isPrime hQ
  have hQhomogeneous : Q.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ) :=
    isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous
      hbaseHomogeneous hQ
  have hconeVertex : translatedProjectiveConeIdeal b (m : ℚ) hmQ Q ≤
      RingHom.ker (MvPolynomial.eval
        (fun j : Option (Fin 13) ↦
          j.elim (m : ℚ) (fun i ↦ -b i))) :=
    translatedProjectiveConeIdeal_le_vertex_eval
      b (m : ℚ) hmQ Q hQprime hQhomogeneous
  rw [mem_affineIdealZeroLocus_iff]
  intro f hf
  have hfmap : E f ∈ P.map E := Ideal.mem_map_of_mem E hf
  rw [hPeq] at hfmap
  have hzero := RingHom.mem_ker.mp (hconeVertex hfmap)
  change MvPolynomial.eval (translatedJoinVertexFinVector b (m : ℚ)) f = 0
  have hv : (fun j : Option (Fin 13) ↦
      j.elim (m : ℚ) (fun i ↦ -b i)) ∘ (_root_.finSuccEquiv 13) =
        translatedJoinVertexFinVector b (m : ℚ) := by
    funext j
    cases j using Fin.cases with
    | zero => simp [translatedJoinVertexFinVector,
        translatedProjectiveConeVertexVector]
    | succ j => simp [translatedJoinVertexFinVector,
        translatedProjectiveConeVertexVector]
  simpa [E, MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename, hv]
    using hzero

end

end TranslatedDepthSeven
