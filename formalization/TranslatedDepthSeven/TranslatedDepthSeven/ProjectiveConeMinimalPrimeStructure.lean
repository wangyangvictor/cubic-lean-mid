import TranslatedDepthSeven.IsolatedVertexQuotientNodeDecomposition
import TranslatedDepthSeven.FiniteEquationMinimalComponents

/-!
# Minimal primes of a polynomial extension

The irreducible components of a cone defined by equations which do not use
the vertex coordinate are themselves cones.  This file proves the underlying
commutative-algebra statement directly: every minimal prime over `I R[X]` is
the polynomial extension of a minimal prime over `I`.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000

universe u

/-- Ring equivalences preserve the minimal-prime relation. -/
private theorem map_mem_minimalPrimes_of_ringEquiv'
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

/-- Every minimal prime over the coefficientwise polynomial extension of an
ideal is itself the extension of a minimal prime of the coefficient ideal. -/
theorem exists_minimalPrime_map_C_eq
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (P : Ideal (Polynomial R))
    (hP : P ∈ (I.map Polynomial.C).minimalPrimes) :
    ∃ Q ∈ I.minimalPrimes, P = Q.map Polynomial.C := by
  have hPprime : P.IsPrime := Ideal.minimalPrimes_isPrime hP
  letI : P.IsPrime := hPprime
  have hIcomap : I ≤ P.comap Polynomial.C := by
    rw [← Ideal.map_le_iff_le_comap]
    exact hP.1.2
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le hIcomap
  have hQprime : Q.IsPrime := Ideal.minimalPrimes_isPrime hQ
  have hQmapPrime : (Q.map Polynomial.C).IsPrime :=
    (Ideal.isPrime_map_C_iff_isPrime Q).2 hQprime
  have hImapQ : I.map Polynomial.C ≤ Q.map Polynomial.C :=
    Ideal.map_mono hQ.1.2
  have hQmapP : Q.map Polynomial.C ≤ P :=
    (Ideal.map_le_iff_le_comap).2 hQP
  have hPmapQ : P ≤ Q.map Polynomial.C :=
    hP.2 ⟨hQmapPrime, hImapQ⟩ hQmapP
  exact ⟨Q, hQ, le_antisymm hPmapQ hQmapP⟩

/-- The same component statement in the extra-coordinate multivariate
presentation used for projective cones. -/
theorem exists_minimalPrime_projectiveConeIdealExtension_eq
    {K : Type u} [Field K] {sigma : Type*} [Fintype sigma]
    (I : Ideal (MvPolynomial sigma K))
    (P : Ideal (MvPolynomial (Option sigma) K))
    (hP : P ∈ (projectiveConeIdealExtension I).minimalPrimes) :
    ∃ Q ∈ I.minimalPrimes, P = projectiveConeIdealExtension Q := by
  let e := MvPolynomial.optionEquivLeft K sigma
  have hmapped : P.map e ∈
      ((projectiveConeIdealExtension I).map e).minimalPrimes := by
    exact map_mem_minimalPrimes_of_ringEquiv' e.toRingEquiv hP
  rw [map_projectiveConeIdealExtension_optionEquivLeft I] at hmapped
  obtain ⟨Q, hQ, hPQ⟩ := exists_minimalPrime_map_C_eq I (P.map e) hmapped
  refine ⟨Q, hQ, ?_⟩
  apply e.toRingEquiv.idealComapOrderIso.symm.injective
  change P.map e = (projectiveConeIdealExtension Q).map e
  rw [map_projectiveConeIdealExtension_optionEquivLeft Q, hPQ]

/-- Every irreducible component of a homogeneous coordinate cone contains
the coordinate vertex. -/
theorem minimalPrime_projectiveConeIdealExtension_le_vertexAxis_eval
    {K : Type u} [Field K] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin N) K))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin N) K))
    (P : Ideal (MvPolynomial (Option (Fin N)) K))
    (hP : P ∈ (projectiveConeIdealExtension I).minimalPrimes)
    (r : K) :
    P ≤ RingHom.ker
      (MvPolynomial.eval (fun j : Option (Fin N) ↦ j.elim r (fun _ ↦ 0))) := by
  obtain ⟨Q, hQ, rfl⟩ :=
    exists_minimalPrime_projectiveConeIdealExtension_eq I P hP
  have hQprime : Q.IsPrime := Ideal.minimalPrimes_isPrime hQ
  have hQhomogeneous : Q.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin N) K) := by
    exact isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous hI hQ
  exact projectiveConeIdealExtension_le_vertexAxis_eval
    Q hQprime hQhomogeneous r

@[simp]
theorem homogeneousAffinePolynomialChangeAlgEquiv_symm_X_none
    {K : Type u} [Field K] {sigma : Type*}
    (b : sigma → K) (m : K) (hm : m ≠ 0) :
    (homogeneousAffinePolynomialChangeAlgEquiv b m hm).symm
        (MvPolynomial.X none) = MvPolynomial.X none := by
  apply (homogeneousAffinePolynomialChangeAlgEquiv b m hm).injective
  simp

@[simp]
theorem homogeneousAffinePolynomialChangeAlgEquiv_symm_C
    {K : Type u} [Field K] {sigma : Type*}
    (b : sigma → K) (m : K) (hm : m ≠ 0) (a : K) :
    (homogeneousAffinePolynomialChangeAlgEquiv b m hm).symm
        (MvPolynomial.C a) = MvPolynomial.C a :=
  (homogeneousAffinePolynomialChangeAlgEquiv b m hm).symm.commutes a

@[simp]
theorem homogeneousAffinePolynomialChangeAlgEquiv_symm_X_some
    {K : Type u} [Field K] {sigma : Type*}
    (b : sigma → K) (m : K) (hm : m ≠ 0) (j : sigma) :
    (homogeneousAffinePolynomialChangeAlgEquiv b m hm).symm
        (MvPolynomial.X (some j)) =
      MvPolynomial.C m⁻¹ *
        (MvPolynomial.X (some j) -
          MvPolynomial.C (b j) * MvPolynomial.X none) := by
  apply (homogeneousAffinePolynomialChangeAlgEquiv b m hm).injective
  simp only [AlgEquiv.apply_symm_apply, map_mul, map_sub,
    homogeneousAffinePolynomialChangeAlgEquiv_C,
    homogeneousAffinePolynomialChangeAlgEquiv_X_some,
    homogeneousAffinePolynomialChangeAlgEquiv_X_none]
  ring_nf
  rw [← MvPolynomial.C_mul, inv_mul_cancel₀ hm,
    MvPolynomial.C_1, one_mul]

/-- A matrix row as a linear polynomial, with an arbitrary finite column
index. -/
def indexedMatrixRowLinearPolynomial
    {K : Type u} [Field K] {c : ℕ} {sigma : Type*} [Fintype sigma]
    (A : Matrix (Fin c) sigma K) (i : Fin c) : MvPolynomial sigma K :=
  ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j

/-- The ideal generated by the rows of a matrix with an arbitrary finite
column index. -/
def indexedMatrixRowLinearIdeal
    {K : Type u} [Field K] {c : ℕ} {sigma : Type*} [Fintype sigma]
    (A : Matrix (Fin c) sigma K) : Ideal (MvPolynomial sigma K) :=
  Ideal.span (Set.range (indexedMatrixRowLinearPolynomial A))

theorem indexedMatrixRowLinearPolynomial_isHomogeneous
    {K : Type u} [Field K] {c : ℕ} {sigma : Type*} [Fintype sigma]
    (A : Matrix (Fin c) sigma K) (i : Fin c) :
    (indexedMatrixRowLinearPolynomial A i).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum Finset.univ _ 1
  intro j _hj
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

theorem indexedMatrixRowLinearIdeal_isHomogeneous
    {K : Type u} [Field K] {c : ℕ} {sigma : Type*} [Fintype sigma]
    (A : Matrix (Fin c) sigma K) :
    (indexedMatrixRowLinearIdeal A).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule sigma K) := by
  apply Ideal.homogeneous_span
  rintro f ⟨i, rfl⟩
  exact ⟨1, indexedMatrixRowLinearPolynomial_isHomogeneous A i⟩

/-- Spatial row coefficients after sending the translated vertex `(m,-b)`
to the coordinate vertex. -/
def vertexContainedBaseMatrix
    {K : Type u} [Field K] {c N : ℕ}
    (b : Fin N → K) (m : K)
    (A : Matrix (Fin c) (Option (Fin N)) K) : Matrix (Fin c) (Fin N) K :=
  fun i j ↦ m⁻¹ * A i (some j)

/-- A linear row which vanishes at `(m,-b)` becomes a row in the spatial
variables alone under the inverse homogeneous affine change. -/
theorem homogeneousAffinePolynomialChange_symm_matrixRow_of_vertex_zero
    {K : Type u} [Field K] {c N : ℕ}
    (b : Fin N → K) (m : K) (hm : m ≠ 0)
    (A : Matrix (Fin c) (Option (Fin N)) K)
    (hvertex : Matrix.mulVec A (fun j ↦ j.elim m (fun i ↦ -b i)) = 0)
    (i : Fin c) :
    (homogeneousAffinePolynomialChangeAlgEquiv b m hm).symm
        (indexedMatrixRowLinearPolynomial A i) =
      MvPolynomial.rename some
        (indexedMatrixRowLinearPolynomial
          (vertexContainedBaseMatrix b m A) i) := by
  have hi := congrFun hvertex i
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_option,
    Pi.zero_apply, Option.elim_none, Option.elim_some, mul_neg] at hi
  have him : A i none = m⁻¹ * ∑ x, A i (some x) * b x := by
    have hi' : A i none * m = ∑ x, A i (some x) * b x := by
      rw [Finset.sum_neg_distrib] at hi
      linear_combination hi
    calc
      A i none = m⁻¹ * (A i none * m) := by field_simp
      _ = m⁻¹ * ∑ x, A i (some x) * b x := by rw [hi']
  have hC : (MvPolynomial.C (A i none) :
        MvPolynomial (Option (Fin N)) K) =
      ∑ x, (MvPolynomial.C (m⁻¹ * A i (some x) * b x) :
        MvPolynomial (Option (Fin N)) K) := by
    rw [him, map_mul, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    rw [map_mul, map_mul]
    simp only [← MvPolynomial.C_mul]
    congr 1
    ring
  unfold indexedMatrixRowLinearPolynomial vertexContainedBaseMatrix
  rw [Fintype.sum_option]
  simp only [map_add, map_mul, map_sum,
    homogeneousAffinePolynomialChangeAlgEquiv_symm_C,
    homogeneousAffinePolynomialChangeAlgEquiv_symm_X_none,
    homogeneousAffinePolynomialChangeAlgEquiv_symm_X_some,
    map_neg, map_C, MvPolynomial.rename_C, MvPolynomial.rename_X]
  simp only [← MvPolynomial.C_mul]
  calc
    MvPolynomial.C (A i none) * MvPolynomial.X none +
        ∑ x, MvPolynomial.C (A i (some x)) *
          (MvPolynomial.C m⁻¹ *
            (MvPolynomial.X (some x) -
              MvPolynomial.C (b x) * MvPolynomial.X none)) =
      MvPolynomial.C (A i none) * MvPolynomial.X none +
        ∑ x, (MvPolynomial.C (m⁻¹ * A i (some x)) *
          MvPolynomial.X (some x) -
          MvPolynomial.C (m⁻¹ * A i (some x) * b x) *
            MvPolynomial.X none) := by
        congr 1
        apply Finset.sum_congr rfl
        intro x _hx
        have h₁ : MvPolynomial.C (A i (some x)) * MvPolynomial.C m⁻¹ =
            (MvPolynomial.C (m⁻¹ * A i (some x)) :
              MvPolynomial (Option (Fin N)) K) := by
          rw [← MvPolynomial.C_mul]
          congr 1
          ring
        have h₂ : MvPolynomial.C (m⁻¹ * A i (some x)) *
              MvPolynomial.C (b x) =
            (MvPolynomial.C (m⁻¹ * A i (some x) * b x) :
              MvPolynomial (Option (Fin N)) K) := by
          rw [← MvPolynomial.C_mul]
        rw [mul_sub]
        ring_nf
        rw [h₁, h₂]
        ring
    _ = (∑ x, MvPolynomial.C (m⁻¹ * A i (some x)) *
          MvPolynomial.X (some x)) +
        (MvPolynomial.C (A i none) -
          ∑ x, MvPolynomial.C (m⁻¹ * A i (some x) * b x)) *
            MvPolynomial.X none := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
        ring
    _ = ∑ x, MvPolynomial.C (m⁻¹ * A i (some x)) *
          MvPolynomial.X (some x) := by rw [hC]; ring

/-- The whole row ideal becomes the polynomial extension of its spatial
row ideal after the vertex is sent to the coordinate vertex. -/
theorem map_vertexContained_rowIdeal_eq_projectiveConeIdealExtension
    {K : Type u} [Field K] {c N : ℕ}
    (b : Fin N → K) (m : K) (hm : m ≠ 0)
    (A : Matrix (Fin c) (Option (Fin N)) K)
    (hvertex : Matrix.mulVec A (fun j ↦ j.elim m (fun i ↦ -b i)) = 0) :
    (indexedMatrixRowLinearIdeal A).map
        (homogeneousAffinePolynomialChangeAlgEquiv b m hm).symm =
      projectiveConeIdealExtension
        (indexedMatrixRowLinearIdeal (vertexContainedBaseMatrix b m A)) := by
  unfold indexedMatrixRowLinearIdeal projectiveConeIdealExtension
  rw [Ideal.map_span, Ideal.map_span]
  apply congrArg Ideal.span
  ext f
  constructor
  · rintro ⟨g, ⟨i, rfl⟩, rfl⟩
    exact ⟨indexedMatrixRowLinearPolynomial
        (vertexContainedBaseMatrix b m A) i,
      ⟨i, rfl⟩,
      homogeneousAffinePolynomialChange_symm_matrixRow_of_vertex_zero
        b m hm A hvertex i |>.symm⟩
  · rintro ⟨g, ⟨i, rfl⟩, rfl⟩
    refine ⟨indexedMatrixRowLinearPolynomial A i, ⟨i, rfl⟩, ?_⟩
    exact homogeneousAffinePolynomialChange_symm_matrixRow_of_vertex_zero
      b m hm A hvertex i

/-- After sending the translated vertex to the coordinate vertex, the
literal cone-plus-row section is again a coordinate cone, now over the base
section by the spatial rows. -/
theorem map_translatedCone_sup_vertexContainedRows_eq_projectiveCone
    {K : Type u} [Field K] {c N : ℕ}
    (I : Ideal (MvPolynomial (Fin N) K))
    (b : Fin N → K) (m : K) (hm : m ≠ 0)
    (A : Matrix (Fin c) (Option (Fin N)) K)
    (hvertex : Matrix.mulVec A (fun j ↦ j.elim m (fun i ↦ -b i)) = 0) :
    (translatedProjectiveConeIdeal b m hm I ⊔
        indexedMatrixRowLinearIdeal A).map
        (homogeneousAffinePolynomialChangeAlgEquiv b m hm).symm =
      projectiveConeIdealExtension
        (I ⊔ indexedMatrixRowLinearIdeal
          (vertexContainedBaseMatrix b m A)) := by
  let T := homogeneousAffinePolynomialChangeAlgEquiv b m hm
  rw [Ideal.map_sup]
  unfold translatedProjectiveConeIdeal
  have hcone : ((projectiveConeIdealExtension I).map T).map T.symm =
      projectiveConeIdealExtension I := Ideal.map_of_equiv T.toRingEquiv
  change ((projectiveConeIdealExtension I).map T).map T.symm ⊔
      (indexedMatrixRowLinearIdeal A).map T.symm = _
  rw [hcone]
  rw [map_vertexContained_rowIdeal_eq_projectiveConeIdealExtension
    b m hm A hvertex]
  unfold projectiveConeIdealExtension
  rw [Ideal.map_sup]

/-- Every actual irreducible component of a vertex-contained translated
cone section is itself the translated cone over an actual minimal component
of the spatial base section. -/
theorem exists_minimalPrime_translatedCone_sup_vertexContainedRows_eq
    {K : Type u} [Field K] {c N : ℕ}
    (I : Ideal (MvPolynomial (Fin N) K))
    (b : Fin N → K) (m : K) (hm : m ≠ 0)
    (A : Matrix (Fin c) (Option (Fin N)) K)
    (hvertex : Matrix.mulVec A (fun j ↦ j.elim m (fun i ↦ -b i)) = 0)
    (P : Ideal (MvPolynomial (Option (Fin N)) K))
    (hP : P ∈ (translatedProjectiveConeIdeal b m hm I ⊔
      indexedMatrixRowLinearIdeal A).minimalPrimes) :
    ∃ Q ∈ (I ⊔ indexedMatrixRowLinearIdeal
        (vertexContainedBaseMatrix b m A)).minimalPrimes,
      P = translatedProjectiveConeIdeal b m hm Q := by
  let T := homogeneousAffinePolynomialChangeAlgEquiv b m hm
  have hPmap : P.map T.symm ∈
      ((translatedProjectiveConeIdeal b m hm I ⊔
        indexedMatrixRowLinearIdeal A).map T.symm).minimalPrimes :=
    map_mem_minimalPrimes_of_ringEquiv' T.symm.toRingEquiv hP
  rw [map_translatedCone_sup_vertexContainedRows_eq_projectiveCone
    I b m hm A hvertex] at hPmap
  obtain ⟨Q, hQ, hPQ⟩ :=
    exists_minimalPrime_projectiveConeIdealExtension_eq
      (I ⊔ indexedMatrixRowLinearIdeal
        (vertexContainedBaseMatrix b m A)) (P.map T.symm) hPmap
  refine ⟨Q, hQ, ?_⟩
  change P = (projectiveConeIdealExtension Q).map T
  have hback := congrArg (fun L : Ideal (MvPolynomial (Option (Fin N)) K) ↦
    L.map T) hPQ
  change (P.map T.symm).map T = (projectiveConeIdealExtension Q).map T at hback
  have hleft : (P.map T.symm).map T = P :=
    Ideal.map_of_equiv T.symm.toRingEquiv
  rw [hleft] at hback
  exact hback

/-! ## Consecutive-coordinate specialization -/

/-- Reindex the columns `Fin (N+1)` as `Option (Fin N)`, with the first
coordinate becoming `none`. -/
def finSuccReindexedMatrix
    {K : Type u} [Field K] {c N : ℕ}
    (A : Matrix (Fin c) (Fin (N + 1)) K) :
    Matrix (Fin c) (Option (Fin N)) K :=
  A.submatrix id (_root_.finSuccEquiv N).symm

theorem renameEquiv_matrixRowLinearPolynomial_finSucc
    {K : Type u} [Field K] {c N : ℕ}
    (A : Matrix (Fin c) (Fin (N + 1)) K) (i : Fin c) :
    MvPolynomial.renameEquiv K (_root_.finSuccEquiv N)
        (matrixRowLinearPolynomial A i) =
      indexedMatrixRowLinearPolynomial (finSuccReindexedMatrix A) i := by
  unfold matrixRowLinearPolynomial indexedMatrixRowLinearPolynomial
    finSuccReindexedMatrix
  simp only [map_sum, map_mul, MvPolynomial.renameEquiv_apply,
    MvPolynomial.rename_C, MvPolynomial.rename_X, Matrix.submatrix_apply,
    id_eq]
  rw [← (_root_.finSuccEquiv N).sum_comp]
  simp

theorem map_matrixRowLinearIdeal_renameEquiv_finSucc
    {K : Type u} [Field K] {c N : ℕ}
    (A : Matrix (Fin c) (Fin (N + 1)) K) :
    (matrixRowLinearIdeal A).map
        (MvPolynomial.renameEquiv K (_root_.finSuccEquiv N)) =
      indexedMatrixRowLinearIdeal (finSuccReindexedMatrix A) := by
  unfold matrixRowLinearIdeal indexedMatrixRowLinearIdeal
  rw [Ideal.map_span]
  apply congrArg Ideal.span
  ext f
  constructor
  · rintro ⟨g, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (renameEquiv_matrixRowLinearPolynomial_finSucc A i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨matrixRowLinearPolynomial A i, ⟨i, rfl⟩,
      renameEquiv_matrixRowLinearPolynomial_finSucc A i⟩

theorem map_isolatedVertexTranslatedConeFinIdeal_renameEquiv_finSucc
    {K : Type u} [Field K]
    (I : Ideal (MvPolynomial (Fin 12) K))
    (b : Fin 12 → K) (m : K) (hm : m ≠ 0) :
    (isolatedVertexTranslatedConeFinIdeal b m hm I).map
        (MvPolynomial.renameEquiv K (_root_.finSuccEquiv 12)) =
      translatedProjectiveConeIdeal b m hm I := by
  unfold isolatedVertexTranslatedConeFinIdeal
  exact Ideal.map_of_equiv
    (MvPolynomial.renameEquiv K (_root_.finSuccEquiv 12).symm).toRingEquiv

theorem map_isolatedVertexQuotientNodeIdeal_renameEquiv_finSucc
    {K : Type u} [Field K]
    (I : Ideal (MvPolynomial (Fin 12) K))
    (b : Fin 12 → K) (m : K) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Fin 13) K) :
    (isolatedVertexQuotientNodeIdeal I b m hm A).map
        (MvPolynomial.renameEquiv K (_root_.finSuccEquiv 12)) =
      translatedProjectiveConeIdeal b m hm I ⊔
        indexedMatrixRowLinearIdeal (finSuccReindexedMatrix A) := by
  unfold isolatedVertexQuotientNodeIdeal
  rw [Ideal.map_sup,
    map_isolatedVertexTranslatedConeFinIdeal_renameEquiv_finSucc,
    map_matrixRowLinearIdeal_renameEquiv_finSucc]

theorem finSuccReindexedMatrix_mulVec_quotientVertex
    {K : Type u} [Field K]
    (A : Matrix (Fin 4) (Fin 13) K)
    (b : Fin 12 → K) (m : K) :
    Matrix.mulVec (finSuccReindexedMatrix A)
        (fun j ↦ j.elim m (fun i ↦ -b i)) =
      Matrix.mulVec A (isolatedVertexQuotientProjectiveVertexVector b m) := by
  funext i
  unfold Matrix.mulVec dotProduct finSuccReindexedMatrix
  rw [← (_root_.finSuccEquiv 12).sum_comp]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [Matrix.submatrix_apply, id_eq, Equiv.symm_apply_apply]
  congr 1
  cases j using Fin.cases with
  | zero =>
      simp [isolatedVertexQuotientProjectiveVertexVector]
  | succ j =>
      simp [isolatedVertexQuotientProjectiveVertexVector]

/-- The explicit component-level consequence needed for the radial branch:
if the displayed section plane contains the translated cone vertex, every
actual component contains that vertex.  This is proved from polynomial
extension and minimality; no component-classification premise is used. -/
theorem quotientNodeComponent_containsVertex_of_plane_contains
    (I : Ideal (MvPolynomial (Fin 12) Qbar))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 12) Qbar))
    (b : Fin 12 → Qbar) (m : Qbar) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Fin 13) Qbar)
    (hvertex : Matrix.mulVec A
      (isolatedVertexQuotientProjectiveVertexVector b m) = 0)
    (P : Ideal (MvPolynomial (Fin 13) Qbar))
    (hP : P ∈ isolatedVertexQuotientNodeComponents I b m hm A) :
    QuotientComponentContainsVertex b m P := by
  let E := MvPolynomial.renameEquiv Qbar (_root_.finSuccEquiv 12)
  let A' := finSuccReindexedMatrix A
  have hPmin : P ∈ (isolatedVertexQuotientNodeIdeal I b m hm A).minimalPrimes :=
    (mem_finiteMinimalPrimes_iff _ _).mp hP
  have hPmap : P.map E ∈
      ((isolatedVertexQuotientNodeIdeal I b m hm A).map E).minimalPrimes :=
    map_mem_minimalPrimes_of_ringEquiv' E.toRingEquiv hPmin
  have hnode : (isolatedVertexQuotientNodeIdeal I b m hm A).map E =
      translatedProjectiveConeIdeal b m hm I ⊔
        indexedMatrixRowLinearIdeal A' :=
    map_isolatedVertexQuotientNodeIdeal_renameEquiv_finSucc I b m hm A
  rw [hnode] at hPmap
  have hvertex' : Matrix.mulVec A'
      (fun j ↦ j.elim m (fun i ↦ -b i)) = 0 := by
    rw [finSuccReindexedMatrix_mulVec_quotientVertex A b m, hvertex]
  obtain ⟨Q, hQ, hPeq⟩ :=
    exists_minimalPrime_translatedCone_sup_vertexContainedRows_eq
      I b m hm A' hvertex' (P.map E) hPmap
  have hbaseHomogeneous :
      (I ⊔ indexedMatrixRowLinearIdeal
        (vertexContainedBaseMatrix b m A')).IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin 12) Qbar) :=
    hI.sup (indexedMatrixRowLinearIdeal_isHomogeneous _)
  have hQprime : Q.IsPrime := Ideal.minimalPrimes_isPrime hQ
  have hQhomogeneous : Q.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 12) Qbar) :=
    isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous
      hbaseHomogeneous hQ
  have hconeVertex : translatedProjectiveConeIdeal b m hm Q ≤
      RingHom.ker (MvPolynomial.eval
        (fun j : Option (Fin 12) ↦ j.elim m (fun i ↦ -b i))) :=
    translatedProjectiveConeIdeal_le_vertex_eval
      b m hm Q hQprime hQhomogeneous
  intro f hf
  have hfmap : E f ∈ P.map E := Ideal.mem_map_of_mem E hf
  rw [hPeq] at hfmap
  have hzero := RingHom.mem_ker.mp (hconeVertex hfmap)
  change MvPolynomial.eval
      (isolatedVertexQuotientProjectiveVertexVector b m) f = 0
  have hv : (fun j : Option (Fin 12) ↦ j.elim m (fun i ↦ -b i)) ∘
      (_root_.finSuccEquiv 12) =
      isolatedVertexQuotientProjectiveVertexVector b m := by
    funext j
    cases j using Fin.cases with
    | zero =>
        simp [isolatedVertexQuotientProjectiveVertexVector]
    | succ j =>
        simp [isolatedVertexQuotientProjectiveVertexVector]
  simpa [E, MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename,
    hv] using hzero

end

end TranslatedDepthSeven
