import HessianTheorem11.CliffordDivisibility
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Normalizing the actual symmetric Schur relations to Clifford generators.
Orthogonal frames are constructed by diagonalization and square roots; no
existence of Clifford operators is taken as an external input. -/

noncomputable section
namespace HessianTheorem11.CliffordNormalization
open Module

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem toBilin'_isSymm {m : ℕ} (P : Matrix (Fin m) (Fin m) K)
    (hP : P.IsSymm) : (Matrix.toBilin' P).IsSymm := by
  constructor
  intro x y
  simp only [Matrix.toBilin'_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hP.apply]
  ring

/-- A symmetric form of rank at least `k` over an algebraically closed field
has an actual frame with Gram matrix `−1`. Degenerate directions are discarded
by counting the nonzero diagonal entries of an orthogonal basis. -/
theorem exists_negative_orthonormal_frame [IsAlgClosed K]
    {m k : ℕ} (P : Matrix (Fin m) (Fin m) K) (hP : P.IsSymm)
    (hk : k ≤ P.rank) :
    ∃ v : Fin k → (Fin m → K), ∀ i j,
      Matrix.toBilin' P (v i) (v j) = if i = j then -1 else 0 := by
  classical
  letI : Invertible (2 : K) := invertibleOfNonzero (by norm_num)
  let β := Matrix.toBilin' P
  obtain ⟨b, hb⟩ : ∃ b : Basis (Fin m) K (Fin m → K), β.IsOrthoᵢ b := by
    have hex := LinearMap.BilinForm.exists_orthogonal_basis (B := β)
      (LinearMap.BilinForm.isSymm_iff.mp (toBilin'_isSymm P hP))
    have hn : finrank K (Fin m → K) = m := by
      rw [Module.finrank_eq_card_basis (Pi.basisFun K (Fin m))]
      exact Fintype.card_fin m
    rw [hn] at hex
    exact hex
  let d : Fin m → K := fun i => β (b i) (b i)
  let G := BilinForm.toMatrix b β
  have hG : G = Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [G, d]
    · simp [G, hij]
      exact hb hij
  let s := Pi.basisFun K (Fin m)
  let E := s.toMatrix b
  have hE : IsUnit E.det :=
    Matrix.isUnit_det_of_right_inverse (s.toMatrix_mul_toMatrix_flip b)
  have hGram : E.transpose * P * E = G := by
    simpa [E, s, β, G, BilinForm.toMatrix_basisFun] using
      (BilinForm.toMatrix_mul_basis_toMatrix s b β)
  have hRank : G.rank = P.rank := by
    rw [← hGram, Matrix.rank_mul_eq_left_of_isUnit_det E _ hE,
      Matrix.rank_mul_eq_right_of_isUnit_det E.transpose P
        (Matrix.isUnit_det_transpose E hE)]
  let S := {i : Fin m // d i ≠ 0}
  have hcard : k ≤ Fintype.card S := by
    change k ≤ Fintype.card {i : Fin m // d i ≠ 0}
    rw [← Matrix.rank_diagonal, ← hG, hRank]
    exact hk
  let f : Fin k ↪ S := (Fin.castLEEmb hcard).trans (Fintype.equivFin S).symm.toEmbedding
  choose c hc using fun i : Fin k => IsAlgClosed.exists_eq_mul_self (-(d (f i).1)⁻¹)
  refine ⟨fun i => c i • b (f i).1, ?_⟩
  intro i j
  change β (c i • b (f i).1) (c j • b (f j).1) = _
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    change c i * (c i * d (f i).1) = -1
    rw [← mul_assoc, ← hc i]
    simp [(f i).property]
  · rw [if_neg hij]
    have hne : (f i).1 ≠ (f j).1 := fun h => hij (f.injective (Subtype.ext h))
    have horth : β (b (f i).1) (b (f j).1) = 0 := hb hne
    rw [horth, mul_zero, mul_zero]

section Operators
variable {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- Normalization produces actual anticommuting involutions, rather than
assuming that the Schur relations already have Clifford normal form. -/
theorem exists_anticommuting_involutions [IsAlgClosed K]
    {m k : ℕ} (P : Matrix (Fin m) (Fin m) K) (hP : P.IsSymm)
    (hk : k ≤ P.rank) (J : (Fin m → K) →ₗ[K] Module.End K W)
    (hJ : ∀ u v, J u * J v + J v * J u =
      (-2 * Matrix.toBilin' P u v) • (1 : Module.End K W)) :
    ∃ v : Fin k → (Fin m → K),
      (∀ i, J (v i) * J (v i) = 1) ∧
      ∀ i j, i ≠ j → J (v i) * J (v j) = -(J (v j) * J (v i)) := by
  obtain ⟨v, hv⟩ := exists_negative_orthonormal_frame P hP hk
  refine ⟨v, ?_, ?_⟩
  · intro i
    apply smul_right_injective (Module.End K W) (by norm_num : (2 : K) ≠ 0)
    have h := hJ (v i) (v i)
    rw [hv i i, if_pos rfl] at h
    simpa only [mul_neg, mul_one, neg_neg, two_smul K] using h
  · intro i j hij
    have h := hJ (v i) (v j)
    rw [hv i j, if_neg hij, mul_zero, zero_smul] at h
    exact eq_neg_of_add_eq_zero_left h

theorem two_dvd_finrank_of_clifford_relations [IsAlgClosed K]
    {m : ℕ} (P : Matrix (Fin m) (Fin m) K) (hP : P.IsSymm)
    (hRank : 2 ≤ P.rank) (J : (Fin m → K) →ₗ[K] Module.End K W)
    (hJ : ∀ u v, J u * J v + J v * J u =
      (-2 * Matrix.toBilin' P u v) • (1 : Module.End K W)) :
    2 ∣ finrank K W := by
  obtain ⟨v, hsquare, hanti⟩ := exists_anticommuting_involutions P hP hRank J hJ
  exact CliffordDivisibility.two_dvd_finrank_of_anticommuting_involutions
    (J (v 0)) (J (v 1)) (hsquare 0) (hsquare 1) (hanti 0 1 (by decide))

theorem four_dvd_finrank_of_self_adjoint_clifford_relations [IsAlgClosed K]
    {m : ℕ} (P : Matrix (Fin m) (Fin m) K) (hP : P.IsSymm)
    (hRank : 3 ≤ P.rank) (J : (Fin m → K) →ₗ[K] Module.End K W)
    (hJ : ∀ u v, J u * J v + J v * J u =
      (-2 * Matrix.toBilin' P u v) • (1 : Module.End K W))
    (β : LinearMap.BilinForm K W) (hβ : β.Nondegenerate) (hβsym : β.IsSymm)
    (hself : ∀ u x y, β (J u x) y = β x (J u y)) :
    4 ∣ finrank K W := by
  obtain ⟨v, hsquare, hanti⟩ := exists_anticommuting_involutions P hP hRank J hJ
  exact CliffordDivisibility.four_dvd_finrank_of_three_self_adjoint_anticommuting_involutions
    β hβ hβsym (J (v 0)) (J (v 1)) (J (v 2))
    (hsquare 0) (hsquare 1) (hsquare 2)
    (hanti 0 1 (by decide)) (hanti 0 2 (by decide)) (hanti 1 2 (by decide))
    (hself (v 0)) (hself (v 1)) (hself (v 2))

end Operators

section LinearCombination
variable {A : Type*} [Ring A] [Algebra K A]

omit [CharZero K] in
/-- Bilinear extension of the actual generator relations. -/
theorem linearCombination_anticommutator {m : ℕ}
    (P : Matrix (Fin m) (Fin m) K) (Γ : Fin m → A)
    (hΓ : ∀ i j, Γ i * Γ j + Γ j * Γ i = (-2 * P i j) • (1 : A))
    (u v : Fin m → K) :
    Fintype.linearCombination K Γ u * Fintype.linearCombination K Γ v +
      Fintype.linearCombination K Γ v * Fintype.linearCombination K Γ u =
      (-2 * Matrix.toBilin' P u v) • (1 : A) := by
  classical
  have hmul (u v : Fin m → K) :
      Fintype.linearCombination K Γ u * Fintype.linearCombination K Γ v =
        ∑ i, ∑ j, (u i * v j) • (Γ i * Γ j) := by
    simp only [Fintype.linearCombination_apply, Finset.sum_mul, Finset.mul_sum,
      smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm]
  rw [hmul, hmul]
  calc
    _ = ∑ i, ∑ j, ((u i * v j) • (Γ i * Γ j) +
        (u i * v j) • (Γ j * Γ i)) := by
      simp only [Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_comm]
    _ = ∑ i, ∑ j, ((u i * v j) * (-2 * P i j)) • (1 : A) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [← smul_add, hΓ, smul_smul]
    _ = _ := by
      rw [Matrix.toBilin'_apply, Finset.mul_sum]
      simp only [Finset.mul_sum, Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      ring

end LinearCombination

section SchurMatrices
variable {m q : ℕ}

/-- The actual operators `B₀⁻¹Bᵢ` represented as endomorphisms. -/
def schurGenerator (B0 : Matrix (Fin q) (Fin q) K)
    (B : Fin m → Matrix (Fin q) (Fin q) K) (i : Fin m) :
    Module.End K (Fin q → K) := Matrix.toLinAlgEquiv' (B0⁻¹ * B i)

def schurCliffordMap (B0 : Matrix (Fin q) (Fin q) K)
    (B : Fin m → Matrix (Fin q) (Fin q) K) :
    (Fin m → K) →ₗ[K] Module.End K (Fin q → K) :=
  Fintype.linearCombination K (schurGenerator B0 B)

omit [CharZero K] in
theorem schurGenerator_anticommutator
    (P : Matrix (Fin m) (Fin m) K)
    (B0 : Matrix (Fin q) (Fin q) K) (hB0 : B0.det ≠ 0)
    (B : Fin m → Matrix (Fin q) (Fin q) K)
    (hSchur : ∀ i j, B i * B0⁻¹ * B j + B j * B0⁻¹ * B i =
      (-2 * P i j) • B0) (i j : Fin m) :
    schurGenerator B0 B i * schurGenerator B0 B j +
      schurGenerator B0 B j * schurGenerator B0 B i =
      (-2 * P i j) • (1 : Module.End K (Fin q → K)) := by
  have hmat : (B0⁻¹ * B i) * (B0⁻¹ * B j) + (B0⁻¹ * B j) * (B0⁻¹ * B i) =
      (-2 * P i j) • (1 : Matrix (Fin q) (Fin q) K) := by
    calc
      _ = B0⁻¹ * (B i * B0⁻¹ * B j + B j * B0⁻¹ * B i) := by
        simp only [mul_add, mul_assoc]
      _ = _ := by
        rw [hSchur, mul_smul_comm, Matrix.nonsing_inv_mul B0 (isUnit_iff_ne_zero.mpr hB0)]
  have hop := congrArg (Matrix.toLinAlgEquiv' (R := K)) hmat
  simpa only [schurGenerator, map_add, map_mul, map_smul, map_one] using hop

omit [CharZero K] in
theorem schurCliffordMap_anticommutator
    (P : Matrix (Fin m) (Fin m) K)
    (B0 : Matrix (Fin q) (Fin q) K) (hB0 : B0.det ≠ 0)
    (B : Fin m → Matrix (Fin q) (Fin q) K)
    (hSchur : ∀ i j, B i * B0⁻¹ * B j + B j * B0⁻¹ * B i =
      (-2 * P i j) • B0) (u v : Fin m → K) :
    schurCliffordMap B0 B u * schurCliffordMap B0 B v +
      schurCliffordMap B0 B v * schurCliffordMap B0 B u =
      (-2 * Matrix.toBilin' P u v) • (1 : Module.End K (Fin q → K)) :=
  linearCombination_anticommutator P (schurGenerator B0 B)
    (schurGenerator_anticommutator P B0 hB0 B hSchur) u v

omit [CharZero K] in
theorem schurGenerator_self_adjoint
    (B0 : Matrix (Fin q) (Fin q) K) (hB0 : B0.det ≠ 0) (hB0sym : B0.IsSymm)
    (B : Fin m → Matrix (Fin q) (Fin q) K) (hB : ∀ i, (B i).IsSymm)
    (i : Fin m) (x y : Fin q → K) :
    Matrix.toBilin' B0 (schurGenerator B0 B i x) y =
      Matrix.toBilin' B0 x (schurGenerator B0 B i y) := by
  have hu : IsUnit B0.det := isUnit_iff_ne_zero.mpr hB0
  have hAdj : Matrix.IsAdjointPair B0 B0 (B0⁻¹ * B i) (B0⁻¹ * B i) := by
    unfold Matrix.IsAdjointPair
    rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hB0sym, hB i]
    rw [mul_assoc, Matrix.nonsing_inv_mul B0 hu, mul_one,
      ← mul_assoc, Matrix.mul_nonsing_inv B0 hu, one_mul]
  exact (isAdjointPair_toLinearMap₂' B0 B0 (B0⁻¹ * B i) (B0⁻¹ * B i)).mpr hAdj x y

omit [CharZero K] in
theorem schurCliffordMap_self_adjoint
    (B0 : Matrix (Fin q) (Fin q) K) (hB0 : B0.det ≠ 0) (hB0sym : B0.IsSymm)
    (B : Fin m → Matrix (Fin q) (Fin q) K) (hB : ∀ i, (B i).IsSymm)
    (u : Fin m → K) (x y : Fin q → K) :
    Matrix.toBilin' B0 (schurCliffordMap B0 B u x) y =
      Matrix.toBilin' B0 x (schurCliffordMap B0 B u y) := by
  simp only [schurCliffordMap, Fintype.linearCombination_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [schurGenerator_self_adjoint B0 hB0 hB0sym B hB]

/-- Two nondegenerate normal directions in the actual Schur form force an
even size of the complementary matrix block. -/
theorem two_dvd_of_schur_relations [IsAlgClosed K]
    (P : Matrix (Fin m) (Fin m) K) (hP : P.IsSymm) (hRank : 2 ≤ P.rank)
    (B0 : Matrix (Fin q) (Fin q) K) (hB0 : B0.det ≠ 0)
    (B : Fin m → Matrix (Fin q) (Fin q) K)
    (hSchur : ∀ i j, B i * B0⁻¹ * B j + B j * B0⁻¹ * B i =
      (-2 * P i j) • B0) : 2 ∣ q := by
  have h := two_dvd_finrank_of_clifford_relations P hP hRank
    (schurCliffordMap B0 B) (schurCliffordMap_anticommutator P B0 hB0 B hSchur)
  simpa using h

/-- Three nondegenerate normal directions and symmetry of the Schur blocks
force their size to be divisible by four. -/
theorem four_dvd_of_schur_relations [IsAlgClosed K]
    (P : Matrix (Fin m) (Fin m) K) (hP : P.IsSymm) (hRank : 3 ≤ P.rank)
    (B0 : Matrix (Fin q) (Fin q) K) (hB0 : B0.det ≠ 0) (hB0sym : B0.IsSymm)
    (B : Fin m → Matrix (Fin q) (Fin q) K) (hB : ∀ i, (B i).IsSymm)
    (hSchur : ∀ i j, B i * B0⁻¹ * B j + B j * B0⁻¹ * B i =
      (-2 * P i j) • B0) : 4 ∣ q := by
  have h := four_dvd_finrank_of_self_adjoint_clifford_relations P hP hRank
    (schurCliffordMap B0 B) (schurCliffordMap_anticommutator P B0 hB0 B hSchur)
    (Matrix.toBilin' B0) (LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hB0)
    (toBilin'_isSymm B0 hB0sym) (schurCliffordMap_self_adjoint B0 hB0 hB0sym B hB)
  simpa using h

end SchurMatrices

end HessianTheorem11.CliffordNormalization
