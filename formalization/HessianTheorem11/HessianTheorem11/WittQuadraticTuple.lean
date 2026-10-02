import HessianTheorem11.WittSubspaceBasis
import HessianTheorem11.SmallQuadraticRelations
import Mathlib.Algebra.MvPolynomial.Funext

/-! The independent regular coordinates of an actual polynomial tuple in
an adapted Witt basis. Its quadratic relation is derived by expansion. -/
noncomputable section
namespace HessianTheorem11.WittQuadraticTuple
open Module Submodule MvPolynomial TangentHessianRank
open scoped BigOperators
variable {K σ τ : Type*} [Field K] [CharZero K] [Fintype σ] [Fintype τ] [DecidableEq τ]

abbrev value (p : τ → MvPolynomial σ K) (x : σ → K) : τ → K := fun i => eval x (p i)
def scalarTuple (L : (τ → K) →ₗ[K] K) (p : τ → MvPolynomial σ K) : MvPolynomial σ K :=
  ∑ i, C (L ((Pi.basisFun K τ) i)) * p i

theorem eval_scalarTuple (L : (τ → K) →ₗ[K] K) (p : τ → MvPolynomial σ K) (x : σ → K) :
    eval x (scalarTuple L p) = L (value p x) := by
  classical
  simp only [scalarTuple,map_sum,map_mul,eval_C]
  have he : ∑ i, value p x i • (Pi.basisFun K τ) i = value p x := by
    ext j
    simp [Pi.basisFun_apply, Pi.single_apply, mul_ite]
  rw [← he,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [map_smul,smul_eq_mul,mul_comm]

theorem scalarTuple_homogeneous {d : ℕ}
    (L : (τ → K) →ₗ[K] K) (p : τ → MvPolynomial σ K)
    (hp : ∀ i, (p i).IsHomogeneous d) : (scalarTuple L p).IsHomogeneous d := by
  apply IsHomogeneous.sum
  intro i hi
  exact (hp i).C_mul _

variable {r l k : ℕ} {B : LinearMap.BilinForm K (τ → K)}
  {U : Submodule K (τ → K)}
open WittSubspaceBasis

def regularTuple (D : Data B U r l k) (p : τ → MvPolynomial σ K) : Fin r → MvPolynomial σ K :=
  fun i => scalarTuple (D.basis.coord (regularIndex i)) p

def radicalTuple (D : Data B U r l k) (p : τ → MvPolynomial σ K) : Fin l → MvPolynomial σ K :=
  fun i => scalarTuple (D.basis.coord (radicalIndex i)) p

def regularGram (D : Data B U r l k) : Matrix (Fin r) (Fin r) K :=
  fun i j => B (D.basis (regularIndex i)) (D.basis (regularIndex j))

theorem regularTuple_independent (D : Data B U r l k) (p : τ → MvPolynomial σ K)
    (hspan : Submodule.span K (Set.range (value p)) = U) :
    LinearIndependent K (regularTuple D p) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  let L : (τ → K) →ₗ[K] K := ∑ i, c i • D.basis.coord (regularIndex i)
  have hker : U ≤ LinearMap.ker L := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨x,rfl⟩
    have he := congrArg (eval x) hc
    change L (value p x) = 0
    simpa [L,regularTuple, map_sum, MvPolynomial.smul_eq_C_mul,
      eval_scalarTuple, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using he
  have hb : D.basis (regularIndex j) ∈ U := by
    exact D.subspace_span.le (Submodule.subset_span ⟨Sum.inl j,rfl⟩)
  have he := hker hb
  change L (D.basis (regularIndex j)) = 0 at he
  simpa [L, LinearMap.sum_apply,LinearMap.smul_apply,Basis.coord_apply,
    Basis.repr_self, Finsupp.single_apply, regularIndex,smul_eq_mul,mul_ite] using he

theorem regularTuple_homogeneous {d : ℕ} (D : Data B U r l k)
    (p : τ → MvPolynomial σ K) (hp : ∀ i, (p i).IsHomogeneous d) :
    ∀ i, (regularTuple D p i).IsHomogeneous d :=
  fun i => scalarTuple_homogeneous _ p hp

theorem radical_pair_zero (D : Data B U r l k) (i j : Fin l) :
    B (D.basis (radicalIndex i)) (D.basis (radicalIndex j)) = 0 := by
  by_contra h
  have he := D.gram_weight _ _ h
  norm_num [weight,radicalIndex] at he

theorem regular_radical_pair_zero (D : Data B U r l k) (i : Fin r) (j : Fin l) :
    B (D.basis (regularIndex i)) (D.basis (radicalIndex j)) = 0 :=
  D.regular_orthogonal i (Sum.inl (Sum.inl j))

theorem coord_dual_zero (D : Data B U r l k) (u : τ → K) (hu : u ∈ U) (i : Fin l) :
    D.basis.coord (dualIndex i) u = 0 := by
  have hs : U ≤ LinearMap.ker (D.basis.coord (dualIndex i)) := by
    apply D.subspace_span.symm.le.trans
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    cases j <;> simp [LinearMap.mem_ker, Basis.coord_apply,Basis.repr_self,
      Finsupp.single_apply,regularIndex,radicalIndex,dualIndex]
  exact hs hu

theorem coord_residual_zero (D : Data B U r l k) (u : τ → K) (hu : u ∈ U) (i : Fin k) :
    D.basis.coord (residualIndex i) u = 0 := by
  have hs : U ≤ LinearMap.ker (D.basis.coord (residualIndex i)) := by
    apply D.subspace_span.symm.le.trans
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    cases j <;> simp [LinearMap.mem_ker, Basis.coord_apply,Basis.repr_self,
      Finsupp.single_apply,regularIndex,radicalIndex,residualIndex]
  exact hs hu

theorem value_expansion (D : Data B U r l k) (p : τ → MvPolynomial σ K)
    (hmem : ∀ x, value p x ∈ U) (x : σ → K) :
    value p x =
      (∑ i, eval x (regularTuple D p i) • D.basis (regularIndex i)) +
      (∑ i, eval x (radicalTuple D p i) • D.basis (radicalIndex i)) := by
  have he := D.basis.sum_repr (value p x)
  simp only [Fintype.sum_sum_type] at he
  have hd (i : Fin l) : D.basis.repr (value p x) (dualIndex i) = 0 :=
    coord_dual_zero D _ (hmem x) i
  have hr (i : Fin k) : D.basis.repr (value p x) (residualIndex i) = 0 :=
    coord_residual_zero D _ (hmem x) i
  simp only [dualIndex] at hd
  simp only [residualIndex] at hr
  simp only [hd,hr,zero_smul,Finset.sum_const_zero,add_zero] at he
  simpa only [regularTuple,radicalTuple,eval_scalarTuple,Basis.coord_apply,
    regularIndex,radicalIndex] using he.symm

theorem regular_relation (D : Data B U r l k) (hB : B.IsSymm)
    (p : τ → MvPolynomial σ K) (hmem : ∀ x, value p x ∈ U)
    (hrel : ∀ x, B (value p x) (value p x) = 0) :
    quadraticRelation (regularGram D) (regularTuple D p) = 0 := by
  apply MvPolynomial.funext
  intro x
  have he := hrel x
  rw [value_expansion D p hmem x] at he
  have hrw := regular_radical_pair_zero D
  have hwr (i j) : B (D.basis (radicalIndex i)) (D.basis (regularIndex j)) = 0 := by
    rw [hB.eq]
    exact hrw j i
  have hww := radical_pair_zero D
  simp only [map_add, LinearMap.add_apply,map_sum,LinearMap.sum_apply,
    map_smul,LinearMap.smul_apply,smul_eq_mul,hrw,hwr,hww,mul_zero,
    Finset.sum_const_zero,add_zero] at he
  convert he using 1
  simp only [quadraticRelation,regularGram,map_sum,map_mul,eval_C,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hB.eq (D.basis (regularIndex j)) (D.basis (regularIndex i))]
  ring

theorem regularGram_symm (D : Data B U r l k) (hB : B.IsSymm) :
    (regularGram D).IsSymm := by
  ext i j
  exact hB.eq _ _

section AlgebraicallyClosed
variable [IsAlgClosed K]

theorem regular_rank_ne_one (D : Data B U r l k) (hB : B.IsSymm)
    (p : τ → MvPolynomial σ K) (hspan : Submodule.span K (Set.range (value p)) = U)
    (hrel : ∀ x, B (value p x) (value p x) = 0) : r ≠ 1 := by
  intro hr
  subst r
  exact one_independent_no_quadratic_relation (regularTuple D p)
    (regularTuple_independent D p hspan) (regularGram D) (regularGram_symm D hB)
    D.regular_nonsingular (regular_relation D hB p
      (fun x => hspan.le (Submodule.subset_span ⟨x,rfl⟩)) hrel)

theorem regular_rank_ne_two (D : Data B U r l k) (hB : B.IsSymm)
    (p : τ → MvPolynomial σ K) (hspan : Submodule.span K (Set.range (value p)) = U)
    (hrel : ∀ x, B (value p x) (value p x) = 0) : r ≠ 2 := by
  intro hr
  subst r
  exact two_independent_no_quadratic_relation (regularTuple D p)
    (regularTuple_independent D p hspan) (regularGram D) (regularGram_symm D hB)
    D.regular_nonsingular (regular_relation D hB p
      (fun x => hspan.le (Submodule.subset_span ⟨x,rfl⟩)) hrel)

theorem deficient_five_cases (D : Data B U r l k) (hB : B.IsSymm)
    (p : τ → MvPolynomial σ K) (hspan : Submodule.span K (Set.range (value p)) = U)
    (hrel : ∀ x, B (value p x) (value p x) = 0)
    (hambient : Fintype.card τ = 5) (hproper : finrank K U ≤ 4) :
    (r = 0 ∧ l ≤ 2) ∨ (r = 3 ∧ l ≤ 1) ∨ (r = 4 ∧ l = 0) := by
  have hd := D.ambient_dimension
  simp only [Module.finrank_pi, Module.finrank_self, Finset.sum_const, smul_eq_mul,
    mul_one, Finset.card_univ] at hd
  have hs := D.subspace_dimension
  have h1 := regular_rank_ne_one D hB p hspan hrel
  have h2 := regular_rank_ne_two D hB p hspan hrel
  omega

end AlgebraicallyClosed
end HessianTheorem11.WittQuadraticTuple
