import HessianTheorem11.ReducedClosedOrbitZero
import HessianTheorem11.CubicRankIrreducibility
import HessianTheorem11.BasisWeightSum
import HessianTheorem11.RationalDescent

/-!
Geometric irreducibility from weight semistability, without geometric
factorization descent. A reducible cubic is a product of homogeneous factors
of degrees one and two. On the kernel of the linear factor the cubic tensor
vanishes on three arguments. Weights -1 on that hyperplane and 2 on its
complement have nonnegative supported weights and negative total weight
in at least four variables, contradicting semistability.
-/
noncomputable section
namespace HessianTheorem11.ReducedIrreducibility
open MvPolynomial Module ReducibleCubicRank
variable {K : Type*} [Field K] {n : ℕ}

lemma tensor_zero_on_linear_factor
    (L Q : MvPolynomial (Fin n) K) (hL : L.IsHomogeneous 1)
    (hQ : Q.IsHomogeneous 2) (u v w : Fin n → K)
    (hu : eval u L = 0) (hv : eval v L = 0) (hw : eval w L = 0) :
    polarization (L*Q) u v w = 0 := by
  rw [eval_linear L hL] at hu hv
  rw [polarization, hessian_linear_product L Q hL hQ, hw]
  simp [Matrix.add_mulVec, Matrix.vecMulVec_mulVec, hv, dotProduct_smul,
    dotProduct_comm u (linearCoefficient L), hu]

/-- Any subspace on which the entire cubic tensor vanishes in three slots
has dimension at most two thirds of the ambient dimension. -/
theorem tensor_zero_subspace_dimension_bound [CharZero K]
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (hsemi : WeightSemistable F) (T : Submodule K (Fin n → K))
    (hT : ∀ u ∈ T, ∀ v ∈ T, ∀ w ∈ T, polarization F u v w = 0) :
    3 * finrank K T ≤ 2*n := by
  classical
  by_cases hzero : T = ⊥
  · rw [hzero, finrank_bot]
    omega
  obtain ⟨x,hx,hne⟩ := T.ne_bot_iff.mp hzero
  let A := adaptedFlagBasis T T le_rfl x hne hx
  let w : Fin n → ℤ := fun i => if i ∈ A.tangentIndices then -1 else 2
  have hw : 0 ≤ ∑ i, w i := by
    apply hsemi.nonnegative_weight_sum_of_basis_tensor hF A.basis w
    intro i j k ht
    have hh : ¬ (i ∈ A.tangentIndices ∧ j ∈ A.tangentIndices ∧
        k ∈ A.tangentIndices) := by
      rintro ⟨hi,hj,hk⟩
      exact ht (hT _ ((A.mem_tangent_iff i).mpr hi)
        _ ((A.mem_tangent_iff j).mpr hj) _ ((A.mem_tangent_iff k).mpr hk))
    by_cases hi : i ∈ A.tangentIndices <;>
      by_cases hj : j ∈ A.tangentIndices <;>
        by_cases hk : k ∈ A.tangentIndices <;> simp_all [w]
  have he (i : Fin n) : w i = 2-3*(if i ∈ A.tangentIndices then 1 else 0) := by
    simp only [w]
    split_ifs <;> norm_num
  simp only [he, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum] at hw
  simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter,
    A.tangent_card] at hw
  norm_num at hw
  omega

/-- Every weight-semistable homogeneous cubic in at least four variables
is irreducible, over any characteristic-zero field. -/
theorem cubic_irreducible_of_weightSemistable [CharZero K]
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (hsemi : WeightSemistable F) (hn : 4 ≤ n) : Irreducible F := by
  classical
  have hzero : F ≠ 0 := by
    intro hz
    subst F
    apply hsemi 1 (by intro x y h; simpa only [Matrix.one_mulVec] using h) (fun _ => 0) (by simp)
    simp [HasPositiveWeights, PolynomialRestriction.restrict]
  by_contra hred
  obtain ⟨L,Q,hL,hQ,hfactor⟩ :=
    reducible_homogeneous_cubic_linear_times_quadratic F hF hzero hred
  let ℓ : (Fin n → K) →ₗ[K] K := {
    toFun := fun x => eval x L
    map_add' := eval_add_homogeneous_one hL
    map_smul' := fun a x => eval_smul_homogeneous_one hL a x }
  have ht : 3 * finrank K (LinearMap.ker ℓ) ≤ 2*n := by
    apply tensor_zero_subspace_dimension_bound F hF hsemi (LinearMap.ker ℓ)
    intro u hu v hv w hw
    rw [hfactor]
    exact tensor_zero_on_linear_factor L Q hL hQ u v w hu hv hw
  have he := ℓ.finrank_range_add_finrank_ker
  have hr : finrank K (LinearMap.range ℓ) ≤ 1 := by
    simpa using (Submodule.finrank_le (LinearMap.range ℓ))
  simp only [finrank_pi, Fintype.card_fin] at he
  omega

/-- Geometric irreducibility of an anisotropic rational cubic, using only
the retained relative Kempf input and proved zero-target rational descent. -/
theorem anisotropic_geometric_irreducible
    (CK : ReducedClosedOrbit.ClosedOrbitKempfInput GeometricField)
    (F : AnisotropicCubic n) (hn : 4 ≤ n) :
    Irreducible (geometricPolynomial F.polynomial) := by
  exact cubic_irreducible_of_weightSemistable _ (geometric_homogeneous F.homogeneous)
    (ReducedClosedOrbit.anisotropic_geometric_weightSemistable CK F (by omega)) hn

end HessianTheorem11.ReducedIrreducibility
