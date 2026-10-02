import HessianTheorem11.UnconditionalWeightDescent
import HessianTheorem11.ReducedClosedOrbitZero
import HessianTheorem11.CubicIrreducibility
import HessianTheorem11.SingularCompleted
import HessianTheorem11.SingularGeometry
import HessianTheorem11.KernelGradientSpan

/-! Rational restrictions and singular linear spaces in Theorem I.1.1(iv).
All restrictions below are the actual polynomial substitution along an injective
rational matrix. Submodule coordinates are constructed from `Module.finBasis`.
No new geometric input is introduced. -/

noncomputable section
namespace HessianTheorem11.BibleRestrictions
open Module MvPolynomial RationalDescent NonzeroLimitTransport

/-- The general singular radial inequality, assembled on the actual finite
component cover, gives the integer floor bound in every positive dimension. -/
theorem singularDimension_le_radial_floor
    (QC : FiniteQuadraticConeCoverInput) (DT : SymmetricDeterminantalTangentInput)
    {n : ℕ}
    (F : AnisotropicCubic n) (hn : 0 < n) :
    singularDimension F.polynomial ≤ ((2*n-3)/3 : ℕ) := by
  let C := singularComponentCover QC F.polynomial F.homogeneous
  apply singularDimension_le_of_component_inputs F.polynomial C.component C.point
  · rw [← singular_equation_zeroSet]
    exact C.covers
  · exact singularComponentCover_radial QC DT F.polynomial F.homogeneous
      (UnconditionalWeightDescent.anisotropic_geometric_weightSemistable F hn)
  · intro i ht hr
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).mpr
    have h := SingularNumerics.component_envelope (n := n) (by omega) hr
    omega

/-- Every injective rational linear restriction remains an anisotropic cubic
and satisfies the general singular-locus bound with its own derivatives. -/
theorem restriction_anisotropic_and_singularDimension
    (QC : FiniteQuadraticConeCoverInput) (DT : SymmetricDeterminantalTangentInput)
    {n m : ℕ}
    (F : AnisotropicCubic n) (B : Matrix (Fin n) (Fin m) ℚ)
    (hB : Function.Injective B.mulVec) (hm : 4 ≤ m) :
    Anisotropic (PolynomialRestriction.restrict B F.polynomial) ∧
      singularDimension (PolynomialRestriction.restrict B F.polynomial) ≤
        ((2*m-3)/3 : ℕ) := by
  exact ⟨PolynomialRestriction.anisotropic_restrict B F.polynomial F.anisotropic hB,
    singularDimension_le_radial_floor QC DT 
      (PolynomialRestriction.restrictedCubic B F hB) (by omega)⟩

/-- Actual rational coordinates on a subspace, from its finite basis. -/
def subspaceCoordinates {n : ℕ} (M : Submodule ℚ (Fin n → ℚ)) :
    (Fin (finrank ℚ M) → ℚ) →ₗ[ℚ] (Fin n → ℚ) :=
  M.subtype.comp (Module.finBasis ℚ M).equivFun.symm.toLinearMap

def subspaceMatrix {n : ℕ} (M : Submodule ℚ (Fin n → ℚ)) :
    Matrix (Fin n) (Fin (finrank ℚ M)) ℚ :=
  LinearMap.toMatrix' (subspaceCoordinates M)

@[simp] theorem subspaceMatrix_mulVec {n : ℕ}
    (M : Submodule ℚ (Fin n → ℚ)) (z : Fin (finrank ℚ M) → ℚ) :
    (subspaceMatrix M).mulVec z = subspaceCoordinates M z :=
  LinearMap.toMatrix'_mulVec _ _

theorem subspaceMatrix_injective {n : ℕ} (M : Submodule ℚ (Fin n → ℚ)) :
    Function.Injective (subspaceMatrix M).mulVec := by
  intro u v h
  simp only [subspaceMatrix_mulVec] at h
  exact (Module.finBasis ℚ M).equivFun.symm.injective (Subtype.val_injective h)

theorem subspaceCoordinates_range {n : ℕ} (M : Submodule ℚ (Fin n → ℚ)) :
    LinearMap.range (subspaceCoordinates M) = M := by
  ext y
  constructor
  · rintro ⟨z,rfl⟩
    exact ((Module.finBasis ℚ M).equivFun.symm z).property
  · intro hy
    refine ⟨(Module.finBasis ℚ M).equivFun ⟨y,hy⟩, ?_⟩
    simp [subspaceCoordinates]

def subspaceCubic {n : ℕ} (F : AnisotropicCubic n)
    (M : Submodule ℚ (Fin n → ℚ)) : AnisotropicCubic (finrank ℚ M) :=
  PolynomialRestriction.restrictedCubic (subspaceMatrix M) F (subspaceMatrix_injective M)

/-- Evaluation of the chosen polynomial is exactly evaluation of F on M. -/
@[simp] theorem eval_subspaceCubic {n : ℕ} (F : AnisotropicCubic n)
    (M : Submodule ℚ (Fin n → ℚ)) (z : Fin (finrank ℚ M) → ℚ) :
    eval z (subspaceCubic F M).polynomial = eval (subspaceCoordinates M z) F.polynomial := by
  exact (PolynomialRestriction.eval_restrict _ _ _).trans
    (congrArg (fun x => eval x F.polynomial) (subspaceMatrix_mulVec M z))

theorem subspace_anisotropic_and_singularDimension
    (QC : FiniteQuadraticConeCoverInput) (DT : SymmetricDeterminantalTangentInput)
    {n : ℕ}
    (F : AnisotropicCubic n) (M : Submodule ℚ (Fin n → ℚ))
    (hm : 4 ≤ finrank ℚ M) :
    Anisotropic (subspaceCubic F M).polynomial ∧
      singularDimension (subspaceCubic F M).polynomial ≤
        ((2*finrank ℚ M-3)/3 : ℕ) :=
  restriction_anisotropic_and_singularDimension QC DT  F
    (subspaceMatrix M) (subspaceMatrix_injective M) hm

/-- Polarizing the identically vanishing gradient on an actual linear space
kills the cubic tensor with two arguments in that space. -/
theorem singular_subspace_tensor {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (L : Submodule K (Fin n → K)) (hL : ∀ x ∈ L, gradient F x = 0)
    (u : Fin n → K) (hu : u ∈ L) (v : Fin n → K) (hv : v ∈ L)
    (w : Fin n → K) : polarization F u v w = 0 := by
  have hd (a : Fin n → K) (ha : a ∈ L) : polarization F w a a = 0 := by
    rw [polarization_diagonal_eq_gradient F hF, hL a ha]
    simp
  have h := hd (u+v) (L.add_mem hu hv)
  rw [polarization_add_second, polarization_add_third hF,
    polarization_add_third hF, hd u hu, hd v hv,
    polarization_swap_last hF w v u] at h
  rw [polarization_rotate hF]
  linear_combination (1/2 : K) * h

/-- The weight -2 on L and +1 on its complement proves 3 dim L ≤ n. -/
theorem singular_subspace_finrank_bound_of_semistable
    {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (hsemi : WeightSemistable F) (L : Submodule K (Fin n → K))
    (hL : ∀ x ∈ L, gradient F x = 0) : 3*finrank K L ≤ n := by
  classical
  by_cases hzero : L = ⊥
  · rw [hzero, finrank_bot]
    omega
  obtain ⟨x,hx,hne⟩ := L.ne_bot_iff.mp hzero
  let A := adaptedFlagBasis L L le_rfl x hne hx
  let w : Fin n → ℤ := fun i => if i ∈ A.tangentIndices then -2 else 1
  have hw : 0 ≤ ∑ i, w i := by
    apply hsemi.nonnegative_weight_sum_of_thirdPartials hF
      (basisMatrix A.basis) (basisMatrix_injective A.basis) w
    intro i j k ht
    change coeff 0 (pderiv k (pderiv j (pderiv i
      (PolynomialRestriction.restrict (basisMatrix A.basis) F)))) ≠ 0 at ht
    rw [polarization_in_coordinates F hF] at ht
    have hij : ¬ (i ∈ A.tangentIndices ∧ j ∈ A.tangentIndices) := by
      rintro ⟨hi,hj⟩
      exact ht (singular_subspace_tensor F hF L hL _
        ((A.mem_tangent_iff i).mpr hi) _ ((A.mem_tangent_iff j).mpr hj) _)
    have hik : ¬ (i ∈ A.tangentIndices ∧ k ∈ A.tangentIndices) := by
      rintro ⟨hi,hk⟩
      apply ht
      rw [polarization_swap_last hF]
      exact singular_subspace_tensor F hF L hL _
        ((A.mem_tangent_iff i).mpr hi) _ ((A.mem_tangent_iff k).mpr hk) _
    have hjk : ¬ (j ∈ A.tangentIndices ∧ k ∈ A.tangentIndices) := by
      rintro ⟨hj,hk⟩
      apply ht
      rw [polarization_swap_first, polarization_swap_last hF]
      exact singular_subspace_tensor F hF L hL _
        ((A.mem_tangent_iff j).mpr hj) _ ((A.mem_tangent_iff k).mpr hk) _
    by_cases hi : i ∈ A.tangentIndices <;>
      by_cases hj : j ∈ A.tangentIndices <;>
        by_cases hk : k ∈ A.tangentIndices <;> simp_all [w]
  have he (i : Fin n) : w i = 1-3*(if i ∈ A.tangentIndices then 1 else 0) := by
    simp only [w]
    split_ifs <;> norm_num
  simp only [he, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum] at hw
  simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter,
    A.tangent_card] at hw
  norm_num at hw
  omega

theorem singular_subspace_finrank_bound
    {n : ℕ}
    (F : AnisotropicCubic n) (hn : 0 < n)
    (L : Submodule GeometricField (GeometricPoint n))
    (hL : (L : Set (GeometricPoint n)) ⊆ singularLocus F.polynomial) :
    3*finrank GeometricField L ≤ n :=
  singular_subspace_finrank_bound_of_semistable _ (geometric_homogeneous F.homogeneous)
    (UnconditionalWeightDescent.anisotropic_geometric_weightSemistable F hn) L hL

section StrongRestrictions

variable (AG : ConcentrationGeometryInput) (GP : GenericConePointSelectionInput)
    (DT : SymmetricDeterminantalTangentInput)
    (KB : KernelBundleTangentImageInput) (SA : FormalSmoothArcInput)
    (AD : AffineHypersurfaceDimensionInput) (MR : GenericMatrixRankInput)
    (KA : KernelAnnihilatorGeometryInput) (FD : AffineFiberDimensionInput)
    (LS : LinearSectionDimensionInput)
    (boundary : RationalRelativeBoundaryInput) (bigCell : TextbookOrbitBigCellInput)
    (DTQ : DeterminantalTangentOver ℚ) (CI : CubicGeometricIrreducibility)
    (FI : FormalImplicitFunctionInput GeometricField)
    include AG GP DT KB SA AD MR KA FD LS boundary bigCell DTQ CI FI 

/-- Rational hyperplane sections inherit the completed eleven-variable affine
singular bound. Projectivization is handled separately by the caller. -/
theorem restriction_singularDimension_eleven
    (F : AnisotropicCubic 12) (B : Matrix (Fin 12) (Fin 11) ℚ)
    (hB : Function.Injective B.mulVec) :
    singularDimension (PolynomialRestriction.restrict B F.polynomial) ≤ 5 :=
  Completed.S11 AG.toAffineComponentsInput GP AG.toGenericRankOpenInput DT KB SA AD
    AG.toKernelBundleInput MR KA FD LS boundary bigCell DTQ CI FI 
    (PolynomialRestriction.restrictedCubic B F hB)

/-- In twelve ambient variables an injective restriction of dimension at
least eleven has dimension eleven or twelve, giving the stronger bound m-6. -/
theorem restriction_singularDimension_strong
    (F : AnisotropicCubic 12) {m : ℕ} (B : Matrix (Fin 12) (Fin m) ℚ)
    (hB : Function.Injective B.mulVec) (hm : 11 ≤ m) :
    singularDimension (PolynomialRestriction.restrict B F.polynomial) ≤ (m-6 : ℕ) := by
  have hdim : m ≤ 12 := by
    simpa using LinearMap.finrank_le_finrank_of_injective (f := B.mulVecLin) hB
  have hcases : m = 11 ∨ m = 12 := by omega
  rcases hcases with rfl | rfl
  · exact restriction_singularDimension_eleven AG GP DT KB SA AD MR KA FD LS
      boundary bigCell DTQ CI FI  F B hB
  · exact Completed.S12 AG.toAffineComponentsInput GP AG.toGenericRankOpenInput DT MR AD SA
      boundary bigCell DTQ CI FI 
      (PolynomialRestriction.restrictedCubic B F hB)

/-- The stronger restriction theorem on an actual rational submodule M. -/
theorem subspace_singularDimension_strong
    (F : AnisotropicCubic 12) (M : Submodule ℚ (Fin 12 → ℚ))
    (hm : 11 ≤ finrank ℚ M) :
    singularDimension (subspaceCubic F M).polynomial ≤ (finrank ℚ M-6 : ℕ) :=
  restriction_singularDimension_strong AG GP DT KB SA AD MR KA FD LS boundary bigCell
    DTQ CI FI  F (subspaceMatrix M) (subspaceMatrix_injective M) hm

/-- The complete restriction and singular-linear-space assertions of
Theorem I.1.1(iv), in actual finite-basis coordinates on every rational M. -/
theorem theorem_I_1_1_iv
    (QC : FiniteQuadraticConeCoverInput) (F : AnisotropicCubic 12) :
    (∀ M : Submodule ℚ (Fin 12 → ℚ), 4 ≤ finrank ℚ M →
      Anisotropic (subspaceCubic F M).polynomial ∧
      singularDimension (subspaceCubic F M).polynomial ≤
        ((2*finrank ℚ M-3)/3 : ℕ) ∧
      (11 ≤ finrank ℚ M → singularDimension (subspaceCubic F M).polynomial ≤
        (finrank ℚ M-6 : ℕ))) ∧
    (∀ L : Submodule GeometricField (GeometricPoint 12),
      (L : Set (GeometricPoint 12)) ⊆ singularLocus F.polynomial →
      3*finrank GeometricField L ≤ 12) := by
  constructor
  · intro M hm
    obtain ⟨ha,hd⟩ := subspace_anisotropic_and_singularDimension QC DT  F M hm
    exact ⟨ha,hd,fun hlarge => subspace_singularDimension_strong AG GP DT KB SA AD MR KA FD LS
      boundary bigCell DTQ CI FI  F M hlarge⟩
  · intro L hL
    exact singular_subspace_finrank_bound  F (by norm_num) L hL

end StrongRestrictions

end HessianTheorem11.BibleRestrictions
