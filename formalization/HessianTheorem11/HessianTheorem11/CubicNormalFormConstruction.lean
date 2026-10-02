import HessianTheorem11.LocalCubicNormalForm
import HessianTheorem11.CubicHyperbolicBasis
import HessianTheorem11.PolarizationExpansion
import HessianTheorem11.SmoothCubicPoint

/-! Construction of the displayed local cubic normal form from an actual
Hessian-adapted basis. All coefficients are actual tensor evaluations. -/

noncomputable section
namespace HessianTheorem11.CubicNormalFormConstruction
open MvPolynomial LocalCubicNormalForm
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K] {n m q : ℕ}

/-- A coordinate block evaluated as a vector in the original space. -/
def blockVector {ι : Type*} [Fintype ι]
    (b : ι → Fin n → K) (v : ι → K) : Fin n → K := ∑ i, v i • b i

/-- The quadratic form with its actual tensor coefficients. -/
def tensorQuadratic {ι : Type*} [Fintype ι]
    (F : MvPolynomial (Fin n) K) (b : ι → Fin n → K) (z : Fin n → K) :
    MvPolynomial ι K := (C (1/2 : K)) * ∑ i, ∑ j,
      C (polarization F (b i) (b j) z) * X i * X j

theorem tensorQuadratic_homogeneous {ι : Type*} [Fintype ι]
    (F : MvPolynomial (Fin n) K) (b : ι → Fin n → K) (z : Fin n → K) :
    (tensorQuadratic F b z).IsHomogeneous 2 := by
  classical
  apply IsHomogeneous.C_mul
  apply IsHomogeneous.sum
  intro i _
  apply IsHomogeneous.sum
  intro j _
  simpa using (isHomogeneous_C_mul_X (polarization F (b i) (b j) z) i).mul
    (isHomogeneous_X K j)

theorem eval_tensorQuadratic {ι : Type*} [Fintype ι]
    (F : MvPolynomial (Fin n) K) (b : ι → Fin n → K) (z : Fin n → K) (v : ι → K) :
    eval v (tensorQuadratic F b z) =
      (1/2 : K) * polarization F (blockVector b v) (blockVector b v) z := by
  classical
  simp only [tensorQuadratic, map_mul, map_sum, eval_C, eval_X, blockVector,
    polarization_sum_first, polarization_sum_second,
    polarization_smul_first, polarization_smul_second]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [polarization_swap_first F (b j) (b i)]
  ring

variable {F : MvPolynomial (Fin n) K} {x : Fin n → K}

def radicalBlock (S : HyperbolicBasis.Splitting (hessianBilinear F x) x m q) :
    Fin m → Fin n → K := fun i => S.basis (aIndex i)

def middleBlock (S : HyperbolicBasis.Splitting (hessianBilinear F x) x m q) :
    Fin q → Fin n → K := fun j => S.basis (bIndex j)

def partner (S : HyperbolicBasis.Splitting (hessianBilinear F x) x m q) : Fin n → K :=
    S.basis (zIndex m q)

def coordinateMatrix (S : HyperbolicBasis.Splitting (hessianBilinear F x) x m q) :
    Matrix (Fin n) (Coordinate m q) K := fun i j => S.basis j i

def residualMatrix (S : HyperbolicBasis.Splitting (hessianBilinear F x) x m q) :
    Matrix (Fin n) (ResidualCoordinate q) K :=
    fun i j => S.basis (residualIndex j) i

def data (hF : F.IsHomogeneous 3)
    (S : HyperbolicBasis.Splitting (hessianBilinear F x) x m q) : Data (K := K) m q where
  QA := tensorQuadratic F (radicalBlock S) (partner S)
  Q0 := tensorQuadratic F (middleBlock S) x
  Q := fun i => tensorQuadratic F (middleBlock S) (radicalBlock S i)
  QA_homogeneous := tensorQuadratic_homogeneous _ _ _
  Q0_homogeneous := tensorQuadratic_homogeneous _ _ _
  Q_homogeneous := fun i => tensorQuadratic_homogeneous _ _ _
  abz := fun i j => polarization F (radicalBlock S i) (middleBlock S j) (partner S)
  azz := fun i => (1/2 : K) * polarization F (radicalBlock S i) (partner S) (partner S)
  R := PolynomialRestriction.restrict (residualMatrix S) F
  R_homogeneous := PolynomialRestriction.homogeneous_restrict _ _ hF

theorem coordinateMatrix_mulVec
    (S : HyperbolicBasis.Splitting (hessianBilinear F x) x m q)
    (v : Coordinate m q → K) :
    (coordinateMatrix S).mulVec v =
      v (xIndex m q) • x +
      (blockVector (radicalBlock S) (v ∘ aIndex) +
      (blockVector (middleBlock S) (v ∘ bIndex) + v (zIndex m q) • partner S)) := by
  ext i
  simp only [coordinateMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Fin.sum_univ_two, blockVector, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Pi.add_apply, Function.comp_apply, radicalBlock, middleBlock, partner,
    aIndex, bIndex, xIndex, zIndex, S.radial_eq]
  simp only [mul_comm]
  ring

theorem residualMatrix_mulVec
    (S : HyperbolicBasis.Splitting (hessianBilinear F x) x m q)
    (v : ResidualCoordinate q → K) :
    (residualMatrix S).mulVec v =
      blockVector (middleBlock S) (v ∘ Sum.inl) + v (Sum.inr ()) • partner S := by
  ext i
  simp [residualMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    residualIndex, blockVector, middleBlock, partner, mul_comm]

theorem polarization_radial_eq (hF : F.IsHomogeneous 3) (u v : Fin n → K) :
    polarization F x u v = hessianBilinear F x u v := by
  rw [hessianBilinear_apply]
  exact (polarization_rotate hF u v x).symm

theorem radical_block_mem_ker
    (S : HyperbolicBasis.Splitting (hessianBilinear F x) x m q) (a : Fin m → K) :
    blockVector (radicalBlock S) a ∈ LinearMap.ker (hessianBilinear F x) := by
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (S.radical_vectors i)

theorem middle_block_orthogonal
    (S : HyperbolicBasis.Splitting (hessianBilinear F x) x m q) (b : Fin q → K) :
    hessianBilinear F x x (blockVector (middleBlock S) b) = 0 ∧
    hessianBilinear F x (partner S) (blockVector (middleBlock S) b) = 0 := by
  have h (k : Fin 2) : hessianBilinear F x (S.basis (Sum.inr (Sum.inr k)))
      (blockVector (middleBlock S) b) = 0 := by
    simp only [blockVector, map_sum, map_smul, smul_eq_mul, middleBlock, bIndex,
      S.middle_orthogonal, mul_zero, Finset.sum_const_zero]
  exact ⟨by simpa only [S.radial_eq] using h 0, h 1⟩

/-- The scalar expansion contains exactly the seven blocks of the source's
normal form. The hypotheses are actual tensor vanishings, not coefficients
of an asserted normal form. -/
theorem eval_hyperbolic_blocks
    (hF : F.IsHomogeneous 3)
    (S : HyperbolicBasis.Splitting (hessianBilinear F x) x m q)
    (a b : Fin n → K) (Xc Zc : K)
    (ha : a ∈ LinearMap.ker (hessianBilinear F x))
    (hb : hessianBilinear F x x b = 0)
    (hzb : hessianBilinear F x (partner S) b = 0)
    (haaa : polarization F a a a = 0) (haab : polarization F a a b = 0) :
    eval (Xc • x + (a + (b + Zc • partner S))) F =
      Zc * Xc^2 + Zc * ((1/2 : K) * polarization F a a (partner S)) +
      Xc * ((1/2 : K) * polarization F b b x) +
      (1/2 : K) * polarization F b b a +
      Zc * polarization F a b (partner S) +
      Zc^2 * ((1/2 : K) * polarization F a (partner S) (partner S)) +
      eval (b + Zc • partner S) F := by
  have hxav (v : Fin n → K) : polarization F x a v = 0 := by
    rw [polarization_radial_eq hF]
    exact congrArg (fun L : (Fin n → K) →ₗ[K] K => L v) ha
  have hxxx : polarization F x x x = 0 := by
    rw [polarization_radial_eq hF]
    exact S.radial_self
  have hxxb : polarization F x x b = 0 := by
    rw [polarization_radial_eq hF]; exact hb
  have hxxz : polarization F x x (partner S) = 2 := by
    rw [polarization_radial_eq hF]; exact S.radial_partner
  have hxzz : polarization F x (partner S) (partner S) = 0 := by
    rw [polarization_radial_eq hF]; exact S.partner_self
  have hxzb : polarization F x (partner S) b = 0 := by
    rw [polarization_radial_eq hF]; exact hzb
  have hxxa : polarization F x x a = 0 := by
    rw [polarization_swap_last hF]; exact hxav x
  have hxba : polarization F x b a = 0 := by
    rw [polarization_swap_last hF]; exact hxav b
  have hxza : polarization F x (partner S) a = 0 := by
    rw [polarization_swap_last hF]; exact hxav (partner S)
  have hxbz : polarization F x b (partner S) = 0 := by
    rw [polarization_swap_last hF]; exact hxzb
  rw [eval_cubic_add hF, eval_cubic_add hF a (b + Zc • partner S),
    eval_cubic_eq_polarization hF (Xc • x), eval_cubic_eq_polarization hF a]
  simp only [polarization_add_first, polarization_add_second, polarization_add_third hF,
    polarization_smul_first, polarization_smul_second, polarization_smul_third hF,
    hxxx, hxxa, hxxb, hxxz, hxzz, hxzb, hxbz, hxza, hxba, hxav, haaa, haab,
    polarization_swap_last hF a (partner S) b]
  rw [polarization_rotate hF b b x, polarization_rotate hF b b a]
  ring

/-- The two tangent blocks have zero differential. -/
theorem blocks_differential_zero (hF : F.IsHomogeneous 3)
    (S : HyperbolicBasis.Splitting (hessianBilinear F x) x m q)
    (a : Fin m → K) (b : Fin q → K) :
    polynomialDifferential F x (blockVector (radicalBlock S) a) = 0 ∧
    polynomialDifferential F x (blockVector (middleBlock S) b) = 0 := by
  constructor
  · simp only [blockVector, map_sum, map_smul, smul_eq_mul, radicalBlock,
      aIndex, S.radical_differential_zero hF, mul_zero, Finset.sum_const_zero]
  · simp only [blockVector, map_sum, map_smul, smul_eq_mul, middleBlock,
      bIndex, S.middle_differential_zero hF, mul_zero, Finset.sum_const_zero]

theorem tensor_radical_blocks_zero (hF : F.IsHomogeneous 3)
    (S : HyperbolicBasis.Splitting (hessianBilinear F x) x m q)
    (htensor : ∀ t, polynomialDifferential F x t = 0 →
      ∀ i j, polarization F t (radicalBlock S i) (radicalBlock S j) = 0)
    (t : Fin n → K) (ht : polynomialDifferential F x t = 0)
    (a a' : Fin m → K) :
    polarization F t (blockVector (radicalBlock S) a)
      (blockVector (radicalBlock S) a') = 0 := by
  classical
  simp only [blockVector, polarization_sum_second, polarization_sum_third Finset.univ hF,
    polarization_smul_second, polarization_smul_third hF,
    htensor t ht, mul_zero, Finset.sum_const_zero]

/-- Evaluation of the explicitly constructed seven coefficient blocks. -/
theorem eval_data_polynomial (hF : F.IsHomogeneous 3)
    (S : HyperbolicBasis.Splitting (hessianBilinear F x) x m q)
    (v : Coordinate m q → K) :
    eval v (polynomial (data hF S)) =
      v (zIndex m q) * v (xIndex m q)^2 +
      v (zIndex m q) * ((1/2 : K) * polarization F
        (blockVector (radicalBlock S) (v ∘ aIndex))
        (blockVector (radicalBlock S) (v ∘ aIndex)) (partner S)) +
      v (xIndex m q) * ((1/2 : K) * polarization F
        (blockVector (middleBlock S) (v ∘ bIndex))
        (blockVector (middleBlock S) (v ∘ bIndex)) x) +
      (1/2 : K) * polarization F
        (blockVector (middleBlock S) (v ∘ bIndex))
        (blockVector (middleBlock S) (v ∘ bIndex))
        (blockVector (radicalBlock S) (v ∘ aIndex)) +
      v (zIndex m q) * polarization F
        (blockVector (radicalBlock S) (v ∘ aIndex))
        (blockVector (middleBlock S) (v ∘ bIndex)) (partner S) +
      v (zIndex m q)^2 * ((1/2 : K) * polarization F
        (blockVector (radicalBlock S) (v ∘ aIndex)) (partner S) (partner S)) +
      eval (blockVector (middleBlock S) (v ∘ bIndex) +
        v (zIndex m q) • partner S) F := by
  classical
  have hR : eval v (rename residualIndex (data hF S).R) =
      eval (blockVector (middleBlock S) (v ∘ bIndex) +
        v (zIndex m q) • partner S) F := by
    rw [eval_rename, data, PolynomialRestriction.eval_restrict, residualMatrix_mulVec]
    rfl
  simp only [polynomial, map_add, map_mul, map_pow, map_sum, eval_C, eval_X,
    eval_rename, data, eval_tensorQuadratic, PolynomialRestriction.eval_restrict,
    residualMatrix_mulVec]
  have hsQ : (∑ i, v (aIndex i) * ((1/2 : K) * polarization F
      (blockVector (middleBlock S) (v ∘ bIndex))
      (blockVector (middleBlock S) (v ∘ bIndex)) (radicalBlock S i))) =
      (1/2 : K) * polarization F
      (blockVector (middleBlock S) (v ∘ bIndex))
      (blockVector (middleBlock S) (v ∘ bIndex))
      (blockVector (radicalBlock S) (v ∘ aIndex)) := by
    simp only [blockVector, polarization_sum_third Finset.univ hF,
      polarization_smul_third hF, Function.comp_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsabz : (∑ i, ∑ j, polarization F (radicalBlock S i)
      (middleBlock S j) (partner S) * v (aIndex i) * v (bIndex j) * v (zIndex m q)) =
      v (zIndex m q) * polarization F
      (blockVector (radicalBlock S) (v ∘ aIndex))
      (blockVector (middleBlock S) (v ∘ bIndex)) (partner S) := by
    simp only [blockVector, polarization_sum_first, polarization_sum_second,
      polarization_smul_first, polarization_smul_second, Function.comp_apply,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hsazz : (∑ i, ((1/2 : K) * polarization F (radicalBlock S i)
      (partner S) (partner S)) * v (aIndex i) * v (zIndex m q)^2) =
      v (zIndex m q)^2 * ((1/2 : K) * polarization F
      (blockVector (radicalBlock S) (v ∘ aIndex)) (partner S) (partner S)) := by
    simp only [blockVector, polarization_sum_first, polarization_smul_first,
      Function.comp_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsQ, hsabz, hsazz]
  rfl

/-- The local normal form is an equality of the actual polynomials. -/
theorem restrict_eq_polynomial_of_tensor_vanishing
    (hF : F.IsHomogeneous 3)
    (S : HyperbolicBasis.Splitting (hessianBilinear F x) x m q)
    (htensor : ∀ t, polynomialDifferential F x t = 0 →
      ∀ i j, polarization F t (radicalBlock S i) (radicalBlock S j) = 0) :
    PolynomialRestriction.restrict (coordinateMatrix S) F = polynomial (data hF S) := by
  apply MvPolynomial.funext
  intro v
  rw [PolynomialRestriction.eval_restrict, coordinateMatrix_mulVec, eval_data_polynomial]
  have hd := blocks_differential_zero hF S (v ∘ aIndex) (v ∘ bIndex)
  have ho := middle_block_orthogonal S (v ∘ bIndex)
  apply eval_hyperbolic_blocks hF S _ _ _ _
    (radical_block_mem_ker S _) ho.1 ho.2
  · exact tensor_radical_blocks_zero hF S htensor _ hd.1 _ _
  · rw [polarization_rotate hF]
    exact tensor_radical_blocks_zero hF S htensor _ hd.2 _ _

/-- The missing tensor blocks follow from the ordinary determinantal tangent
formula for a maximal-rank point, once the actual tangent is the differential
kernel. This version works over any characteristic-zero field. -/
theorem restrict_eq_polynomial_of_determinantal_tangent
    (DT : DeterminantalTangentOver K)
    (hF : F.IsHomogeneous 3)
    (S : HyperbolicBasis.Splitting (hessianBilinear F x) x m q)
    (Z : Set (Fin n → K)) (hx : x ∈ Z)
    (hmax : ∀ y ∈ Z, (hessian F y).rank ≤ (hessian F x).rank)
    (hT : affineTangentSpace Z x = LinearMap.ker (polynomialDifferential F x)) :
    PolynomialRestriction.restrict (coordinateMatrix S) F = polynomial (data hF S) := by
  apply restrict_eq_polynomial_of_tensor_vanishing hF S
  intro t ht i j
  have htZ : t ∈ affineTangentSpace Z x := by
    rw [hT]; exact ht
  have hz := DT.tangent_kernel_pairing (hessianLinearMap F hF) (hessian_symmetric F)
    Z x hx hmax t htZ (radicalBlock S i) (S.radical_hessian_kernel i)
    (radicalBlock S j) (S.radical_hessian_kernel j)
  rw [polarization_swap_first, polarization_swap_last hF]
  exact hz

/-- At a maximal-rank point of an irreducible geometric cubic, the actual
coordinate polynomial has the source's local normal form. -/
theorem restrict_eq_polynomial_of_geometric_generic_rank
    (DT : SymmetricDeterminantalTangentInput)
    {n m q : ℕ} {F : GeometricPolynomial n} {x : GeometricPoint n}
    (hF : F.IsHomogeneous 3) (hirred : Irreducible F) (hx : eval x F = 0)
    (S : HyperbolicBasis.Splitting (hessianBilinear F x) x m q)
    (hmax : ∀ y, eval y F = 0 → (hessian F y).rank ≤ (hessian F x).rank) :
    PolynomialRestriction.restrict (coordinateMatrix S) F = polynomial (data hF S) := by
  apply restrict_eq_polynomial_of_tensor_vanishing hF S
  intro t ht i j
  let Z := zeroLocus GeometricField (Ideal.span ({F} : Set (GeometricPolynomial n)))
  have hxZ : x ∈ Z := by
    apply mem_zeroLocus_iff.mpr
    intro p hp
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hp
    simp [hx]
  have htZ : t ∈ affineTangentSpace Z x := by
    rw [affineTangentSpace_irreducible_hypersurface_eq_ker F hirred x hx]
    exact ht
  have hz := hessian_tangent_polarization_zero DT F hF Z x hxZ
    (fun y hy => hmax y (hy F (Ideal.subset_span (Set.mem_singleton F))))
    t htZ (radicalBlock S i) (S.radical_hessian_kernel i)
    (radicalBlock S j) (S.radical_hessian_kernel j)
  exact hz

/-- The quadratic coefficient matrices are the actual restricted tensors. -/
theorem quadraticMatrix_tensorQuadratic (F : MvPolynomial (Fin n) K)
    (b : Fin q → Fin n → K) (z : Fin n → K) (i j : Fin q) :
    quadraticMatrix (tensorQuadratic F b z) i j = polarization F (b i) (b j) z := by
  classical
  simp [quadraticMatrix, tensorQuadratic, Derivation.leibniz, smul_eq_mul,
    Pi.single_apply, mul_ite, ite_mul, Finset.sum_add_distrib]
  rw [polarization_swap_first F (b j) (b i)]
  ring

theorem Q0_matrix (hF : F.IsHomogeneous 3)
    (S : HyperbolicBasis.Splitting (hessianBilinear F x) x m q) :
    quadraticMatrix (data hF S).Q0 =
      fun i j => hessianBilinear F x (S.basis (bIndex i)) (S.basis (bIndex j)) := by
  ext i j
  simp only [data, quadraticMatrix_tensorQuadratic, hessianBilinear_apply, middleBlock]

/-- The middle quadratic form is nondegenerate by the actual Hessian splitting. -/
theorem Q0_det_ne_zero (hF : F.IsHomogeneous 3)
    (S : HyperbolicBasis.Splitting (hessianBilinear F x) x m q) :
    (quadraticMatrix (data hF S).Q0).det ≠ 0 := by
  rw [Q0_matrix]
  exact S.middle_nonsingular

/-- This coordinate change is an actual vector-space isomorphism. -/
theorem coordinateMatrix_mulVec_eq
    (S : HyperbolicBasis.Splitting (hessianBilinear F x) x m q)
    (v : Coordinate m q → K) :
    (coordinateMatrix S).mulVec v = S.basis.equivFun.symm v := by
  rw [S.basis.equivFun_symm_apply]
  ext i
  simp [coordinateMatrix, Matrix.mulVec, dotProduct, mul_comm]

theorem coordinateMatrix_bijective
    (S : HyperbolicBasis.Splitting (hessianBilinear F x) x m q) :
    Function.Bijective (coordinateMatrix S).mulVec := by
  have heq : (coordinateMatrix S).mulVec = S.basis.equivFun.symm :=
    funext (coordinateMatrix_mulVec_eq S)
  rw [heq]
  exact S.basis.equivFun.symm.bijective

end HessianTheorem11.CubicNormalFormConstruction
