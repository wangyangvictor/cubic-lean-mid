import HessianTheorem11.SingularTupleRadical
import HessianTheorem11.SingularWittWeights
import HessianTheorem11.WittQuadraticTuple
import HessianTheorem11.SingularWittExclusion

/-! Actual ambient coordinates obtained from the radial singleton,
nonradial tangent basis and inverse-Hessian-transformed Witt normal basis. -/
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

noncomputable section
namespace HessianTheorem11.SingularWittCoordinates
open Module MvPolynomial Matrix
variable {n s r l k : ℕ} {T : Finset (Fin n)} {c : Fin n}

/-- Assemble three disjoint coordinate blocks using a proved bijection. -/
def blockCoordinateEquiv (C : GradedIndexCoordinates T c 5 s) :
    ((Fin 5 → GeometricField) × ((Fin s → GeometricField) × (Unit → GeometricField))) ≃ₗ[GeometricField]
      GeometricPoint n where
  toFun z := (Sum.elim z.1 (Sum.elim z.2.1 z.2.2)) ∘ C.equiv.symm
  invFun y := (fun i => y (C.equiv (Sum.inl i)),
    (fun i => y (C.equiv (Sum.inr (Sum.inl i))), fun i => y (C.equiv (Sum.inr (Sum.inr i)))))
  left_inv z := by
    rcases z with ⟨d,a,X⟩
    simp
  right_inv y := by
    funext i
    obtain ⟨j,rfl⟩ := C.equiv.surjective i
    rcases j with j | (j | j) <;> simp
  map_add' z w := by
    funext i
    obtain ⟨j,rfl⟩ := C.equiv.surjective i
    rcases j with j | (j | j) <;> simp
  map_smul' a z := by
    funext i
    obtain ⟨j,rfl⟩ := C.equiv.surjective i
    rcases j with j | (j | j) <;> simp

def reorder :
    (WittSubspaceBasis.Index r l k ⊕ (Fin s ⊕ Unit)) ≃ SingularWittWeights.Index s r l k where
  toFun := Sum.elim SingularWittWeights.normal
    (Sum.elim SingularWittWeights.tangent (fun _ => SingularWittWeights.radial))
  invFun := Sum.elim (fun _ => Sum.inr (Sum.inr ()))
    (Sum.elim (fun i => Sum.inr (Sum.inl i)) Sum.inl)
  left_inv i := by rcases i with i | (i | ⟨⟩) <;> rfl
  right_inv i := by rcases i with ⟨⟩ | (i | i) <;> rfl

def inverseHessianEquiv (Q : Matrix (Fin 5) (Fin 5) GeometricField) (hQ : Q.det ≠ 0) :
    GeometricPoint 5 ≃ₗ[GeometricField] GeometricPoint 5 :=
  LinearEquiv.ofInjectiveEndo Q⁻¹.mulVecLin
    (Matrix.mulVec_injective_iff_isUnit.mpr (Matrix.isUnit_nonsing_inv_iff.mpr
      ((Matrix.isUnit_iff_isUnit_det Q).mpr (isUnit_iff_ne_zero.mpr hQ))))

def ambientBasis
    (b : Basis (Fin n) GeometricField (GeometricPoint n))
    (C : GradedIndexCoordinates T c 5 s)
    (ba : Basis (Fin s) GeometricField (GeometricPoint s))
    (bn : Basis (WittSubspaceBasis.Index r l k) GeometricField (GeometricPoint 5))
    (Q : Matrix (Fin 5) (Fin 5) GeometricField) (hQ : Q.det ≠ 0) :
    Basis (SingularWittWeights.Index s r l k) GeometricField (GeometricPoint n) :=
  ((((bn.map (inverseHessianEquiv Q hQ)).prod (ba.prod (Pi.basisFun GeometricField Unit))).map
    ((blockCoordinateEquiv C).trans b.equivFun.symm)).reindex reorder)

def tangentVector
    (b : Basis (Fin n) GeometricField (GeometricPoint n))
    (C : GradedIndexCoordinates T c 5 s) (a : GeometricPoint s) : GeometricPoint n :=
  b.equivFun.symm (blockCoordinateEquiv C (0,a,0))

def normalVector
    (b : Basis (Fin n) GeometricField (GeometricPoint n))
    (C : GradedIndexCoordinates T c 5 s) (d : GeometricPoint 5) : GeometricPoint n :=
  b.equivFun.symm (blockCoordinateEquiv C (d,0,0))

theorem ambientBasis_radial
    (b : Basis (Fin n) GeometricField (GeometricPoint n))
    (C : GradedIndexCoordinates T c 5 s)
    (ba : Basis (Fin s) GeometricField (GeometricPoint s))
    (bn : Basis (WittSubspaceBasis.Index r l k) GeometricField (GeometricPoint 5))
    (Q : Matrix (Fin 5) (Fin 5) GeometricField) (hQ : Q.det ≠ 0) :
    ambientBasis b C ba bn Q hQ SingularWittWeights.radial = b c := by
  have hr : (reorder (s := s) (r := r) (l := l) (k := k)).symm SingularWittWeights.radial =
      Sum.inr (Sum.inr ()) := rfl
  rw [ambientBasis, Basis.reindex_apply, hr]
  simp only [Basis.map_apply, Basis.prod_apply, Sum.elim_inr, Function.comp_apply,
    LinearMap.inr_apply, LinearEquiv.trans_apply]
  change b.equivFun.symm (blockCoordinateEquiv C (0,0,(Pi.basisFun GeometricField Unit) ())) = b c
  have he : blockCoordinateEquiv C (0,0,(Pi.basisFun GeometricField Unit) ()) = Pi.single c 1 := by
    funext i
    obtain ⟨j,rfl⟩ := C.equiv.surjective i
    rcases j with j | (j | j)
    · have hj : C.equiv (Sum.inl j) ≠ c := by
        intro h
        have he := C.equiv.injective (h.trans C.radial_apply.symm)
        cases he
      simp [blockCoordinateEquiv, Pi.single_apply, hj]
    · have hj : C.equiv (Sum.inr (Sum.inl j)) ≠ c := by
        intro h
        have he := C.equiv.injective (h.trans C.radial_apply.symm)
        cases he
      simp [blockCoordinateEquiv, Pi.single_apply, hj]
    · have hz : blockCoordinateEquiv C (0,0,(Pi.basisFun GeometricField Unit) ())
          (C.equiv (Sum.inr (Sum.inr j))) = 1 := by
        simp [blockCoordinateEquiv, Pi.basisFun_apply]
        rw [C.equiv.symm_apply_apply]
        simp
      have hj : j = () := Subsingleton.elim _ _
      have hc : C.equiv (Sum.inr (Sum.inr j)) = c := by
        simpa only [hj] using C.radial_apply
      rw [hz, hc]
      simp
  rw [he]
  rw [← BasisHessianTransport.basisMatrix_mulVec_eq]
  exact HessianTheorem11.basisMatrix_mulVec_single b c

theorem ambientBasis_tangent
    (b : Basis (Fin n) GeometricField (GeometricPoint n))
    (C : GradedIndexCoordinates T c 5 s)
    (ba : Basis (Fin s) GeometricField (GeometricPoint s))
    (bn : Basis (WittSubspaceBasis.Index r l k) GeometricField (GeometricPoint 5))
    (Q : Matrix (Fin 5) (Fin 5) GeometricField) (hQ : Q.det ≠ 0) (i : Fin s) :
    ambientBasis b C ba bn Q hQ (SingularWittWeights.tangent i) = tangentVector b C (ba i) := by
  simp [ambientBasis, Basis.prod_apply, reorder, SingularWittWeights.tangent, tangentVector]

theorem ambientBasis_normal
    (b : Basis (Fin n) GeometricField (GeometricPoint n))
    (C : GradedIndexCoordinates T c 5 s)
    (ba : Basis (Fin s) GeometricField (GeometricPoint s))
    (bn : Basis (WittSubspaceBasis.Index r l k) GeometricField (GeometricPoint 5))
    (Q : Matrix (Fin 5) (Fin 5) GeometricField) (hQ : Q.det ≠ 0) (i : WittSubspaceBasis.Index r l k) :
    ambientBasis b C ba bn Q hQ (SingularWittWeights.normal i) = normalVector b C (Q⁻¹.mulVec (bn i)) := by
  simp [ambientBasis, Basis.prod_apply, reorder, SingularWittWeights.normal, normalVector,
    inverseHessianEquiv]
  rfl

def tangentMatrix (b : Basis (Fin n) GeometricField (GeometricPoint n))
    (C : GradedIndexCoordinates T c 5 s) : Matrix (Fin n) (Fin s) GeometricField :=
  fun i j => b (C.tangent j) i

def normalMatrix (b : Basis (Fin n) GeometricField (GeometricPoint n))
    (C : GradedIndexCoordinates T c 5 s) : Matrix (Fin n) (Fin 5) GeometricField :=
  fun i j => b (C.normal j) i

theorem tangentVector_eq_sum
    (b : Basis (Fin n) GeometricField (GeometricPoint n))
    (C : GradedIndexCoordinates T c 5 s) (a : GeometricPoint s) :
    tangentVector b C a = ∑ i, a i • b (C.tangent i) := by
  rw [tangentVector, Basis.equivFun_symm_apply]
  rw [← C.equiv.sum_comp (fun i => blockCoordinateEquiv C (0,a,0) i • b i)]
  simp only [blockCoordinateEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, Function.comp_apply, C.equiv.symm_apply_apply,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
    zero_smul, Finset.sum_const_zero, zero_add, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [show C.equiv (Sum.inr (Sum.inl i)) = (C.tangent i : Fin n) from C.tangent_apply i]

theorem normalVector_eq_sum
    (b : Basis (Fin n) GeometricField (GeometricPoint n))
    (C : GradedIndexCoordinates T c 5 s) (d : GeometricPoint 5) :
    normalVector b C d = ∑ i, d i • b (C.normal i) := by
  rw [normalVector, Basis.equivFun_symm_apply]
  rw [← C.equiv.sum_comp (fun i => blockCoordinateEquiv C (d,0,0) i • b i)]
  simp [blockCoordinateEquiv, Fintype.sum_sum_type, C.normal_apply]

theorem tangentVector_eq_mulVec
    (b : Basis (Fin n) GeometricField (GeometricPoint n))
    (C : GradedIndexCoordinates T c 5 s) (a : GeometricPoint s) :
    tangentVector b C a = (tangentMatrix b C).mulVec a := by
  rw [tangentVector_eq_sum]
  ext i
  simp [tangentMatrix, Matrix.mulVec, dotProduct, mul_comm]

theorem normalVector_eq_mulVec
    (b : Basis (Fin n) GeometricField (GeometricPoint n))
    (C : GradedIndexCoordinates T c 5 s) (d : GeometricPoint 5) :
    normalVector b C d = (normalMatrix b C).mulVec d := by
  rw [normalVector_eq_sum]
  ext i
  simp [normalMatrix, Matrix.mulVec, dotProduct, mul_comm]

theorem block_tangent_eq_extension
    (C : GradedIndexCoordinates T c 5 s) (a : GeometricPoint s) :
    blockCoordinateEquiv C (0,a,0) =
      SingularNormalPairing.blockExtension (T.erase c) (a ∘ C.tangent.symm) := by
  funext i
  obtain ⟨j,rfl⟩ := C.equiv.surjective i
  simp only [blockCoordinateEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, Function.comp_apply, C.equiv.symm_apply_apply]
  rcases j with j | (j | j)
  · have hj : (C.normal j : Fin n) ∉ T.erase c := by
      intro h
      exact Finset.mem_compl.mp (C.normal j).property (Finset.mem_of_mem_erase h)
    change (0 : GeometricField) = _
    rw [C.normal_apply, SingularNormalPairing.blockExtension_zero _ _ _ hj]
  · change a j = _
    rw [show C.equiv (Sum.inr (Sum.inl j)) = (C.tangent j : Fin n) from C.tangent_apply j,
      SingularNormalPairing.blockExtension_coe]
    simp
  · cases j
    change (0 : GeometricField) = _
    rw [show C.equiv (Sum.inr (Sum.inr ())) = c from C.radial_apply,
      SingularNormalPairing.blockExtension_zero _ _ _ (Finset.notMem_erase _ _)]

theorem tangentVector_eq_extension
    (b : Basis (Fin n) GeometricField (GeometricPoint n))
    (C : GradedIndexCoordinates T c 5 s) (a : GeometricPoint s) :
    tangentVector b C a = (HessianTheorem11.basisMatrix b).mulVec
      (SingularNormalPairing.blockExtension (T.erase c) (a ∘ C.tangent.symm)) := by
  rw [tangentVector, block_tangent_eq_extension, ← BasisHessianTransport.basisMatrix_mulVec_eq]
  rfl

theorem finite_normal_tuple_linearGradient
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3) (x : GeometricPoint n)
    (T₀ L : Submodule GeometricField (GeometricPoint n)) (A : AdaptedFlagBasis T₀ L x)
    (hW : HasNonnegativeWeights (PolynomialRestriction.restrict (HessianTheorem11.basisMatrix A.basis) F)
      (singularRadialWeight A.radial A.tangentIndices A.tangentIndices))
    (p : (↑A.tangentIndicesᶜ : Type) →
      MvPolynomial (↑(A.tangentIndices.erase A.radial) : Type) GeometricField)
    (hpe : ∀ i, rename (fun j : (↑(A.tangentIndices.erase A.radial) : Type) => (j : Fin n)) (p i) =
      SingularRadialNormalForm.normalMapComponent
        (NonzeroLimitTransport.zeroWeightPart
          (PolynomialRestriction.restrict (HessianTheorem11.basisMatrix A.basis) F)
          (singularRadialWeight A.radial A.tangentIndices A.tangentIndices))
        A.radial A.tangentIndices i)
    (C₀ : GradedIndexCoordinates A.tangentIndices A.radial 5 s) :
    C₀.normalTuple p = fun i => ∑ k, C (normalMatrix A.basis C₀ k i) *
      PolynomialRestriction.restrict (tangentMatrix A.basis C₀) (pderiv k F) := by
  classical
  have hp := SingularNormalPairing.normal_tuple_linearGradient F hF x T₀ L A hW p hpe
  funext i
  apply MvPolynomial.funext
  intro a
  change eval a (rename C₀.tangent.symm (p (C₀.normal i))) = _
  rw [eval_rename, congrFun hp (C₀.normal i)]
  simp only [map_sum, map_mul, eval_C, PolynomialRestriction.eval_restrict]
  have hv : ((HessianTheorem11.basisMatrix A.basis) *
      (QuadraticBlockRank.renamingMatrix (K := GeometricField)
        (fun j : (↑(A.tangentIndices.erase A.radial) : Type) => (j : Fin n))).transpose).mulVec
        (a ∘ C₀.tangent.symm) = (tangentMatrix A.basis C₀).mulVec a := by
    rw [← Matrix.mulVec_mulVec, SingularNormalPairing.transpose_renaming_mulVec_eq_blockExtension,
      ← tangentVector_eq_extension, tangentVector_eq_mulVec]
  rw [hv]
  rfl

theorem quadraticHessian_rename_entry {σ τ : Type*}
    (f : σ → τ) (hf : Function.Injective f) (q : MvPolynomial σ GeometricField) (i j : σ) :
    SingularNormalEquations.quadraticHessian (rename f q) (f i) (f j) =
      SingularNormalEquations.quadraticHessian q i j := by
  change coeff 0 (pderiv (f j) (pderiv (f i) (rename f q))) =
    coeff 0 (pderiv j (pderiv i q))
  rw [pderiv_rename hf, pderiv_rename hf]
  simpa only [Finsupp.mapDomain_zero] using
    coeff_rename_mapDomain f hf (pderiv j (pderiv i q)) 0

theorem normal_hessian_matrix
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3) (x : GeometricPoint n)
    (T₀ L : Submodule GeometricField (GeometricPoint n)) (A : AdaptedFlagBasis T₀ L x)
    (hW : HasNonnegativeWeights (PolynomialRestriction.restrict (HessianTheorem11.basisMatrix A.basis) F)
      (singularRadialWeight A.radial A.tangentIndices A.tangentIndices))
    (q : MvPolynomial (↑A.tangentIndicesᶜ : Type) GeometricField)
    (hqe : rename (fun i : (↑A.tangentIndicesᶜ : Type) => (i : Fin n)) q =
      SingularRadialNormalForm.normalQuadratic
        (NonzeroLimitTransport.zeroWeightPart
          (PolynomialRestriction.restrict (HessianTheorem11.basisMatrix A.basis) F)
          (singularRadialWeight A.radial A.tangentIndices A.tangentIndices)) A.radial)
    (C₀ : GradedIndexCoordinates A.tangentIndices A.radial 5 s) :
    (normalMatrix A.basis C₀).transpose * hessian F x * normalMatrix A.basis C₀ =
      SingularNormalEquations.quadraticHessian (C₀.normalPolynomial q) := by
  let P := PolynomialRestriction.restrict (HessianTheorem11.basisMatrix A.basis) F
  have hP : P.IsHomogeneous 3 := PolynomialRestriction.homogeneous_restrict _ _ hF
  have he := SingularPositiveNormalForm.retained_normalQuadratic_hessian P hP
    A.radial A.tangentIndices A.radial_mem hW
  rw [PolynomialRestriction.hessian_restrict, HessianTheorem11.basisMatrix_mulVec_single,
    A.radial_eq] at he
  rw [C₀.normalPolynomial_hessian]
  ext i j
  change _ = SingularNormalEquations.quadraticHessian q (C₀.normal i) (C₀.normal j)
  rw [← quadraticHessian_rename_entry (fun i : (↑A.tangentIndicesᶜ : Type) => (i : Fin n))
    Subtype.val_injective q (C₀.normal i) (C₀.normal j), hqe]
  change _ = LocalCubicNormalForm.quadraticMatrix
    (SingularRadialNormalForm.normalQuadratic (NonzeroLimitTransport.zeroWeightPart P _) A.radial)
      (C₀.normal i) (C₀.normal j)
  rw [he]
  rfl

theorem normal_tensor_of_linearGradient
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (b : Basis (Fin n) GeometricField (GeometricPoint n))
    (C₀ : GradedIndexCoordinates T c 5 s)
    (p : Fin 5 → GeometricPolynomial s)
    (hp : p = fun i => ∑ k, C (normalMatrix b C₀ k i) *
      PolynomialRestriction.restrict (tangentMatrix b C₀) (pderiv k F))
    (a a' : GeometricPoint s) (d : GeometricPoint 5) :
    polarization F (tangentVector b C₀ a) (tangentVector b C₀ a') (normalVector b C₀ d) =
      dotProduct d ((TangentHessianRank.polynomialJacobian p a').mulVec a) := by
  have hJ : TangentHessianRank.polynomialJacobian p a' =
      (normalMatrix b C₀).transpose * hessian F ((tangentMatrix b C₀).mulVec a') * tangentMatrix b C₀ := by
    rw [hp]
    exact SingularNormalPairing.linearGradient_jacobian F (tangentMatrix b C₀)
      (normalMatrix b C₀).transpose a'
  rw [polarization_rotate hF]
  unfold polarization
  rw [normalVector_eq_mulVec, tangentVector_eq_mulVec, tangentVector_eq_mulVec, hJ,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  conv_rhs => rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem normal_tensor_inverse_pairing
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (b : Basis (Fin n) GeometricField (GeometricPoint n))
    (C₀ : GradedIndexCoordinates T c 5 s)
    (p : Fin 5 → GeometricPolynomial s)
    (hp : p = fun i => ∑ k, C (normalMatrix b C₀ k i) *
      PolynomialRestriction.restrict (tangentMatrix b C₀) (pderiv k F))
    (Q : Matrix (Fin 5) (Fin 5) GeometricField) (hQ : Q.IsSymm)
    (a a' : GeometricPoint s) (d : GeometricPoint 5) :
    polarization F (tangentVector b C₀ a) (tangentVector b C₀ a')
      (normalVector b C₀ (Q⁻¹.mulVec d)) =
      polynomialDifferential (WittQuadraticTuple.scalarTuple ((Matrix.toBilin' Q⁻¹) d) p) a' a := by
  rw [normal_tensor_of_linearGradient F hF b C₀ p hp,
    WittQuadraticTuple.polynomialDifferential_scalarTuple, Matrix.toBilin'_apply']
  change dotProduct (Q⁻¹.mulVec d) _ = dotProduct d (Q⁻¹.mulVec _)
  conv_rhs => rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    Matrix.transpose_nonsing_inv, hQ.eq]

theorem radial_tensor_inverse_pairing
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3) (x : GeometricPoint n)
    (b : Basis (Fin n) GeometricField (GeometricPoint n))
    (C₀ : GradedIndexCoordinates T c 5 s)
    (Q : Matrix (Fin 5) (Fin 5) GeometricField) (hQ : Q.IsSymm) (hdet : Q.det ≠ 0)
    (hH : (normalMatrix b C₀).transpose * hessian F x * normalMatrix b C₀ = Q)
    (d d' : GeometricPoint 5) :
    polarization F x (normalVector b C₀ (Q⁻¹.mulVec d)) (normalVector b C₀ (Q⁻¹.mulVec d')) =
      Matrix.toBilin' Q⁻¹ d d' := by
  rw [polarization_rotate hF, polarization_rotate hF]
  unfold polarization
  rw [normalVector_eq_mulVec, normalVector_eq_mulVec]
  have he : (normalMatrix b C₀).transpose.mulVec
      ((hessian F x).mulVec ((normalMatrix b C₀).mulVec (Q⁻¹.mulVec d'))) = d' := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hH, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv Q (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
  calc
    _ = dotProduct (Q⁻¹.mulVec d)
        ((normalMatrix b C₀).transpose.mulVec
          ((hessian F x).mulVec ((normalMatrix b C₀).mulVec (Q⁻¹.mulVec d')))) := by
      conv_rhs => rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    _ = dotProduct (Q⁻¹.mulVec d) d' := by rw [he]
    _ = _ := by
      rw [Matrix.toBilin'_apply', Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
        Matrix.transpose_nonsing_inv, hQ.eq]

/-- Construct the concrete tensor coordinates consumed by the isotropic
weight proof. No tensor-coordinate existence premise is retained. -/
theorem exists_coordinates
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3) (x : GeometricPoint n)
    (T₀ : Submodule GeometricField (GeometricPoint n))
    (A : AdaptedFlagBasis T₀ (LinearMap.ker (hessian F x).mulVecLin) x)
    (hT : T₀ = LinearMap.ker (hessian F x).mulVecLin)
    (htensor : ∀ t ∈ T₀, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0)
    (q : MvPolynomial (↑A.tangentIndicesᶜ : Type) GeometricField)
    (p : (↑A.tangentIndicesᶜ : Type) →
      MvPolynomial (↑(A.tangentIndices.erase A.radial) : Type) GeometricField)
    (hqe : rename (fun i : (↑A.tangentIndicesᶜ : Type) => (i : Fin n)) q =
      SingularRadialNormalForm.normalQuadratic
        (NonzeroLimitTransport.zeroWeightPart
          (PolynomialRestriction.restrict (HessianTheorem11.basisMatrix A.basis) F)
          (singularRadialWeight A.radial A.tangentIndices A.tangentIndices)) A.radial)
    (hpe : ∀ i, rename (fun j : (↑(A.tangentIndices.erase A.radial) : Type) => (j : Fin n)) (p i) =
      SingularRadialNormalForm.normalMapComponent
        (NonzeroLimitTransport.zeroWeightPart
          (PolynomialRestriction.restrict (HessianTheorem11.basisMatrix A.basis) F)
          (singularRadialWeight A.radial A.tangentIndices A.tangentIndices))
        A.radial A.tangentIndices i)
    (C₀ : GradedIndexCoordinates A.tangentIndices A.radial 5 s)
    {U : Submodule GeometricField (GeometricPoint 5)}
    (D : WittSubspaceBasis.Data
      (Matrix.toBilin' (SingularNormalEquations.quadraticHessian (C₀.normalPolynomial q))⁻¹) U r l k)
    (ba : Basis (Fin s) GeometricField (GeometricPoint s)) :
    Nonempty (SingularWittExclusion.Coordinates F D (C₀.normalTuple p) ba) := by
  let Q := SingularNormalEquations.quadraticHessian (C₀.normalPolynomial q)
  have hdet : Q.det ≠ 0 := C₀.normalPolynomial_det_ne_zero q
    (SingularPositiveNormalForm.typed_normal_det_ne_zero_in_adapted_flag F hF x T₀ A hT htensor q hqe)
  have hQ : Q.IsSymm := GradedCubic.quadraticHessian_symm _
  let b := ambientBasis A.basis C₀ ba D.basis Q hdet
  have hxT : x ∈ T₀ := by
    have h := (A.mem_tangent_iff A.radial).mpr A.radial_mem
    rwa [A.radial_eq] at h
  have ht (a : GeometricPoint s) : tangentVector A.basis C₀ a ∈ T₀ := by
    rw [tangentVector_eq_extension]
    exact SingularNormalPairing.blockExtension_in_tangent T₀ _ x A (a ∘ C₀.tangent.symm)
  have hr : b SingularWittWeights.radial = x :=
    (ambientBasis_radial A.basis C₀ ba D.basis Q hdet).trans A.radial_eq
  have ht' (i : Fin s) : b (SingularWittWeights.tangent i) = tangentVector A.basis C₀ (ba i) :=
    ambientBasis_tangent A.basis C₀ ba D.basis Q hdet i
  have hn (i : WittSubspaceBasis.Index r l k) : b (SingularWittWeights.normal i) =
      normalVector A.basis C₀ (Q⁻¹.mulVec (D.basis i)) :=
    ambientBasis_normal A.basis C₀ ba D.basis Q hdet i
  have hW := SingularRadialEquality.nonnegative_in_adapted_flag F hF x T₀ A htensor
  rw [← SingularPositiveNormalForm.adapted_indices_eq_of_tangent_eq_kernel F x T₀ A hT] at hW
  refine ⟨{ basis := b
            radial_kernel := ?_
            tangent_kernel := ?_
            tangent_tensor := ?_
            radial_tensor := ?_
            normal_tensor := ?_ }⟩
  · rw [hr]
    exact hT.le hxT
  · intro i
    rw [hr, ht']
    exact hT.le (ht _)
  · intro i j a
    rw [ht', ht', ht']
    exact htensor _ (ht _) _ (hT.le (ht _)) _ (hT.le (ht _))
  · intro i j
    rw [hr, hn, hn]
    exact radial_tensor_inverse_pairing F hF x A.basis C₀ Q hQ hdet
      (normal_hessian_matrix F hF x T₀ _ A hW q hqe C₀) (D.basis i) (D.basis j)
  · intro i j a
    rw [ht', ht', hn]
    exact normal_tensor_inverse_pairing F hF A.basis C₀ (C₀.normalTuple p)
      (finite_normal_tuple_linearGradient F hF x T₀ _ A hW p hpe C₀) Q hQ (ba i) (ba j) (D.basis a)

end HessianTheorem11.SingularWittCoordinates
