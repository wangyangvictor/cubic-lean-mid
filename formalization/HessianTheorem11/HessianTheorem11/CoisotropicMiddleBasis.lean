import HessianTheorem11.RadicalPencilCoordinates

/-! Change only the middle block of the constructed coisotropic basis. -/
noncomputable section
namespace HessianTheorem11
open Matrix Module
namespace CoisotropicBasis.Data
variable {n m d q : ℕ} {F : GeometricPolynomial n} {x : GeometricPoint n}
  {T : Submodule GeometricField (GeometricPoint n)}
  (D : Data (hessianBilinear F x) T x m d q)

def middleMatrix : Matrix (Fin n) (Fin q) GeometricField := fun i j => D.middleVector j i

theorem middleMatrix_mulVec_sum (v : GeometricPoint q) :
    D.middleMatrix.mulVec v = ∑i,v i • D.middleVector i := by
  ext j
  simp [middleMatrix,Matrix.mulVec,dotProduct,mul_comm]

theorem middleMatrix_mulVec_coordinates (v : GeometricPoint q) :
    D.middleMatrix.mulVec v = D.basis.equivFun.symm (Sum.elim 0 (Sum.elim v 0)) := by
  rw [← BasisHessianTransport.basisMatrix_mulVec_eq]
  ext i
  simp [middleMatrix,middleVector,Matrix.mulVec,dotProduct,
    BasisHessianTransport.basisMatrix,Fintype.sum_sum_type]

def middleComplementBasis (b : Basis (Fin q) GeometricField (GeometricPoint q)) :
    Basis (CoisotropicBasis.NondegenerateIndex d q) GeometricField
      (CoisotropicBasis.NondegenerateIndex d q → GeometricField) :=
  (b.prod (Pi.basisFun GeometricField (Fin d ⊕ Fin d))).map
    (LinearEquiv.sumArrowLequivProdArrow (Fin q) (Fin d ⊕ Fin d)
      GeometricField GeometricField).symm

def middleRebasedBasis (b : Basis (Fin q) GeometricField (GeometricPoint q)) :
    Basis (CoisotropicBasis.Index m d q) GeometricField (GeometricPoint n) :=
  ((Pi.basisFun GeometricField (Fin m)).prod (middleComplementBasis (d:=d) b)).map
    ((LinearEquiv.sumArrowLequivProdArrow (Fin m) (CoisotropicBasis.NondegenerateIndex d q)
      GeometricField GeometricField).symm.trans D.basis.equivFun.symm)

theorem middleRebasedBasis_middle (b : Basis (Fin q) GeometricField (GeometricPoint q)) (i : Fin q) :
    D.middleRebasedBasis b (Sum.inr (Sum.inl i)) = D.middleMatrix.mulVec (b i) := by
  rw [D.middleMatrix_mulVec_coordinates]
  simp [middleRebasedBasis,middleComplementBasis,Basis.prod_apply,
    LinearEquiv.sumArrowLequivProdArrow]

theorem middleRebasedBasis_radical (b : Basis (Fin q) GeometricField (GeometricPoint q)) (i : Fin m) :
    D.middleRebasedBasis b (Sum.inl i) = D.basis (Sum.inl i) := by
  simp only [middleRebasedBasis,Basis.map_apply,Basis.prod_apply,Sum.elim_inl,
    Function.comp_apply,LinearMap.inl_apply,LinearEquiv.trans_apply]
  have he : (LinearEquiv.sumArrowLequivProdArrow (Fin m) (CoisotropicBasis.NondegenerateIndex d q)
      GeometricField GeometricField).symm ((Pi.basisFun GeometricField _) i,0) =
      Pi.single (Sum.inl i) 1 := by
    funext j
    cases j <;> simp [Pi.basisFun_apply,Pi.single_apply]
  rw [he]
  simp [Basis.equivFun_symm_apply]

theorem middleRebasedBasis_final (b : Basis (Fin q) GeometricField (GeometricPoint q))
    (i : Fin d ⊕ Fin d) :
    D.middleRebasedBasis b (Sum.inr (Sum.inr i)) = D.basis (Sum.inr (Sum.inr i)) := by
  simp only [middleRebasedBasis,middleComplementBasis,Basis.map_apply,Basis.prod_apply,
    Sum.elim_inr,Function.comp_apply,LinearMap.inr_apply,LinearEquiv.trans_apply]
  have he : (LinearEquiv.sumArrowLequivProdArrow (Fin m) (CoisotropicBasis.NondegenerateIndex d q)
      GeometricField GeometricField).symm (0,
        (LinearEquiv.sumArrowLequivProdArrow (Fin q) (Fin d ⊕ Fin d)
          GeometricField GeometricField).symm (0,(Pi.basisFun GeometricField _) i)) =
      Pi.single (Sum.inr (Sum.inr i)) 1 := by
    funext j
    rcases j with j|(j|j) <;> simp [Pi.basisFun_apply,Pi.single_apply]
  rw [he]
  simp [Basis.equivFun_symm_apply]

theorem middleRebasedGram (b : Basis (Fin q) GeometricField (GeometricPoint q)) :
    (fun i j => hessianBilinear F x (D.middleRebasedBasis b (Sum.inr (Sum.inl i)))
      (D.middleRebasedBasis b (Sum.inr (Sum.inl j)))) =
      (BasisHessianTransport.basisMatrix b).transpose*D.middleGram*
        BasisHessianTransport.basisMatrix b := by
  classical
  ext i j
  rw [D.middleRebasedBasis_middle,D.middleRebasedBasis_middle,hessianBilinear_apply,
    D.middleMatrix_mulVec_sum,D.middleMatrix_mulVec_sum]
  simp only [polarization_sum_first,polarization_sum_second,polarization_smul_first,
    polarization_smul_second,Matrix.mul_apply,Matrix.transpose_apply,
    BasisHessianTransport.basisMatrix,middleGram,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

def rebaseMiddle (b : Basis (Fin q) GeometricField (GeometricPoint q)) :
    Data (hessianBilinear F x) T x m d q where
  basis := D.middleRebasedBasis b
  radial := D.radial
  radial_eq := (D.middleRebasedBasis_final b _).trans D.radial_eq
  radical_dimension := D.radical_dimension
  codimension := D.codimension
  dimension := D.dimension
  radical_vectors i := by rw [D.middleRebasedBasis_radical]; exact D.radical_vectors i
  tangent_middle i := by
    rw [D.middleRebasedBasis_middle,D.middleMatrix_mulVec_sum]
    apply T.sum_mem
    intro j _
    exact T.smul_mem _ (D.tangent_middle j)
  tangent_isotropic i := by rw [D.middleRebasedBasis_final]; exact D.tangent_isotropic i
  isotropic_left i j := by
    rw [D.middleRebasedBasis_final,D.middleRebasedBasis_final]
    exact D.isotropic_left i j
  isotropic_right i j := by
    rw [D.middleRebasedBasis_final,D.middleRebasedBasis_final]
    exact D.isotropic_right i j
  pairing i j := by
    rw [D.middleRebasedBasis_final,D.middleRebasedBasis_final]
    exact D.pairing i j
  middle_orthogonal_left i j := by
    rw [D.middleRebasedBasis_middle,D.middleRebasedBasis_final,D.middleMatrix_mulVec_sum]
    simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply]
    apply Finset.sum_eq_zero
    intro k _
    change _ • hessianBilinear F x (D.middleVector k) (D.isotropicVector j)=0
    rw [middleVector,isotropicVector,D.middle_orthogonal_left]
    exact smul_zero _
  middle_orthogonal_right i j := by
    rw [D.middleRebasedBasis_middle,D.middleRebasedBasis_final,D.middleMatrix_mulVec_sum]
    simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply]
    apply Finset.sum_eq_zero
    intro k _
    change _ • hessianBilinear F x (D.middleVector k) (D.dualVector j)=0
    rw [middleVector,dualVector,D.middle_orthogonal_right]
    exact smul_zero _
  middle_nonsingular := by
    rw [D.middleRebasedGram,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose]
    have hb : (BasisHessianTransport.basisMatrix b).det≠0 := by
      apply isUnit_iff_ne_zero.mp
      apply (Matrix.isUnit_iff_isUnit_det _).mp
      apply Matrix.mulVec_injective_iff_isUnit.mp
      intro u v h
      rw [BasisHessianTransport.basisMatrix_mulVec_eq,
        BasisHessianTransport.basisMatrix_mulVec_eq] at h
      exact b.equivFun.symm.injective h
    exact mul_ne_zero (mul_ne_zero hb D.middleGram_det_ne_zero) hb

end CoisotropicBasis.Data
end HessianTheorem11
