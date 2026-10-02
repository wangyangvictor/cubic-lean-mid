import HessianTheorem11.RadicalPencilCoordinates

/-! Refine the radical basis while preserving every coisotropic Gram block
and the prescribed radial vector. -/
noncomputable section
namespace HessianTheorem11
open Matrix Module
namespace CoisotropicBasis.Data
variable {n m d q : ℕ} {F : GeometricPolynomial n} {x : GeometricPoint n}
  {T : Submodule GeometricField (GeometricPoint n)}
  (D : Data (hessianBilinear F x) T x m d q)

def radicalRebasedBasis (ba : Basis (Fin m) GeometricField (GeometricPoint m)) :
    Basis (CoisotropicBasis.Index m d q) GeometricField (GeometricPoint n) :=
  (ba.prod (Pi.basisFun GeometricField (CoisotropicBasis.NondegenerateIndex d q))).map
    ((LinearEquiv.sumArrowLequivProdArrow (Fin m) (CoisotropicBasis.NondegenerateIndex d q)
      GeometricField GeometricField).symm.trans D.basis.equivFun.symm)

theorem radicalRebasedBasis_radical
    (ba : Basis (Fin m) GeometricField (GeometricPoint m)) (i : Fin m) :
    D.radicalRebasedBasis ba (Sum.inl i) = D.radicalMatrix.mulVec (ba i) := by
  rw [D.radicalMatrix_mulVec]
  simp [radicalRebasedBasis, Basis.prod_apply, LinearEquiv.sumArrowLequivProdArrow]

theorem radicalRebasedBasis_complement
    (ba : Basis (Fin m) GeometricField (GeometricPoint m))
    (i : CoisotropicBasis.NondegenerateIndex d q) :
    D.radicalRebasedBasis ba (Sum.inr i) = D.basis (Sum.inr i) := by
  simp only [radicalRebasedBasis, Basis.map_apply, Basis.prod_apply, Sum.elim_inr,
    Function.comp_apply, LinearMap.inr_apply, LinearEquiv.trans_apply]
  have he : (LinearEquiv.sumArrowLequivProdArrow (Fin m) (CoisotropicBasis.NondegenerateIndex d q)
      GeometricField GeometricField).symm (0, (Pi.basisFun GeometricField _) i) =
      Pi.single (Sum.inr i) 1 := by
    funext j
    rcases j with j | j <;> simp [Pi.basisFun_apply, Pi.single_apply]
  rw [he]
  simp [Basis.equivFun_symm_apply]

/-- This is the same geometric flag with a new actual basis of its radical. -/
def rebaseRadical (ba : Basis (Fin m) GeometricField (GeometricPoint m)) :
    Data (hessianBilinear F x) T x m d q where
  basis := D.radicalRebasedBasis ba
  radial := D.radial
  radial_eq := (D.radicalRebasedBasis_complement ba _).trans D.radial_eq
  radical_dimension := D.radical_dimension
  codimension := D.codimension
  dimension := D.dimension
  radical_vectors i := by
    rw [D.radicalRebasedBasis_radical ba i, ker_hessianBilinear]
    exact D.radicalMatrix_mem_kernel (ba i)
  tangent_middle i := by
    rw [D.radicalRebasedBasis_complement ba _]
    exact D.tangent_middle i
  tangent_isotropic i := by
    rw [D.radicalRebasedBasis_complement ba _]
    exact D.tangent_isotropic i
  isotropic_left i j := by
    rw [D.radicalRebasedBasis_complement ba _, D.radicalRebasedBasis_complement ba _]
    exact D.isotropic_left i j
  isotropic_right i j := by
    rw [D.radicalRebasedBasis_complement ba _, D.radicalRebasedBasis_complement ba _]
    exact D.isotropic_right i j
  pairing i j := by
    rw [D.radicalRebasedBasis_complement ba _, D.radicalRebasedBasis_complement ba _]
    exact D.pairing i j
  middle_orthogonal_left i j := by
    rw [D.radicalRebasedBasis_complement ba _, D.radicalRebasedBasis_complement ba _]
    exact D.middle_orthogonal_left i j
  middle_orthogonal_right i j := by
    rw [D.radicalRebasedBasis_complement ba _, D.radicalRebasedBasis_complement ba _]
    exact D.middle_orthogonal_right i j
  middle_nonsingular := by
    simpa only [D.radicalRebasedBasis_complement ba] using D.middle_nonsingular

end CoisotropicBasis.Data
end HessianTheorem11
