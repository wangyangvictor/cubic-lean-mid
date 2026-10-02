import CubicTenVariables.CubicFourSingularCoordinates
import CubicTenVariables.CubicSurfaceProjectiveSingular

/-! Literal coordinate transport of an integral cubic surface by an actual
linear equivalence. This supplies the four-point frame application over any
infinite field, not just the project's fixed algebraic closure. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.CubicSurfaceSingularCoordinateTransport
open MvPolynomial HessianTheorem11
open PolynomialRestriction CubicSurfaceProjectiveSingular CubicFourSingularCoordinates
open scoped BigOperators
variable {K : Type*} [Field K] [Infinite K]

def coordinateMatrix (e : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) : Matrix (Fin 4) (Fin 4) K :=
  pointMatrix (fun i => e (Pi.single i 1))

@[simp] theorem coordinateMatrix_mulVec
    (e : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) (x : Fin 4 → K) :
    (coordinateMatrix e).mulVec x = e x := by
  have hx : x = ∑ i : Fin 4, x i • (Pi.single i (1 : K) : Fin 4 → K) := by
    ext j
    simp [Pi.single_apply]
  conv_rhs => rw [hx,map_sum]
  ext j
  simp [coordinateMatrix,pointMatrix,Matrix.mulVec,dotProduct,smul_eq_mul,mul_comm]

private theorem restrict_inverse
    (e : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) (F : MvPolynomial (Fin 4) K) :
    restrict (coordinateMatrix e) (restrict (coordinateMatrix e.symm) F) = F := by
  apply MvPolynomial.funext
  intro x
  rw [eval_restrict,coordinateMatrix_mulVec,eval_restrict,coordinateMatrix_mulVec,
    LinearEquiv.symm_apply_apply]

/-- The polynomial pullback is an actual algebra equivalence. -/
def coordinateAlgEquiv (e : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) :
    MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K :=
  AlgEquiv.ofAlgHom (aeval (linearForms (coordinateMatrix e)))
    (aeval (linearForms (coordinateMatrix e.symm)))
    (by apply MvPolynomial.algHom_ext; intro i; exact restrict_inverse e (X i))
    (by apply MvPolynomial.algHom_ext; intro i; exact restrict_inverse e.symm (X i))

theorem restrict_irreducible
    (e : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) (F : MvPolynomial (Fin 4) K)
    (hirr : Irreducible F) : Irreducible (restrict (coordinateMatrix e) F) :=
  hirr.map (coordinateAlgEquiv e).toMulEquiv

/-- Four independent actual singular points supplied as an invertible linear
frame contain every projective singular point of an integral cubic surface. -/
theorem singular_in_frame
    (e : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) (F : MvPolynomial (Fin 4) K)
    (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (hz : ∀ i : Fin 4, eval (e (Pi.single i 1)) F = 0)
    (hg : ∀ i : Fin 4, HessianTheorem11.gradient F (e (Pi.single i 1)) = 0)
    (p : Fin 4 → K) (hp : eval p F = 0) (hgp : HessianTheorem11.gradient F p = 0) :
    ∃ i : Fin 4, ∃ t : K, p = t • e (Pi.single i 1) := by
  let B := coordinateMatrix e
  have hz' (i : Fin 4) : eval (Pi.single i 1) (restrict B F) = 0 := by
    simpa only [eval_restrict,B,coordinateMatrix_mulVec] using hz i
  have hg' (i j : Fin 4) : eval (Pi.single i 1) (pderiv j (restrict B F)) = 0 := by
    simp only [pderiv_restrict,map_sum,map_mul,eval_restrict,B,coordinateMatrix_mulVec]
    have hh (a : Fin 4) : eval (e (Pi.single i 1)) (pderiv a F) = 0 := congrFun (hg i) a
    simp only [hh,zero_mul,Finset.sum_const_zero]
  have hpx : eval (e.symm p) (restrict B F) = 0 := by
    simpa only [eval_restrict,B,coordinateMatrix_mulVec,LinearEquiv.apply_symm_apply] using hp
  have hpg : HessianTheorem11.gradient (restrict B F) (e.symm p) = 0 := by
    ext j
    simp only [HessianTheorem11.gradient,pderiv_restrict,map_sum,map_mul,eval_restrict,
      B,coordinateMatrix_mulVec,LinearEquiv.apply_symm_apply]
    have hh (a : Fin 4) : eval p (pderiv a F) = 0 := congrFun hgp a
    simp only [hh,zero_mul,Finset.sum_const_zero,Pi.zero_apply]
  obtain ⟨i,t,hi⟩ := (singular_iff_axis_of_coordinate_frame (restrict B F)
    (homogeneous_restrict B F hF) (restrict_irreducible e F hirr) hz' hg' (e.symm p)).mp ⟨hpx,hpg⟩
  refine ⟨i,t,?_⟩
  have he := congrArg e hi
  simpa only [LinearEquiv.apply_symm_apply,show Pi.single i t =
    t • (Pi.single i (1 : K) : Fin 4 → K) by ext j; simp [Pi.single_apply],map_smul] using he

end CubicTenVariables.CubicSurfaceSingularCoordinateTransport
