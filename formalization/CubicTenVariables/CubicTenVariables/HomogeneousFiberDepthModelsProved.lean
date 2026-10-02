import CubicTenVariables.RawHomogeneousFiberDepthModels
import CubicTenVariables.IntegralConeZeroSetModel
import CubicTenVariables.BihomogeneousIncidenceFamily
import CubicTenVariables.Literature.HomogeneousFiberDepthModels

/-! The exact homogeneous fiber-depth model input, proved from finite
homogeneous linear-cut certificates, Noetherian finite generation, Galois
descent and integer zero-set spreading. No semicontinuity or spreading
literature proposition is supplied as an assumption. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.HomogeneousFiberDepthModelsProved
open MvPolynomial HessianTheorem11 IntegralGeometricFiberDepth

/-- Parameter homogeneity makes the actual geometric depth locus conical.
At scalar zero, inclusion of fibers suffices; no nonzero-scalar restriction
or nonemptiness convention is hidden in this statement. -/
theorem depth_cone {m n t : ℕ}
    (f : Fin t → MvPolynomial (Fin n) (MvPolynomial (Fin m) ℤ))
    (dv : Fin t → ℕ) (hf : ∀ i s, (coeff s (f i)).IsHomogeneous (dv i))
    (j : ℕ) :
    IsAffineCone {v : GeometricPoint m | (j : Dimension) ≤
      ReducedGaussSection.coordinateDimension (fiber f GeometricField v)} := by
  have heq (v : GeometricPoint m) : fiber f GeometricField v =
      BihomogeneousIncidenceFamily.fiber f GeometricField v := by
    ext x
    simp only [fiber, BihomogeneousIncidenceFamily.fiber,
      BihomogeneousIncidenceFamily.value, eval_map]
  intro a v hv
  change (j : Dimension) ≤ ReducedGaussSection.coordinateDimension
    (fiber f GeometricField v) at hv
  change (j : Dimension) ≤ ReducedGaussSection.coordinateDimension
    (fiber f GeometricField (a • v))
  apply hv.trans
  apply ReducedGaussSection.coordinateDimension_mono
  rw [heq, heq]
  exact BihomogeneousIncidenceFamily.fiber_subset_smul_parameter f dv hf v a

/-- An inhabitant of the unchanged literature interface: homogeneous
integral generators give the exact reduced Qbar ideal and the exact depth
locus over every field of every good characteristic. -/
theorem proved : Literature.HomogeneousFiberDepthModels := by
  intro m n t j hj f dx dv _hdx hfx hfv
  obtain ⟨r,H,hH0,hH⟩ := RawHomogeneousFiberDepthModels.exists_equations hj f dx hfx
  have hset : IntegralConeZeroSetModel.zeroSet H =
      {v : GeometricPoint m | (j : Dimension) ≤
        ReducedGaussSection.coordinateDimension (fiber f GeometricField v)} := by
    ext v
    exact hH0 v
  have hcone : IsAffineCone (IntegralConeZeroSetModel.zeroSet H) := by
    rw [hset]
    exact depth_cone f dv hfv j
  obtain ⟨u,G,d,D,hd,hD,hI,_h0,hgood⟩ := IntegralConeZeroSetModel.exists_model H hcone
  refine ⟨u,G,d,D,hd,hD,?_,?_⟩
  · simpa only [hset] using hI
  · intro p _hp hpD K _ _ v
    exact (hgood p hpD K v).symm.trans (hH K v)

end CubicTenVariables.HomogeneousFiberDepthModelsProved
