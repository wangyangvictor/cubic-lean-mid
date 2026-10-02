import HessianTheorem11.QuadraticLowImage

/-! Actual rectangular coordinates on an arbitrary vector subspace. -/
noncomputable section
namespace HessianTheorem11
open Module Matrix MvPolynomial PolynomialRestriction
variable {n m : ℕ}

def submoduleCoordinateMap (L : Submodule GeometricField (GeometricPoint n)) :
    GeometricPoint (finrank GeometricField L) →ₗ[GeometricField] GeometricPoint n :=
  L.subtype.comp (Module.finBasis GeometricField L).equivFun.symm.toLinearMap

def submoduleCoordinateMatrix (L : Submodule GeometricField (GeometricPoint n)) :
    Matrix (Fin n) (Fin (finrank GeometricField L)) GeometricField :=
  LinearMap.toMatrix' (submoduleCoordinateMap L)

@[simp] theorem submoduleCoordinateMatrix_mulVec
    (L : Submodule GeometricField (GeometricPoint n))
    (v : GeometricPoint (finrank GeometricField L)) :
    (submoduleCoordinateMatrix L).mulVec v = submoduleCoordinateMap L v :=
  LinearMap.toMatrix'_mulVec _ _

theorem submoduleCoordinateMap_injective
    (L : Submodule GeometricField (GeometricPoint n)) :
    Function.Injective (submoduleCoordinateMap L) :=
  Subtype.val_injective.comp (Module.finBasis GeometricField L).equivFun.symm.injective

theorem submoduleCoordinateMap_range
    (L : Submodule GeometricField (GeometricPoint n)) :
    Set.range (submoduleCoordinateMap L) = L := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    exact ((Module.finBasis GeometricField L).equivFun.symm v).property
  · intro hx
    refine ⟨(Module.finBasis GeometricField L).equivFun ⟨x,hx⟩, ?_⟩
    change ((Module.finBasis GeometricField L).equivFun.symm
      ((Module.finBasis GeometricField L).equivFun ⟨x,hx⟩) : GeometricPoint n) = x
    rw [LinearEquiv.symm_apply_apply]

theorem polynomialMap_restrict_submodule_image
    (P : Fin m → GeometricPolynomial n)
    (L : Submodule GeometricField (GeometricPoint n)) :
    polynomialMap (fun j => restrict (submoduleCoordinateMatrix L) (P j)) '' Set.univ =
      polynomialMap P '' (L : Set (GeometricPoint n)) := by
  have he : polynomialMap (fun j => restrict (submoduleCoordinateMatrix L) (P j)) =
      polynomialMap P ∘ submoduleCoordinateMap L := by
    ext x j
    simp [polynomialMap]
  rw [he, Set.image_comp, Set.image_univ, submoduleCoordinateMap_range]

theorem quadratic_submodule_low_image_span_le_three
    (GR : GenericRankOpenInput) (AD : AffineHypersurfaceDimensionInput)
    (Q : Fin m → GeometricPolynomial n) (hQ : ∀ j, (Q j).IsHomogeneous 2)
    (L : Submodule GeometricField (GeometricPoint n))
    (hdim : affineDimension (geometricClosure
      (polynomialMap Q '' (L : Set (GeometricPoint n)))) ≤ 2) :
    finrank GeometricField (Submodule.span GeometricField
      (polynomialMap Q '' (L : Set (GeometricPoint n)))) ≤ 3 := by
  have h := quadratic_low_image_span_le_three GR AD
    (fun j => restrict (submoduleCoordinateMatrix L) (Q j))
    (fun j => homogeneous_restrict _ _ (hQ j))
    (by simpa only [polynomialMap_restrict_submodule_image] using hdim)
  rw [polynomialMap_restrict_submodule_image Q L] at h
  exact h

end HessianTheorem11
