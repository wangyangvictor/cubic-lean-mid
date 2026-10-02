import HessianTheorem11.ReducedComponentDimension
import HessianTheorem11.ReducedMaximalComponent
import HessianTheorem11.ReducedBiconeComponent
import HessianTheorem11.ReducedDominantFiberProduct

/-! The old nine-assertion concentration package is constructed from three
remaining assertions: the generic smooth/rank open and the two ordinary
kernel-bundle assertions. The separate retained AD supplies strict dimension
drop for recognizing components. Six old assertions are now proved. -/

noncomputable section
namespace HessianTheorem11.ReducedConcentration

/-- Exactly the remaining generic-rank and ordinary kernel-bundle premises.
No component selection, scalar invariance, fiber-product bound, or dominant
open inverse-image dimension is a field of this smaller input. -/
structure ConcentrationCoreInput : Prop extends GenericRankOpenInput, KernelBundleInput

/-- All four former affine-component assertions, constructed from the
existing kernel-bundle and strict dimension-drop inputs. -/
theorem affineComponentsInput (KI : KernelBundleInput)
    (AD : AffineHypersurfaceDimensionInput) : AffineComponentsInput where
  finite_dimension := ReducedComponentDimension.finite_dimension
  maximal_dimension_component := ReducedMaximalComponent.maximal_dimension_component
  dimension_maximal := ReducedComponentDimension.dimension_maximal AD
  bicone_component := ReducedBiconeComponent.bicone_component KI

/-- Reconstruct the full original concentration interface. The new public
signature uses only its weaker core and the separately retained AD. -/
theorem ConcentrationCoreInput.toConcentrationGeometryInput
    (AG : ConcentrationCoreInput) (AD : AffineHypersurfaceDimensionInput) :
    ConcentrationGeometryInput where
  toAffineComponentsInput := affineComponentsInput AG.toKernelBundleInput AD
  toGenericRankOpenInput := AG.toGenericRankOpenInput
  toKernelBundleInput := AG.toKernelBundleInput
  toDominantFiberProductInput :=
    ReducedDominantFiberProduct.dominantFiberProductInput AG.toGenericRankOpenInput
  toDominantOpenInput := ReducedDominantOpen.dominantOpenInput

end HessianTheorem11.ReducedConcentration
