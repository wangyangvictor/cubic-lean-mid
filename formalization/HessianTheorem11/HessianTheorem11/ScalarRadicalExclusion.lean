import HessianTheorem11.CoisotropicRadicalBasis
import HessianTheorem11.ScalarRadicalWeight
import HessianTheorem11.AdaptedFlag

/-! The final lowered-weight contradiction on the actual common radical
in the scalar alternative. The basis refinement is constructed internally. -/
noncomputable section
namespace HessianTheorem11
open Module MvPolynomial
namespace CoisotropicBasis.Data
variable {F : GeometricPolynomial 13} {x : GeometricPoint 13}
  {T : Submodule GeometricField (GeometricPoint 13)}
  (D : Data (hessianBilinear F x) T x 5 2 4)

theorem scalar_common_radical_eq_bot (hF : F.IsHomogeneous 3) (hsemi : WeightSemistable F)
    (hker : LinearMap.ker (hessian F x).mulVecLin ≤ T)
    (hann : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0)
    (U : Submodule GeometricField (GeometricPoint 5))
    (hUA : ∀ z ∈ U, ∀ a : GeometricPoint 5, ∀ v : GeometricPoint 13,
      polarization F (D.radicalMatrix.mulVec z) (D.radicalMatrix.mulVec a) v = 0)
    (hUT : ∀ z ∈ U, ∀ t ∈ T, ∀ u ∈ T,
      polarization F (D.radicalMatrix.mulVec z) t u = 0) : U = ⊥ := by
  classical
  by_contra hU
  obtain ⟨z,hz,hz0⟩ := U.ne_bot_iff.mp hU
  obtain ⟨A⟩ := nonempty_adaptedFlagBasis U ⊤ le_top z hz0 hz
  let D' := D.rebaseRadical A.basis
  have hv (i : Fin 5) : D'.radicalVector i = D.radicalMatrix.mulVec (A.basis i) :=
    D.radicalRebasedBasis_radical A.basis i
  have hSA : ∀ a ∈ A.tangentIndices, ∀ b : Fin 5, ∀ v : GeometricPoint 13,
      polarization F (D'.radicalVector a) (D'.radicalVector b) v = 0 := by
    intro a ha b v
    rw [hv, hv]
    exact hUA _ ((A.mem_tangent_iff a).mpr ha) _ v
  have hST : ∀ a ∈ A.tangentIndices, ∀ t ∈ T, ∀ u ∈ T,
      polarization F (D'.radicalVector a) t u = 0 := by
    intro a ha t ht u hu
    rw [hv]
    exact hUT _ ((A.mem_tangent_iff a).mpr ha) t ht u hu
  have hs := D'.scalarRadicalWeight_sum_nonnegative hF hsemi hker hann A.tangentIndices hSA hST
  have hc : 0 < (A.tangentIndices.card : ℤ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨A.radial,A.radial_mem⟩
  norm_num at hs
  omega

end CoisotropicBasis.Data
end HessianTheorem11
