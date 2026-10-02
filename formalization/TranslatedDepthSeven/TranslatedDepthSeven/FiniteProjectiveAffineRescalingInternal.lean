import TranslatedDepthSeven.IsolatedVertexQuotientSourceTransportInternal
import TranslatedDepthSeven.IsolatedVertexQuotientNodeDecomposition

/-! # Homogeneous first-chart affine rescaling in consecutive coordinates -/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 2500000

/-- The homogeneous substitution `[s,z] ↦ [s,b*s+r*z]`. -/
def finHomogeneousAffinePolynomialChange
    {K : Type*} [Field K] {N : ℕ} (b : Fin N → K) (r : K) (hr : r ≠ 0) :
    MvPolynomial (Fin (N + 1)) K ≃ₐ[K] MvPolynomial (Fin (N + 1)) K :=
  let E := MvPolynomial.renameEquiv K (_root_.finSuccEquiv N)
  (E.trans (homogeneousAffinePolynomialChangeAlgEquiv b r hr)).trans E.symm

theorem finHomogeneousAffinePolynomialChange_isHomogeneous
    {K : Type*} [Field K] {N k : ℕ} (b : Fin N → K) (r : K) (hr : r ≠ 0)
    (f : MvPolynomial (Fin (N + 1)) K) (hf : f.IsHomogeneous k) :
    (finHomogeneousAffinePolynomialChange b r hr f).IsHomogeneous k := by
  apply MvPolynomial.IsHomogeneous.rename_isHomogeneous
  apply isHomogeneous_homogeneousAffinePolynomialChange b r hr
  exact hf.rename_isHomogeneous

theorem finHomogeneousAffinePolynomialChange_symm_isHomogeneous
    {K : Type*} [Field K] {N k : ℕ} (b : Fin N → K) (r : K) (hr : r ≠ 0)
    (f : MvPolynomial (Fin (N + 1)) K) (hf : f.IsHomogeneous k) :
    ((finHomogeneousAffinePolynomialChange b r hr).symm f).IsHomogeneous k := by
  apply MvPolynomial.IsHomogeneous.rename_isHomogeneous
  apply isHomogeneous_homogeneousAffinePolynomialChange_symm b r hr
  exact hf.rename_isHomogeneous

theorem finHomogeneousAffinePolynomialChange_map_data
    {K : Type*} [Field K] {N s d : ℕ} (b : Fin N → K) (r : K) (hr : r ≠ 0)
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) (hIprime : I.IsPrime)
    (hIhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K))
    (hIdegree : HasProjectiveDimensionDegree I s d) :
    let J := I.map (finHomogeneousAffinePolynomialChange b r hr)
    J.IsPrime ∧ J.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K) ∧
      HasProjectiveDimensionDegree J s d := by
  let E := MvPolynomial.renameEquiv K (_root_.finSuccEquiv N)
  let A := homogeneousAffinePolynomialChangeAlgEquiv b r hr
  let e := finHomogeneousAffinePolynomialChange b r hr
  have hmap : I.map e = ((I.map E).map A).map E.symm := by
    calc
      I.map e = (I.map (E.trans A)).map E.symm :=
        (I.map_mapₐ (E.trans A).toAlgHom E.symm.toAlgHom).symm
      _ = ((I.map E).map A).map E.symm :=
        congrArg (fun J => J.map E.symm) (I.map_mapₐ E.toAlgHom A.toAlgHom).symm
  refine ⟨?_, ?_, ?_⟩
  · letI : I.IsPrime := hIprime
    exact Ideal.map_isPrime_of_equiv e.toRingEquiv
  · change (I.map e).IsHomogeneous _
    rw [hmap]
    apply map_renameEquiv_isHomogeneous (_root_.finSuccEquiv N).symm
    apply map_homogeneousAffinePolynomialChange_isHomogeneous b r hr
    exact map_renameEquiv_isHomogeneous (_root_.finSuccEquiv N) I hIhom
  · exact (hasProjectiveDimensionDegree_map_homogeneousAlgEquiv_iff K e
      (fun k f hf => finHomogeneousAffinePolynomialChange_isHomogeneous b r hr f hf)
      (fun k f hf => finHomogeneousAffinePolynomialChange_symm_isHomogeneous b r hr f hf) I).mpr hIdegree

theorem eval_finHomogeneousAffinePolynomialChange_affine
    {K : Type*} [Field K] {N : ℕ} (b w : Fin N → K) (r : K) (hr : r ≠ 0)
    (f : MvPolynomial (Fin (N + 1)) K) :
    eval (Fin.cons 1 w) (finHomogeneousAffinePolynomialChange b r hr f) =
      eval (Fin.cons 1 (fun j => b j + r * w j)) f := by
  change eval (Fin.cons 1 w)
      (rename (_root_.finSuccEquiv N).symm
        (homogeneousAffinePolynomialChangeAlgEquiv b r hr
          (rename (_root_.finSuccEquiv N) f))) = _
  rw [eval_rename]
  change aeval (Fin.cons 1 w ∘ (_root_.finSuccEquiv N).symm)
      (homogeneousAffinePolynomialChangeAlgEquiv b r hr
        (rename (_root_.finSuccEquiv N) f)) =
      aeval (Fin.cons 1 (fun j => b j + r * w j)) f
  rw [aeval_homogeneousAffinePolynomialChange, aeval_rename]
  congr 1
  apply MvPolynomial.algHom_ext
  intro j
  refine Fin.cases ?_ (fun i => ?_) j <;>
    simp [homogeneousAffineLinearEquiv]

end
end TranslatedDepthSeven
