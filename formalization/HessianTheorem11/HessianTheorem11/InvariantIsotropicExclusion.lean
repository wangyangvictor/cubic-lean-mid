import HessianTheorem11.InvariantWeightExclusion
import HessianTheorem11.CoisotropicMiddleBasis
import HessianTheorem11.WittInvariantWeights

/-! Excluding the invariant-isotropic alternative for the actual
five-dimensional radical and four-dimensional middle cubic blocks. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix Module NonzeroLimitTransport

theorem fin_two_eq_or_eq (r e k : Fin 2) (hre : e≠r) : k=r ∨ k=e := by
  fin_cases r <;> fin_cases e <;> fin_cases k <;> simp_all

theorem thirteen_invariant_isotropic_subspace_impossible
    (boundary : RationalRelativeBoundaryInput) (bigCell : TextbookOrbitBigCellInput)
    (F : AnisotropicCubic 13) {x : GeometricPoint 13}
    {T : Submodule GeometricField (GeometricPoint 13)}
    (D : CoisotropicBasis.Data (hessianBilinear (geometricPolynomial F.polynomial) x) T x 5 2 4)
    (hker : LinearMap.ker (hessian (geometricPolynomial F.polynomial) x).mulVecLin ≤ T)
    (hann : ∀t∈T,∀u∈LinearMap.ker (hessian (geometricPolynomial F.polynomial) x).mulVecLin,
      ∀v∈LinearMap.ker (hessian (geometricPolynomial F.polynomial) x).mulVecLin,
        polarization (geometricPolynomial F.polynomial) t u v=0)
    (hC : ∀a∈LinearMap.ker (hessian (geometricPolynomial F.polynomial) x).mulVecLin,D.isotropicGramAt a=0)
    (β : LinearMap.BilinForm GeometricField (GeometricPoint 4))
    (hβsym : β.IsSymm) (hβnondeg : β.Nondegenerate)
    (hβ : ∀u v,β u v=polarization (geometricPolynomial F.polynomial)
      (D.middleMatrix.mulVec u) (D.middleMatrix.mulVec v) x)
    (η : Fin 2) (hη : η≠D.radial)
    (e : GeometricPoint 5 →ₗ[GeometricField] GeometricPoint 4)
    (M : GeometricPoint 5 →ₗ[GeometricField] (GeometricPoint 4 →ₗ[GeometricField] GeometricPoint 4))
    (heq : ∀a b,β (e a) b=polarization (geometricPolynomial F.polynomial)
      (D.radicalMatrix.mulVec a) (D.isotropicVector η) (D.middleMatrix.mulVec b))
    (hMq : ∀a b c,β (M a b) c=polarization (geometricPolynomial F.polynomial)
      (D.radicalMatrix.mulVec a) (D.middleMatrix.mulVec b) (D.middleMatrix.mulVec c))
    (hMsym : ∀a u v,β (M a u) v=β u (M a v))
    (W : Submodule GeometricField (GeometricPoint 4))
    (hW : ∀u∈W,∀v∈W,β u v=0)
    (heW : LinearMap.range e ≤ W)
    (hMW : ∀a u,u∈W→M a u∈W) : False := by
  let P := geometricPolynomial F.polynomial
  have hP : P.IsHomogeneous 3 := geometric_homogeneous F.homogeneous
  obtain ⟨b,w,hw,hsum,hGram,hE,hQ⟩ := WittSubspaceBasis.exists_invariant_weight_basis
    β hβsym hβnondeg W hW e M (fun a => heW ⟨a,rfl⟩) hMsym hMW
  let D' := D.rebaseMiddle b
  have hR (i : Fin 5) : D'.radicalVector i=D.radicalVector i := D.middleRebasedBasis_radical b i
  have hK (i : Fin 2) : D'.isotropicVector i=D.isotropicVector i := D.middleRebasedBasis_final b (Sum.inl i)
  have hB (i : Fin 4) : D'.middleVector i=D.middleMatrix.mulVec (b i) := D.middleRebasedBasis_middle b i
  have hsingle (i : Fin 5) : D.radicalMatrix.mulVec (Pi.single i 1)=D.radicalVector i := by
    ext j
    rw [Matrix.mulVec_single_one]
    rfl
  have hC' : ∀a∈LinearMap.ker (hessian P x).mulVecLin,D'.isotropicGramAt a=0 := by
    intro a ha
    ext i j
    change polarization P (D'.isotropicVector i) (D'.isotropicVector j) a=0
    rw [hK,hK]
    exact congrFun (congrFun (hC a ha) i) j
  apply thirteen_invariant_radial_weights_impossible boundary bigCell F D' w hw
    (by simpa using hsum) hker hann hC'
  · intro i j hij
    apply hGram i j
    rw [hβ]
    change polarization P (D'.middleVector i) (D'.middleVector j) x≠0 at hij
    rwa [hB,hB] at hij
  · intro a k i hne
    rw [hR,hK,hB] at hne
    rcases fin_two_eq_or_eq D.radial η k hη with hk|hk
    · subst k
      have hx := D.radial_eq
      change D.isotropicVector D.radial=x at hx
      rw [hx,polarization_swap_last hP] at hne
      change dotProduct (D.radicalVector a)
        ((hessian P x).mulVec (D.middleMatrix.mulVec (b i)))≠0 at hne
      have hz : polarization P (D.middleMatrix.mulVec (b i)) (D.radicalVector a) x=0 := by
        change dotProduct _ ((hessian P x).mulVec (D.radicalVector a))=0
        rw [show (hessian P x).mulVec (D.radicalVector a)=0 from D.radical_hessian_kernel a]
        simp
      have hz' := polarization_swap_first P (D.radicalVector a) (D.middleMatrix.mulVec (b i)) x
      exact False.elim (hne (hz'.trans hz))
    · subst k
      have hh : β (e (Pi.single a 1)) (b i)≠0 := by
        rw [heq,hsingle]
        exact hne
      have hh' := hE (Pi.single a 1) i hh
      omega
  · intro a i j hne
    rw [hR,hB,hB] at hne
    apply hQ (Pi.single a 1) i j
    rw [hMq,hsingle]
    exact hne

end HessianTheorem11
