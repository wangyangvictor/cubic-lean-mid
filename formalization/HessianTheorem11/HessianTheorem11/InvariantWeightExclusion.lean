import HessianTheorem11.CoisotropicFiniteCoordinates

/-! The invariant-isotropic radial weighting contradicts actual rational
anisotropy through the proved unipotent transport and normal-column bound. -/
noncomputable section
namespace HessianTheorem11
open Matrix MvPolynomial Module PolynomialRestriction NonzeroLimitTransport

theorem CoisotropicBasis.Data.finiteWeight_nonnegative_support
    {n m d q : ℕ} {F : GeometricPolynomial n} {x : GeometricPoint n}
    {T : Submodule GeometricField (GeometricPoint n)}
    (D : CoisotropicBasis.Data (hessianBilinear F x) T x m d q)
    (wB : Fin q → ℤ) (hF : F.IsHomogeneous 3)
    (hker : LinearMap.ker (hessian F x).mulVecLin ≤ T)
    (hann : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v=0)
    (hC : ∀a∈LinearMap.ker (hessian F x).mulVecLin,D.isotropicGramAt a=0)
    (hB : ∀i j,D.middleGram i j≠0→wB i+wB j=2)
    (hwb : ∀i,0≤wB i)
    (hE : ∀a b c,polarization F (D.radicalVector a) (D.isotropicVector b)
      (D.middleVector c)≠0→2≤wB c)
    (hQ : ∀a b c,polarization F (D.radicalVector a) (D.middleVector b)
      (D.middleVector c)≠0→2≤wB b+wB c) :
    HasNonnegativeWeights (restrict (basisMatrix D.finiteBasis) F) (D.finiteWeight wB) := by
  apply nonnegativeWeights_of_thirdPartials _ (homogeneous_restrict _ F hF)
  intro i j k hne
  change coeff 0 (pderiv k (pderiv j (pderiv i
    (restrict (basisMatrix D.finiteBasis) F))))≠0 at hne
  rw [polarization_in_coordinates F hF] at hne
  apply D.invariantRadialWeight_nonnegative_tensor wB hF hker hann hC hB hwb hE hQ
    (D.finiteIndexEquiv.symm i) (D.finiteIndexEquiv.symm j) (D.finiteIndexEquiv.symm k)
  simpa only [CoisotropicBasis.Data.finiteBasis,Basis.reindex_apply] using hne

theorem CoisotropicBasis.Data.normal_dimension_le_one_of_finiteWeight
    (boundary : RationalRelativeBoundaryInput) (bigCell : TextbookOrbitBigCellInput)
    {n m d q : ℕ} (F : AnisotropicCubic n) (hn : 0<n) {x : GeometricPoint n}
    {T : Submodule GeometricField (GeometricPoint n)}
    (D : CoisotropicBasis.Data (hessianBilinear (geometricPolynomial F.polynomial) x) T x m d q)
    (wB : Fin q → ℤ) (hwb : ∀i,0≤wB i)
    (hsum : ∑i,D.finiteWeight wB i=0)
    (hW : HasNonnegativeWeights
      (restrict (basisMatrix D.finiteBasis) (geometricPolynomial F.polynomial)) (D.finiteWeight wB)) :
    d≤1 := by
  obtain ⟨U,hdet,hupper,htransport⟩ := anisotropic_zeroWeightPart_transport boundary bigCell F hn
    (basisMatrix D.finiteBasis) (basisMatrix_injective D.finiteBasis) (D.finiteWeight wB) hsum hW
  rw [← D.finiteNormal_card]
  exact normal_card_le_one_of_extremal_weight_transport _
    (homogeneous_restrict _ _ (geometric_homogeneous F.homogeneous))
    (D.finiteWeight wB) D.finiteRadial D.finiteRadicalIndices D.finiteNormalIndices
    (D.finiteWeight_radial wB) (D.finiteWeight_minimum wB hwb)
    (D.finiteWeight_radical wB) (D.finiteWeight_minimum_only wB hwb)
    (D.finiteWeight_normal wB) D.finite_coordinate_kernel_iff U (injective_of_det_one U hdet)
    hupper htransport

theorem thirteen_invariant_radial_weights_impossible
    (boundary : RationalRelativeBoundaryInput) (bigCell : TextbookOrbitBigCellInput)
    (F : AnisotropicCubic 13) {x : GeometricPoint 13}
    {T : Submodule GeometricField (GeometricPoint 13)}
    (D : CoisotropicBasis.Data (hessianBilinear (geometricPolynomial F.polynomial) x) T x 5 2 4)
    (wB : Fin 4 → ℤ) (hwb : ∀i,0≤wB i) (hsum : ∑i,wB i=4)
    (hker : LinearMap.ker (hessian (geometricPolynomial F.polynomial) x).mulVecLin ≤ T)
    (hann : ∀t∈T,∀u∈LinearMap.ker (hessian (geometricPolynomial F.polynomial) x).mulVecLin,
      ∀v∈LinearMap.ker (hessian (geometricPolynomial F.polynomial) x).mulVecLin,
        polarization (geometricPolynomial F.polynomial) t u v=0)
    (hC : ∀a∈LinearMap.ker (hessian (geometricPolynomial F.polynomial) x).mulVecLin,D.isotropicGramAt a=0)
    (hB : ∀i j,D.middleGram i j≠0→wB i+wB j=2)
    (hE : ∀a b c,polarization (geometricPolynomial F.polynomial)
      (D.radicalVector a) (D.isotropicVector b) (D.middleVector c)≠0→2≤wB c)
    (hQ : ∀a b c,polarization (geometricPolynomial F.polynomial)
      (D.radicalVector a) (D.middleVector b) (D.middleVector c)≠0→2≤wB b+wB c) : False := by
  have hw := D.finiteWeight_nonnegative_support wB (geometric_homogeneous F.homogeneous)
    hker hann hC hB hwb hE hQ
  have hs : ∑i,D.finiteWeight wB i=0 := by rw [D.sum_finiteWeight,hsum]; norm_num
  have hh := D.normal_dimension_le_one_of_finiteWeight boundary bigCell F (by norm_num) wB hwb hs hw
  omega

end HessianTheorem11
