import HessianTheorem11.SmoothRadialEquality
import HessianTheorem11.NonzeroLimitTransport

/-! Actual polynomial weight support controls the Hessian of a radial limit.
The ensuing one-row column obstruction is elementary linear algebra. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix Module

variable {K : Type*} [Field K] {n : ℕ}

theorem matrix_congruence_kernel_iff
    (B H : Matrix (Fin n) (Fin n) K) (hB : Function.Injective B.mulVec)
    (v : Fin n → K) :
    (B.transpose * H * B).mulVec v = 0 ↔ H.mulVec (B.mulVec v) = 0 := by
  have hBT : Function.Injective B.transpose.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_transpose B).mpr (Matrix.mulVec_injective_iff_isUnit.mp hB))
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  constructor
  · intro h
    apply hBT
    simpa using h
  · intro h
    simp [h]

/-- Congruence by an invertible map fixing the whole kernel pointwise keeps
that actual kernel unchanged. -/
theorem matrix_congruence_kernel_of_fixed_kernel
    (B H : Matrix (Fin n) (Fin n) K) (hB : Function.Injective B.mulVec)
    (hfix : ∀ v, H.mulVec v = 0 → B.mulVec v = v) (v : Fin n → K) :
    (B.transpose * H * B).mulVec v = 0 ↔ H.mulVec v = 0 := by
  rw [matrix_congruence_kernel_iff B H hB]
  constructor
  · intro h
    have hh := hfix (B.mulVec v) h
    have hv : B.mulVec v = v := hB hh
    rwa [hv] at h
  · intro h
    rwa [hfix v h]

theorem basis_coordinates_mem_span (b : Basis (Fin n) K (Fin n → K))
    (I : Finset (Fin n)) (v : Fin n → K) :
    b.equivFun.symm v ∈ Submodule.span K (b '' (I : Set (Fin n))) ↔
      ∀ i, i ∉ I → v i = 0 := by
  classical
  rw [b.mem_span_image]
  have hr (i : Fin n) : b.repr (b.equivFun.symm v) i = v i := by
    change b.equivFun (b.equivFun.symm v) i = v i
    simp [Finsupp.single_apply]
  constructor
  · intro h i hi
    by_contra hvi
    exact hi (h (Finsupp.mem_support_iff.mpr (by rwa [hr])))
  · intro h i hi
    by_contra hni
    have hzero := h i hni
    have hn := Finsupp.mem_support_iff.mp hi
    rw [hr, hzero] at hn
    exact hn rfl

/-- The kernel in the constructed coordinate basis is precisely the space
supported on the kernel indices, as an equality of actual matrix equations. -/
theorem SimultaneousSubspaceBasis.coordinate_kernel_iff
    {F : MvPolynomial (Fin n) K} {x : Fin n → K}
    {T : Submodule K (Fin n → K)}
    (A : SimultaneousSubspaceBasis T (LinearMap.ker (hessian F x).mulVecLin) x)
    (v : Fin n → K) :
    (hessian (PolynomialRestriction.restrict (basisMatrix A.basis) F)
      (Pi.single A.radial 1)).mulVec v = 0 ↔
        ∀ i, i ∉ A.kernelIndices → v i = 0 := by
  rw [PolynomialRestriction.hessian_restrict, basisMatrix_mulVec_single, A.radial_eq,
    matrix_congruence_kernel_iff _ _ (basisMatrix_injective A.basis), basisMatrix_mulVec_eq]
  change A.basis.equivFun.symm v ∈ LinearMap.ker (hessian F x).mulVecLin ↔ _
  have hspan := basis_coordinates_mem_span A.basis A.kernelIndices v
  rwa [A.kernel_span] at hspan

/-- Formal differentiation subtracts the differentiated variable's weight
from every surviving monomial, including arbitrary repeated variables. -/
theorem exact_weight_pderiv (F : MvPolynomial (Fin n) K) (w : Fin n → ℤ)
    (c : ℤ) (hF : ∀ d ∈ F.support, monomialWeight w d = c) (i : Fin n) :
    ∀ d ∈ (pderiv i F).support, monomialWeight w d = c - w i := by
  classical
  have he : pderiv i F = ∑ s ∈ F.support, pderiv i (monomial s (coeff s F)) := by
    conv_lhs => rw [F.as_sum]
    simp only [map_sum]
  rw [he]
  intro d hd
  obtain ⟨s, hs, hds⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
  rw [pderiv_monomial] at hds
  have hdi : s i ≠ 0 := by
    intro hz
    simpa [hz] using hds
  have hdeq : d = s - Finsupp.single i 1 :=
    Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hds)
  subst d
  have hw := congrArg (monomialWeight w) (Finsupp.sub_add_single_one_cancel hdi)
  rw [monomialWeight_add, monomialWeight_single, hF s hs] at hw
  omega

theorem thirdPartialCoefficient_weight (F : MvPolynomial (Fin n) K)
    (w : Fin n → ℤ) (c : ℤ)
    (hF : ∀ d ∈ F.support, monomialWeight w d = c)
    (i j k : Fin n) (hne : thirdPartialCoefficient F i j k ≠ 0) :
    w i + w j + w k = c := by
  have h1 := exact_weight_pderiv F w c hF i
  have h2 := exact_weight_pderiv (pderiv i F) w (c - w i) h1 j
  have h3 := exact_weight_pderiv (pderiv j (pderiv i F)) w (c - w i - w j) h2 k
  have hz := h3 0 (Finsupp.mem_support_iff.mpr hne)
  simp only [monomialWeight, Finsupp.zero_apply, Nat.cast_zero, zero_mul,
    Finset.sum_const_zero] at hz
  omega

/-- A Hessian entry at a coordinate point has the weight prescribed by its
two matrix indices and the radial coordinate. -/
theorem hessian_coordinate_weight (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous 3) (w : Fin n → ℤ)
    (hW : ∀ d ∈ F.support, monomialWeight w d = 0)
    (radial i j : Fin n) (hne : hessian F (Pi.single radial 1) i j ≠ 0) :
    w i + w j + w radial = 0 := by
  classical
  have he : hessian F (Pi.single radial 1) i j = thirdPartialCoefficient F i j radial := by
    rw [hessian_entry_expansion hF]
    simp [Pi.single_apply, thirdPartialCoefficient]
  rw [he] at hne
  exact thirdPartialCoefficient_weight F w 0 hW i j radial hne

/-- If the normal columns are supported on a single row and the matrix
kernel has no normal coordinates, there is at most one normal coordinate. -/
theorem normal_columns_card_le_one
    (M : Matrix (Fin n) (Fin n) K) (IT IL : Finset (Fin n)) (radial : Fin n)
    (hIL : IL ⊆ IT)
    (hker : ∀ v, M.mulVec v = 0 → ∀ i, i ∉ IL → v i = 0)
    (hcol : ∀ i j, j ∉ IT → i ≠ radial → M i j = 0) :
    (Finset.univ \ IT).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hiT : i ∉ IT := (Finset.mem_sdiff.mp hi).2
  have hjT : j ∉ IT := (Finset.mem_sdiff.mp hj).2
  have hiL : i ∉ IL := fun h => hiT (hIL h)
  have hjL : j ∉ IL := fun h => hjT (hIL h)
  have hcolumn (k : Fin n) (hk : k ∉ IT) :
      M.mulVec (Pi.single k 1) = M radial k • (Pi.single radial 1 : Fin n → K) := by
    ext l
    rw [Matrix.mulVec_single_one]
    by_cases hl : l = radial
    · subst l; simp
    · simp [Pi.single_apply, hl, hcol l k hk hl]
  have hentry (k : Fin n) (hk : k ∉ IT) : M radial k ≠ 0 := by
    intro hz
    have hzcol : M.mulVec (Pi.single k 1) = 0 := by rw [hcolumn k hk, hz, zero_smul]
    have hv := hker (Pi.single k 1) hzcol k (fun h => hk (hIL h))
    simpa using hv
  by_contra hne
  let v : Fin n → K := M radial j • (Pi.single i 1 : Fin n → K) -
    M radial i • (Pi.single j 1 : Fin n → K)
  have hv : M.mulVec v = 0 := by
    simp only [v, Matrix.mulVec_sub, Matrix.mulVec_smul, hcolumn i hiT, hcolumn j hjT,
      smul_smul, mul_comm (M radial i) (M radial j), sub_self]
  have hvi := hker v hv i hiL
  have hz : M radial j = 0 := by
    simpa [v, Pi.single_apply, hne, Ne.symm hne] using hvi
  exact hentry j hjT hz

section Equality
variable [CharZero K]

/-- The actual zero-weight cubic and preserved actual kernel give the
one-dimensional normal-space obstruction in the radial equality argument. -/
theorem SmoothRadialEqualityData.normal_card_le_one_of_limit_kernel
    {F : MvPolynomial (Fin n) K} {x : Fin n → K} {T : Submodule K (Fin n → K)}
    (E : SmoothRadialEqualityData F x T)
    (G : MvPolynomial (Fin n) K) (hG : G.IsHomogeneous 3)
    (hW : ∀ d ∈ G.support,
      monomialWeight (smoothRadialWeight E.adapted.radial
        E.adapted.tangentIndices E.adapted.kernelIndices) d = 0)
    (hker : ∀ v, (hessian G (Pi.single E.adapted.radial 1)).mulVec v = 0 ↔
      ∀ i, i ∉ E.adapted.kernelIndices → v i = 0) :
    (Finset.univ \ E.adapted.tangentIndices).card ≤ 1 := by
  apply normal_columns_card_le_one (hessian G (Pi.single E.adapted.radial 1))
    E.adapted.tangentIndices E.adapted.kernelIndices E.adapted.radial
    E.kernel_subset_tangent (fun v => (hker v).mp)
  intro i j hjT hir
  by_cases hiL : i ∈ E.adapted.kernelIndices
  · have hcol : (hessian G (Pi.single E.adapted.radial 1)).mulVec
        (Pi.single i 1) = 0 := by
      apply (hker _).mpr
      intro l hl
      have hli : l ≠ i := by rintro rfl; exact hl hiL
      simp [Pi.single_apply, hli, Ne.symm hli]
    have hentry := congrFun hcol j
    rw [Matrix.mulVec_single_one] at hentry
    have hs := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i j)
      (hessian_symmetric G (Pi.single E.adapted.radial 1))
    change hessian G (Pi.single E.adapted.radial 1) j i =
      hessian G (Pi.single E.adapted.radial 1) i j at hs
    exact hs.symm.trans hentry
  · by_contra hne
    have hw := hessian_coordinate_weight G hG _ hW E.adapted.radial i j hne
    have hjL : j ∉ E.adapted.kernelIndices := fun h => hjT (E.kernel_subset_tangent h)
    have hjr : j ≠ E.adapted.radial := by
      rintro rfl
      exact hjT E.adapted.radial_mem_tangent
    rw [E.weight_values i, E.weight_values j,
      smoothRadialWeight_radial E.adapted.radial_mem_tangent E.adapted.radial_notMem_kernel]
      at hw
    by_cases hiT : i ∈ E.adapted.tangentIndices <;>
      simp [hiL, hir, hjL, hjr, hiT, hjT] at hw

end Equality

section Transport
variable [CharZero K]
open NonzeroLimitTransport

/-- A minimum variable-weight coordinate is precisely a kernel or radial
coordinate in the equality basis. -/
theorem SmoothRadialEqualityData.minimum_weight
    {F : MvPolynomial (Fin n) K} {x : Fin n → K} {T : Submodule K (Fin n → K)}
    (E : SmoothRadialEqualityData F x T) (j : Fin n)
    (hj : j ∈ E.adapted.kernelIndices ∨ j = E.adapted.radial) (i : Fin n) :
    smoothRadialWeight E.adapted.radial E.adapted.tangentIndices E.adapted.kernelIndices j ≤
      smoothRadialWeight E.adapted.radial E.adapted.tangentIndices E.adapted.kernelIndices i := by
  rw [E.weight_values j, E.weight_values i]
  simp only [hj, if_true]
  split_ifs <;> norm_num

/-- The unipotent transport fixes the radial vector and the whole old
kernel pointwise; the chain rule then proves the new kernel is exactly the
old coordinate kernel. This closes the one-normal-direction argument. -/
theorem SmoothRadialEqualityData.normal_card_le_one_of_unipotent_transport
    {F : MvPolynomial (Fin n) K} {x : Fin n → K} {T : Submodule K (Fin n → K)}
    (E : SmoothRadialEqualityData F x T) (hF : F.IsHomogeneous 3)
    (U : Matrix (Fin n) (Fin n) K) (hU : Function.Injective U.mulVec)
    (hupper : WeightUpperUnipotent
      (smoothRadialWeight E.adapted.radial E.adapted.tangentIndices E.adapted.kernelIndices) U)
    (htransport : zeroWeightPart (PolynomialRestriction.restrict (basisMatrix E.adapted.basis) F)
      (smoothRadialWeight E.adapted.radial E.adapted.tangentIndices E.adapted.kernelIndices) =
      PolynomialRestriction.restrict U
        (PolynomialRestriction.restrict (basisMatrix E.adapted.basis) F)) :
    (Finset.univ \ E.adapted.tangentIndices).card ≤ 1 := by
  let G := PolynomialRestriction.restrict (basisMatrix E.adapted.basis) F
  let w := smoothRadialWeight E.adapted.radial E.adapted.tangentIndices E.adapted.kernelIndices
  have hGr : U.mulVec (Pi.single E.adapted.radial 1) = Pi.single E.adapted.radial 1 :=
    hupper.fixes_minimum_column _ (E.minimum_weight _ (Or.inr rfl))
  have hfix : ∀ v, (hessian G (Pi.single E.adapted.radial 1)).mulVec v = 0 → U.mulVec v = v := by
    intro v hv
    apply hupper.fixes_minimum_subspace
    intro j hj
    have hjL : j ∈ E.adapted.kernelIndices := by
      by_contra hnot
      exact hj ((E.adapted.coordinate_kernel_iff v).mp hv j hnot)
    exact E.minimum_weight j (Or.inl hjL)
  apply E.normal_card_le_one_of_limit_kernel (zeroWeightPart G w)
    (zeroWeightPart_homogeneous (PolynomialRestriction.homogeneous_restrict _ F hF) w)
    (zeroWeightPart_weights G w)
  intro v
  change (hessian (zeroWeightPart G w) (Pi.single E.adapted.radial 1)).mulVec v = 0 ↔ _
  rw [show zeroWeightPart G w = PolynomialRestriction.restrict U G from htransport,
    PolynomialRestriction.hessian_restrict, hGr,
    matrix_congruence_kernel_of_fixed_kernel U _ hU hfix]
  exact E.adapted.coordinate_kernel_iff v

end Transport

/-- Applying the general closed-orbit transport theorem to an anisotropic
cubic eliminates every normal block of dimension greater than one. -/
theorem SmoothRadialEqualityData.normal_card_le_one
    (boundary : NonzeroLimitTransport.RationalRelativeBoundaryInput)
    (bigCell : NonzeroLimitTransport.TextbookOrbitBigCellInput)
    {n : ℕ} (F : AnisotropicCubic n) (hn : 0 < n)
    {x : GeometricPoint n} {T : Submodule GeometricField (GeometricPoint n)}
    (E : SmoothRadialEqualityData (geometricPolynomial F.polynomial) x T) :
    (Finset.univ \ E.adapted.tangentIndices).card ≤ 1 := by
  obtain ⟨U, hdet, hupper, htransport⟩ := NonzeroLimitTransport.anisotropic_zeroWeightPart_transport
    boundary bigCell F hn (basisMatrix E.adapted.basis) (basisMatrix_injective E.adapted.basis)
    (smoothRadialWeight E.adapted.radial E.adapted.tangentIndices E.adapted.kernelIndices)
    E.total_weight_zero E.support_nonnegative
  exact E.normal_card_le_one_of_unipotent_transport (geometric_homogeneous F.homogeneous)
    U (NonzeroLimitTransport.injective_of_det_one U hdet) hupper htransport

end HessianTheorem11
