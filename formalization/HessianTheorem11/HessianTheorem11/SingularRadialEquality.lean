import HessianTheorem11.NonzeroLimitTransport
import HessianTheorem11.SingularRadial
import HessianTheorem11.GeometricRadial
import HessianTheorem11.BasisHessianTransport
import HessianTheorem11.SplitPolynomial

/-! The singular radial equality gives an actual separation of the zero-weight
cubic into nine active variables and the complementary variables. All support
calculations below concern the genuine polynomial, not a splitting certificate. -/

noncomputable section
namespace HessianTheorem11.SingularRadialEquality
open MvPolynomial Module PolynomialRestriction NonzeroLimitTransport
open scoped BigOperators

variable {K : Type*} [Field K] {n : ℕ}

/-- Exponent-weight formula before specializing to a cubic. -/
theorem monomialWeight_singularRadialWeight (radial : Fin n)
    (IT IL : Finset (Fin n)) (d : Fin n →₀ ℕ) :
    monomialWeight (singularRadialWeight radial IT IL) d =
      -6 * (d radial : ℤ) - 2 * (∑ i ∈ IT, d i : ℕ) +
        4 * ((d.degree : ℤ) - (∑ i ∈ IL, d i : ℕ)) := by
  classical
  unfold monomialWeight singularRadialWeight
  simp only [mul_add, Finset.sum_add_distrib]
  have h1 : (∑ i : Fin n, (d i : ℤ) * if i = radial then -6 else 0) =
      -6 * d radial := by simp [mul_comm]
  have h2 : (∑ i : Fin n, (d i : ℤ) * if i ∈ IT then -2 else 0) =
      -2 * (∑ i ∈ IT, d i : ℕ) := by
    simp only [mul_ite, mul_zero, ← Finset.sum_filter]
    simp [Nat.cast_sum, Finset.mul_sum, mul_comm]
  have h3 : (∑ i : Fin n, (d i : ℤ) * if i ∈ IL then 0 else 4) =
      4 * ((d.degree : ℤ) - (∑ i ∈ IL, d i : ℕ)) := by
    calc
      _ = ∑ i : Fin n, ((d i : ℤ) * 4 - if i ∈ IL then (d i : ℤ) * 4 else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_filter]
        simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finsupp.degree_eq_sum, Nat.cast_sum]
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        ring
  rw [h1, h2, h3]
  ring

/-- A degree-three zero-weight exponent uses only the active coordinates
`IT ∪ ILᶜ`, or only the complementary coordinates `IL \ IT`. -/
theorem zero_weight_cubic_support_separates (radial : Fin n)
    (IT IL : Finset (Fin n)) (hr : radial ∈ IT) (hnest : IT ⊆ IL)
    (d : Fin n →₀ ℕ) (hdegree : d.degree = 3)
    (hw : monomialWeight (singularRadialWeight radial IT IL) d = 0) :
    d.support ⊆ IT ∪ ILᶜ ∨ d.support ⊆ (IT ∪ ILᶜ)ᶜ := by
  classical
  have hrad : d radial ≤ ∑ i ∈ IT, d i :=
    Finset.single_le_sum (by intros; omega) hr
  have hTL : (∑ i ∈ IT, d i) ≤ ∑ i ∈ IL, d i :=
    Finset.sum_le_sum_of_subset_of_nonneg hnest (by intros; omega)
  have hLD : (∑ i ∈ IL, d i) ≤ 3 := by
    rw [← hdegree, Finsupp.degree_eq_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; omega)
  rw [monomialWeight_singularRadialWeight, hdegree] at hw
  have hcases : (∑ i ∈ IL, d i) = ∑ i ∈ IT, d i ∨
      (∑ i ∈ IL, d i) = 3 ∧ (∑ i ∈ IT, d i) = 0 := by omega
  rcases hcases with hsame | ⟨hL, hT⟩
  · left
    have hC : ∑ i ∈ IL \ IT, d i = 0 := by
      have h := Finset.sum_sdiff (f := fun i => d i) hnest
      dsimp only at h
      omega
    intro i hi
    by_contra hn
    have hiC : i ∈ IL \ IT := by simpa [and_comm] using hn
    exact Finsupp.mem_support_iff.mp hi ((Finset.sum_eq_zero_iff.mp hC) i hiC)
  · right
    have hC : ∑ i ∈ ILᶜ, d i = 0 := by
      have h := Finset.sum_compl_add_sum IL (fun i => d i)
      rw [← Finsupp.degree_eq_sum, hdegree] at h
      omega
    intro i hi
    have hiT : i ∉ IT := by
      intro h
      exact Finsupp.mem_support_iff.mp hi ((Finset.sum_eq_zero_iff.mp hT) i h)
    have hiL : i ∈ IL := by
      by_contra h
      exact Finsupp.mem_support_iff.mp hi
        ((Finset.sum_eq_zero_iff.mp hC) i (Finset.mem_compl.mpr h))
    simp [hiT, hiL]

/-- The actual sum of the monomials supported in one coordinate block. -/
def supportedPart (F : MvPolynomial (Fin n) K) (S : Finset (Fin n)) :
    MvPolynomial (Fin n) K := Finsupp.filter (fun d => d.support ⊆ S) F

@[simp] theorem coeff_supportedPart (F : MvPolynomial (Fin n) K)
    (S : Finset (Fin n)) (d : Fin n →₀ ℕ) :
    coeff d (supportedPart F S) = if d.support ⊆ S then coeff d F else 0 := rfl

theorem supportedPart_homogeneous {F : MvPolynomial (Fin n) K} {k : ℕ}
    (hF : F.IsHomogeneous k) (S : Finset (Fin n)) :
    (supportedPart F S).IsHomogeneous k := by
  intro d hd
  apply hF
  intro hz
  exact hd (by simp [hz])

theorem supportedPart_vars (F : MvPolynomial (Fin n) K) (S : Finset (Fin n)) :
    (supportedPart F S).vars ⊆ S := by
  intro i hi
  obtain ⟨d, hd, hid⟩ := (MvPolynomial.mem_vars i).mp hi
  have hs : d.support ⊆ S := (Finset.mem_filter.mp hd).2
  exact hs hid

/-- A homogeneous cubic whose monomials each belong to one of two
complementary blocks is literally a sum of polynomials in those blocks. -/
theorem exists_split_of_support_separates (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous 3) (S : Finset (Fin n))
    (hsep : ∀ d ∈ F.support, d.support ⊆ S ∨ d.support ⊆ Sᶜ) :
    ∃ G : MvPolynomial S K, ∃ H : MvPolynomial (↑Sᶜ : Type) K,
      G.IsHomogeneous 3 ∧ H.IsHomogeneous 3 ∧
      F = rename (fun i : S => (i : Fin n)) G +
        rename (fun i : (↑Sᶜ : Type) => (i : Fin n)) H := by
  classical
  have hex (A : Finset (Fin n)) : ∃ P : MvPolynomial A K,
      rename (fun i : A => (i : Fin n)) P = supportedPart F A := by
    apply exists_rename_eq_of_vars_subset_range _ _ Subtype.val_injective
    intro i hi
    exact ⟨⟨i, supportedPart_vars F A hi⟩, rfl⟩
  obtain ⟨G, hG⟩ := hex S
  obtain ⟨H, hH⟩ := hex Sᶜ
  refine ⟨G, H, ?_, ?_, ?_⟩
  · apply (MvPolynomial.IsHomogeneous.rename_isHomogeneous_iff Subtype.val_injective).mp
    rw [hG]
    exact supportedPart_homogeneous hF S
  · apply (MvPolynomial.IsHomogeneous.rename_isHomogeneous_iff Subtype.val_injective).mp
    rw [hH]
    exact supportedPart_homogeneous hF Sᶜ
  · rw [hG, hH]
    ext d
    by_cases hd : coeff d F = 0
    · simp [hd]
    have hd0 : d ≠ 0 := by
      intro hz
      subst d
      exact hd (hF.coeff_eq_zero (by simp))
    have hdsep := hsep d (Finsupp.mem_support_iff.mpr hd)
    have hnot : ¬ (d.support ⊆ S ∧ d.support ⊆ Sᶜ) := by
      intro ⟨h1, h2⟩
      apply hd0
      apply Finsupp.support_eq_empty.mp
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact Finset.mem_compl.mp (h2 hi) (h1 hi)
    rcases hdsep with hs | hs
    · have hc : ¬ d.support ⊆ Sᶜ := fun hc => hnot ⟨hs, hc⟩
      simp [hs, hc]
    · have hc : ¬ d.support ⊆ S := fun hc => hnot ⟨hc, hs⟩
      simp [hs, hc]

/-- The zero-weight singular radial cubic has no mixed monomial between
`IT ∪ ILᶜ` and its complement. This conclusion needs only cubic homogeneity. -/
theorem zeroWeightPart_splits (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (radial : Fin n) (IT IL : Finset (Fin n)) (hr : radial ∈ IT) (hnest : IT ⊆ IL) :
    ∃ G : MvPolynomial (↑(IT ∪ ILᶜ) : Type) K,
    ∃ H : MvPolynomial (↑((IT ∪ ILᶜ)ᶜ) : Type) K,
      G.IsHomogeneous 3 ∧ H.IsHomogeneous 3 ∧
      zeroWeightPart F (singularRadialWeight radial IT IL) =
        rename (fun i : (↑(IT ∪ ILᶜ) : Type) => (i : Fin n)) G +
        rename (fun i : (↑((IT ∪ ILᶜ)ᶜ) : Type) => (i : Fin n)) H := by
  apply exists_split_of_support_separates _ (zeroWeightPart_homogeneous hF _) (IT ∪ ILᶜ)
  intro d hd
  have hd' := (Finset.mem_filter.mp hd).1
  have hdeg : d.degree = 3 := by
    rw [Finsupp.degree_eq_weight_one]
    exact hF (Finsupp.mem_support_iff.mp hd')
  exact zero_weight_cubic_support_separates radial IT IL hr hnest d hdeg
    ((Finset.mem_filter.mp hd).2)

/-- In the equality case `dim T=5`, `rank H=4`, the active block has
exactly nine coordinates and the radial weights have total zero. -/
theorem equality_dimensions (radial : Fin n) (IT IL : Finset (Fin n))
    (hnest : IT ⊆ IL) (hT : IT.card = 5) (hL : IL.card + 4 = n) :
    (IT ∪ ILᶜ).card = 9 ∧ (∑ i, singularRadialWeight radial IT IL i) = 0 := by
  classical
  have hd : Disjoint IT ILᶜ := Finset.disjoint_left.mpr (by
    intro i hi hni
    exact Finset.mem_compl.mp hni (hnest hi))
  have hLc := Finset.card_compl IL
  constructor
  · rw [Finset.card_union_of_disjoint hd]
    simp only [Fintype.card_fin] at hLc
    omega
  · rw [sum_singularRadialWeight, hT]
    omega

/-- The actual tensor vanishing supplies admissibility of the singular
radial weighting in an adapted basis. -/
theorem nonnegative_in_adapted_flag [CharZero K]
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (x : Fin n → K) (T : Submodule K (Fin n → K))
    (A : AdaptedFlagBasis T (LinearMap.ker (hessian F x).mulVecLin) x)
    (htensor : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0) :
    HasNonnegativeWeights (restrict (HessianTheorem11.basisMatrix A.basis) F)
      (singularRadialWeight A.radial A.tangentIndices A.kernelIndices) := by
  apply nonnegativeWeights_of_thirdPartials _ (homogeneous_restrict _ _ hF)
  intro i j l hne
  have hkernel (k : Fin n) (hk : k ∈ A.kernelIndices) :
      (hessian F (A.basis A.radial)).mulVec (A.basis k) = 0 := by
    rw [A.radial_eq]
    exact (A.mem_kernel_iff k).mpr hk
  have htangent (i : Fin n) (hi : i ∈ A.tangentIndices)
      (j : Fin n) (hj : j ∈ A.kernelIndices)
      (l : Fin n) (hl : l ∈ A.kernelIndices) :
      polarization F (A.basis i) (A.basis j) (A.basis l) = 0 :=
    htensor _ ((A.mem_tangent_iff i).mpr hi)
      _ ((A.mem_kernel_iff j).mpr hj) _ ((A.mem_kernel_iff l).mpr hl)
  apply singularRadialWeight_nonnegative_tensor F hF A.basis
    A.radial A.tangentIndices A.kernelIndices A.radial_mem A.indices_nested
    hkernel htangent i j l
  change coeff 0 (pderiv l (pderiv j (pderiv i
    (restrict (HessianTheorem11.basisMatrix A.basis) F)))) ≠ 0 at hne
  rwa [polarization_in_coordinates F hF] at hne

/-- The columns of an injective square matrix form an actual basis. -/
def matrixBasis (B : Matrix (Fin n) (Fin n) GeometricField)
    (hB : Function.Injective B.mulVec) :
    Basis (Fin n) GeometricField (GeometricPoint n) :=
  (Pi.basisFun GeometricField (Fin n)).map (frameEquiv B hB)

@[simp] theorem matrixBasis_matrix (B : Matrix (Fin n) (Fin n) GeometricField)
    (hB : Function.Injective B.mulVec) :
    BasisHessianTransport.basisMatrix (matrixBasis B hB) = B := by
  ext i j
  simp [BasisHessianTransport.basisMatrix, matrixBasis, frameEquiv_apply,
    Pi.basisFun_apply]

theorem restrict_irreducible (F : GeometricPolynomial n) (hF : Irreducible F)
    (B : Matrix (Fin n) (Fin n) GeometricField) (hB : Function.Injective B.mulVec) :
    Irreducible (restrict B F) := by
  simpa using BasisHessianTransport.restrict_irreducible (matrixBasis B hB) F hF

/-- Nonsingularity of the polynomial Hessian determinant is preserved by
an actual invertible linear substitution. -/
theorem restrict_hessianDeterminant_ne_zero (F : GeometricPolynomial n)
    (hF : hessianDeterminantPolynomial F ≠ 0)
    (B : Matrix (Fin n) (Fin n) GeometricField) (hB : Function.Injective B.mulVec) :
    hessianDeterminantPolynomial (restrict B F) ≠ 0 := by
  obtain ⟨c, hc, he⟩ := BasisHessianTransport.hessian_determinant_restrict (matrixBasis B hB) F
  simp only [matrixBasis_matrix] at he
  change hessianDeterminantPolynomial (restrict B F) =
    C c * restrict B (hessianDeterminantPolynomial F) at he
  rw [he]
  exact mul_ne_zero (C_ne_zero.mpr hc) (NonzeroLimitTransport.restrict_ne_zero _ hF B hB)

/-- Transport preserves the two polynomial properties required by the
split-form divisibility obstruction. -/
theorem zeroWeightPart_irreducible_and_hessianDeterminant_ne_zero
    (boundary : RationalRelativeBoundaryInput) (bigCell : TextbookOrbitBigCellInput)
    (F : AnisotropicCubic n) (hn : 0 < n)
    (hirred : Irreducible (geometricPolynomial F.polynomial))
    (hdet : hessianDeterminantPolynomial (geometricPolynomial F.polynomial) ≠ 0)
    (B : Matrix (Fin n) (Fin n) GeometricField) (hB : Function.Injective B.mulVec)
    (w : Fin n → ℤ) (hsum : ∑ i, w i = 0)
    (hW : HasNonnegativeWeights (restrict B (geometricPolynomial F.polynomial)) w) :
    Irreducible (zeroWeightPart (restrict B (geometricPolynomial F.polynomial)) w) ∧
      hessianDeterminantPolynomial
        (zeroWeightPart (restrict B (geometricPolynomial F.polynomial)) w) ≠ 0 := by
  obtain ⟨U, hU, htri, heq⟩ := anisotropic_zeroWeightPart_transport
    boundary bigCell F hn B hB w hsum hW
  rw [heq]
  exact ⟨restrict_irreducible _ (restrict_irreducible _ hirred B hB) U
    (injective_of_det_one U hU),
    restrict_hessianDeterminant_ne_zero _ (restrict_hessianDeterminant_ne_zero _ hdet B hB)
      U (injective_of_det_one U hU)⟩

/-- Explicit reindexing by the two complementary blocks. -/
def splitIndexEquiv (S : Finset (Fin n)) : S ⊕ (↑Sᶜ : Type) ≃ Fin n where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun i := if h : i ∈ S then Sum.inl ⟨i, h⟩ else Sum.inr ⟨i, Finset.mem_compl.mpr h⟩
  left_inv a := by
    cases a with
    | inl a => simp [a.property]
    | inr a => simp [Finset.mem_compl.mp a.property]
  right_inv i := by dsimp only; split_ifs <;> rfl

theorem rename_splitIndexEquiv (S : Finset (Fin n))
    (G : MvPolynomial S K) (H : MvPolynomial (↑Sᶜ : Type) K) :
    rename (splitIndexEquiv S).symm
      (rename (fun i : S => (i : Fin n)) G +
        rename (fun i : (↑Sᶜ : Type) => (i : Fin n)) H) =
      rename Sum.inl G + rename Sum.inr H := by
  rw [map_add, rename_rename, rename_rename]
  have hl : (splitIndexEquiv S).symm ∘ (fun i : S => (i : Fin n)) = Sum.inl :=
    funext fun i => (splitIndexEquiv S).symm_apply_apply (Sum.inl i)
  have hr : (splitIndexEquiv S).symm ∘ (fun i : (↑Sᶜ : Type) => (i : Fin n)) = Sum.inr :=
    funext fun i => (splitIndexEquiv S).symm_apply_apply (Sum.inr i)
  rw [hl, hr]

/-- Concrete data obtained at a singular radial equality point. The two
summands are actual polynomials on the complementary coordinate subtypes. -/
structure Data (F : GeometricPolynomial n) (x : GeometricPoint n)
    (T : Submodule GeometricField (GeometricPoint n)) where
  flag : AdaptedFlagBasis T (LinearMap.ker (hessian F x).mulVecLin) x
  active_card : (flag.tangentIndices ∪ flag.kernelIndicesᶜ).card = 9
  weight_sum : ∑ i, singularRadialWeight flag.radial flag.tangentIndices flag.kernelIndices i = 0
  nonnegative : HasNonnegativeWeights (restrict (HessianTheorem11.basisMatrix flag.basis) F)
    (singularRadialWeight flag.radial flag.tangentIndices flag.kernelIndices)
  left : MvPolynomial (↑(flag.tangentIndices ∪ flag.kernelIndicesᶜ) : Type) GeometricField
  right : MvPolynomial (↑((flag.tangentIndices ∪ flag.kernelIndicesᶜ)ᶜ) : Type) GeometricField
  left_homogeneous : left.IsHomogeneous 3
  right_homogeneous : right.IsHomogeneous 3
  split : zeroWeightPart (restrict (HessianTheorem11.basisMatrix flag.basis) F)
      (singularRadialWeight flag.radial flag.tangentIndices flag.kernelIndices) =
    rename (fun i : (↑(flag.tangentIndices ∪ flag.kernelIndicesᶜ) : Type) => (i : Fin n)) left +
    rename (fun i : (↑((flag.tangentIndices ∪ flag.kernelIndicesᶜ)ᶜ) : Type) => (i : Fin n)) right
  limit_irreducible : Irreducible (zeroWeightPart
    (restrict (HessianTheorem11.basisMatrix flag.basis) F)
    (singularRadialWeight flag.radial flag.tangentIndices flag.kernelIndices))
  limit_hessianDeterminant_ne_zero : hessianDeterminantPolynomial (zeroWeightPart
    (restrict (HessianTheorem11.basisMatrix flag.basis) F)
    (singularRadialWeight flag.radial flag.tangentIndices flag.kernelIndices)) ≠ 0

/-- The singular equality `dim T=5`, `rank H(x)=4` produces the split
zero-weight limit, and actual orbit transport retains irreducibility and
nonzero Hessian determinant. No splitting or dimension inequality is assumed. -/
theorem nonempty_data_of_tensor_vanishing
    (boundary : RationalRelativeBoundaryInput) (bigCell : TextbookOrbitBigCellInput)
    (F : AnisotropicCubic n) (hn : 0 < n)
    (hirred : Irreducible (geometricPolynomial F.polynomial))
    (hdet : hessianDeterminantPolynomial (geometricPolynomial F.polynomial) ≠ 0)
    (x : GeometricPoint n) (hx : x ≠ 0)
    (T : Submodule GeometricField (GeometricPoint n)) (hxT : x ∈ T)
    (hTL : T ≤ LinearMap.ker (hessian (geometricPolynomial F.polynomial) x).mulVecLin)
    (htensor : ∀ t ∈ T,
      ∀ u ∈ LinearMap.ker (hessian (geometricPolynomial F.polynomial) x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian (geometricPolynomial F.polynomial) x).mulVecLin,
      polarization (geometricPolynomial F.polynomial) t u v = 0)
    (hT : finrank GeometricField T = 5)
    (hR : (hessian (geometricPolynomial F.polynomial) x).rank = 4) :
    Nonempty (Data (geometricPolynomial F.polynomial) x T) := by
  let P := geometricPolynomial F.polynomial
  let A := adaptedFlagBasis T (LinearMap.ker (hessian P x).mulVecLin) hTL x hx hxT
  have hcardT : A.tangentIndices.card = 5 := A.tangent_card.trans hT
  have hcardL : A.kernelIndices.card + 4 = n := by
    rw [A.kernel_card]
    have h := (hessian P x).mulVecLin.finrank_range_add_finrank_ker
    change (hessian P x).rank + finrank GeometricField (LinearMap.ker (hessian P x).mulVecLin) =
      finrank GeometricField (GeometricPoint n) at h
    rw [hR] at h
    simpa [add_comm] using h
  obtain ⟨hcard, hsum⟩ := equality_dimensions A.radial A.tangentIndices A.kernelIndices
    A.indices_nested hcardT hcardL
  have hhom := geometric_homogeneous F.homogeneous
  have hnonneg := nonnegative_in_adapted_flag P hhom x T A htensor
  obtain ⟨G,H,hG,hH,hsplit⟩ := zeroWeightPart_splits
    (restrict (HessianTheorem11.basisMatrix A.basis) P)
    (homogeneous_restrict _ _ hhom) A.radial A.tangentIndices A.kernelIndices
    A.radial_mem A.indices_nested
  obtain ⟨hi, hd⟩ := zeroWeightPart_irreducible_and_hessianDeterminant_ne_zero
    boundary bigCell F hn hirred hdet (HessianTheorem11.basisMatrix A.basis)
    (basisMatrix_injective A.basis) _ hsum hnonneg
  exact ⟨⟨A,hcard,hsum,hnonneg,G,H,hG,hH,hsplit,hi,hd⟩⟩

/-- Geometric specialization: the actual tangent space of a singular subset
supplies the nested flag, and the general determinantal tangent theorem
supplies all tensor vanishing needed by the equality construction. -/
theorem nonempty_data_of_singular_subset
    (DT : SymmetricDeterminantalTangentInput)
    (boundary : RationalRelativeBoundaryInput) (bigCell : TextbookOrbitBigCellInput)
    (F : AnisotropicCubic n) (hn : 0 < n)
    (hirred : Irreducible (geometricPolynomial F.polynomial))
    (hdet : hessianDeterminantPolynomial (geometricPolynomial F.polynomial) ≠ 0)
    (Z : Set (GeometricPoint n)) (x : GeometricPoint n)
    (hxZ : x ∈ Z) (hx : x ≠ 0) (hxT : x ∈ affineTangentSpace Z x)
    (hmax : ∀ y ∈ Z, (hessian (geometricPolynomial F.polynomial) y).rank ≤
      (hessian (geometricPolynomial F.polynomial) x).rank)
    (hsingular : ∀ y ∈ Z, gradient (geometricPolynomial F.polynomial) y = 0)
    (hT : finrank GeometricField (affineTangentSpace Z x) = 5)
    (hR : (hessian (geometricPolynomial F.polynomial) x).rank = 4) :
    Nonempty (Data (geometricPolynomial F.polynomial) x (affineTangentSpace Z x)) :=
  nonempty_data_of_tensor_vanishing boundary bigCell F hn hirred hdet x hx
    (affineTangentSpace Z x) hxT
    (affineTangentSpace_le_hessian_ker _ Z hsingular x)
    (hessian_tangent_polarization_zero DT _ (geometric_homogeneous F.homogeneous) Z x hxZ hmax)
    hT hR

/-- Hessian determinants commute with an actual bijective renaming of
coordinates, including a change from `Fin n` to the sum of two blocks. -/
theorem determinant_rename_equiv {σ τ : Type*} [Fintype σ] [Fintype τ]
    [DecidableEq σ] [DecidableEq τ] (e : σ ≃ τ) (F : MvPolynomial σ K) :
    (SplitPolynomial.fullHessian (rename e F)).det =
      rename e (SplitPolynomial.fullHessian F).det := by
  classical
  have he : SplitPolynomial.fullHessian (rename e F) =
      ((SplitPolynomial.fullHessian F).submatrix e.symm e.symm).map (rename e) := by
    apply Matrix.ext
    intro i j
    change pderiv j (pderiv i (rename e F)) = rename e (pderiv (e.symm j) (pderiv (e.symm i) F))
    have hi := pderiv_rename e.injective (e.symm i) F
    have hj := pderiv_rename e.injective (e.symm j) (pderiv (e.symm i) F)
    simp only [e.apply_symm_apply] at hi hj
    rw [hi, hj]
  rw [he]
  change ((rename e).toRingHom.mapMatrix
    ((SplitPolynomial.fullHessian F).submatrix e.symm e.symm)).det = _
  rw [← RingHom.map_det, Matrix.det_submatrix_equiv_self]
  rfl

theorem Data.split_irreducible {F : GeometricPolynomial n} {x : GeometricPoint n}
    {T : Submodule GeometricField (GeometricPoint n)} (D : Data F x T) :
    Irreducible (rename Sum.inl D.left + rename Sum.inr D.right) := by
  let S := D.flag.tangentIndices ∪ D.flag.kernelIndicesᶜ
  have h := D.limit_irreducible.map
    (renameEquiv GeometricField (splitIndexEquiv S).symm).toMulEquiv
  change Irreducible (rename (splitIndexEquiv S).symm _) at h
  rw [D.split, rename_splitIndexEquiv] at h
  exact h

theorem Data.split_hessianDeterminant_ne_zero {F : GeometricPolynomial n} {x : GeometricPoint n}
    {T : Submodule GeometricField (GeometricPoint n)} (D : Data F x T) :
    (SplitPolynomial.fullHessian (rename Sum.inl D.left + rename Sum.inr D.right)).det ≠ 0 := by
  let S := D.flag.tangentIndices ∪ D.flag.kernelIndicesᶜ
  let P := zeroWeightPart (restrict (HessianTheorem11.basisMatrix D.flag.basis) F)
    (singularRadialWeight D.flag.radial D.flag.tangentIndices D.flag.kernelIndices)
  have he : rename (splitIndexEquiv S).symm P =
      rename Sum.inl D.left + rename Sum.inr D.right := by
    rw [show P = _ from D.split, rename_splitIndexEquiv]
  rw [← he, determinant_rename_equiv]
  intro hz
  apply D.limit_hessianDeterminant_ne_zero
  apply rename_injective _ (splitIndexEquiv S).symm.injective
  simpa using hz

/-- Both blocks are nonempty when `n>9`, so the irreducible split form
cannot divide its own nonzero Hessian determinant. -/
theorem Data.split_not_dvd_hessianDeterminant {F : GeometricPolynomial n}
    {x : GeometricPoint n} {T : Submodule GeometricField (GeometricPoint n)}
    (D : Data F x T) (hn : 9 < n) :
    ¬ (rename Sum.inl D.left + rename Sum.inr D.right) ∣
      (SplitPolynomial.fullHessian (rename Sum.inl D.left + rename Sum.inr D.right)).det := by
  classical
  let S := D.flag.tangentIndices ∪ D.flag.kernelIndicesᶜ
  have hS : S.card = 9 := D.active_card
  have hSc : Sᶜ.card = n - 9 := by simpa [hS] using Finset.card_compl S
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (show 0 < Sᶜ.card by omega)
  letI : Nonempty S := ⟨⟨i, hi⟩⟩
  letI : Nonempty (↑Sᶜ : Type) := ⟨⟨j, hj⟩⟩
  have hd := D.split_hessianDeterminant_ne_zero
  have hg : (SplitPolynomial.fullHessian D.left).det ≠ 0 := by
    intro hz
    apply hd
    rw [SplitPolynomial.determinant_split, hz, map_zero, zero_mul]
  have hh : (SplitPolynomial.fullHessian D.right).det ≠ 0 := by
    intro hz
    apply hd
    rw [SplitPolynomial.determinant_split, hz, map_zero, mul_zero]
  exact SplitPolynomial.split_not_dvd_hessian_determinant D.left D.right
    (SplitPolynomial.exists_nonconstant_coefficient_of_det_ne_zero D.left hg)
    (SplitPolynomial.exists_nonconstant_coefficient_of_det_ne_zero D.right hh)
    D.split_irreducible hd

/-- The same obstruction expressed in the original adapted coordinates. -/
theorem Data.limit_not_dvd_hessianDeterminant {F : GeometricPolynomial n}
    {x : GeometricPoint n} {T : Submodule GeometricField (GeometricPoint n)}
    (D : Data F x T) (hn : 9 < n) :
    ¬ zeroWeightPart (restrict (HessianTheorem11.basisMatrix D.flag.basis) F)
        (singularRadialWeight D.flag.radial D.flag.tangentIndices D.flag.kernelIndices) ∣
      hessianDeterminantPolynomial (zeroWeightPart
        (restrict (HessianTheorem11.basisMatrix D.flag.basis) F)
        (singularRadialWeight D.flag.radial D.flag.tangentIndices D.flag.kernelIndices)) := by
  intro hdiv
  let S := D.flag.tangentIndices ∪ D.flag.kernelIndicesᶜ
  apply D.split_not_dvd_hessianDeterminant hn
  have h := map_dvd (rename (splitIndexEquiv S).symm).toRingHom hdiv
  change rename (splitIndexEquiv S).symm _ ∣
    rename (splitIndexEquiv S).symm (SplitPolynomial.fullHessian
      (zeroWeightPart (restrict (HessianTheorem11.basisMatrix D.flag.basis) F)
        (singularRadialWeight D.flag.radial D.flag.tangentIndices D.flag.kernelIndices))).det at h
  rw [← determinant_rename_equiv] at h
  rw [D.split, rename_splitIndexEquiv] at h
  exact h

/-- Hessian divisibility is retained by an invertible linear substitution. -/
theorem restrict_dvd_hessianDeterminant (F : GeometricPolynomial n)
    (hdiv : F ∣ hessianDeterminantPolynomial F)
    (B : Matrix (Fin n) (Fin n) GeometricField) (hB : Function.Injective B.mulVec) :
    restrict B F ∣ hessianDeterminantPolynomial (restrict B F) := by
  obtain ⟨c, hc, he⟩ := BasisHessianTransport.hessian_determinant_restrict (matrixBasis B hB) F
  simp only [matrixBasis_matrix] at he
  change hessianDeterminantPolynomial (restrict B F) =
    C c * restrict B (hessianDeterminantPolynomial F) at he
  rw [he]
  exact dvd_mul_of_dvd_right (map_dvd (aeval (linearForms B)).toRingHom hdiv) (C c)

/-- A singular radial equality with `n>9` excludes positive generic corank:
its irreducible cubic cannot divide its Hessian determinant. The implication
from positive generic corank to that divisibility is proved separately by
actual determinant multiplicity. -/
theorem equality_not_dvd_hessianDeterminant
    (boundary : RationalRelativeBoundaryInput) (bigCell : TextbookOrbitBigCellInput)
    (F : AnisotropicCubic n) (hn : 9 < n)
    (hirred : Irreducible (geometricPolynomial F.polynomial))
    (hdet : hessianDeterminantPolynomial (geometricPolynomial F.polynomial) ≠ 0)
    (x : GeometricPoint n) (hx : x ≠ 0)
    (T : Submodule GeometricField (GeometricPoint n)) (hxT : x ∈ T)
    (hTL : T ≤ LinearMap.ker (hessian (geometricPolynomial F.polynomial) x).mulVecLin)
    (htensor : ∀ t ∈ T,
      ∀ u ∈ LinearMap.ker (hessian (geometricPolynomial F.polynomial) x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian (geometricPolynomial F.polynomial) x).mulVecLin,
      polarization (geometricPolynomial F.polynomial) t u v = 0)
    (hT : finrank GeometricField T = 5)
    (hR : (hessian (geometricPolynomial F.polynomial) x).rank = 4) :
    ¬ geometricPolynomial F.polynomial ∣
      hessianDeterminantPolynomial (geometricPolynomial F.polynomial) := by
  obtain ⟨D⟩ := nonempty_data_of_tensor_vanishing boundary bigCell F (by omega)
    hirred hdet x hx T hxT hTL htensor hT hR
  intro hdiv
  apply D.limit_not_dvd_hessianDeterminant hn
  obtain ⟨U,hU,htri,he⟩ := anisotropic_zeroWeightPart_transport boundary bigCell F (by omega)
    (HessianTheorem11.basisMatrix D.flag.basis) (basisMatrix_injective D.flag.basis)
    _ D.weight_sum D.nonnegative
  rw [he]
  exact restrict_dvd_hessianDeterminant _
    (restrict_dvd_hessianDeterminant _ hdiv _ (basisMatrix_injective D.flag.basis))
    U (injective_of_det_one U hU)

end HessianTheorem11.SingularRadialEquality
