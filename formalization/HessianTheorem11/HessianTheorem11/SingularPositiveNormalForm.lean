import HessianTheorem11.SingularRadialNormalForm
import HessianTheorem11.SingularNormalEquations
import HessianTheorem11.QuadraticBlockRank

/-! The full singular normal form when the tangent space equals the
Hessian kernel. The positive-weight remainder is retained and proved to
contain only the actual exponent types a d² and d³. -/

noncomputable section
namespace HessianTheorem11.SingularPositiveNormalForm
open MvPolynomial Module NonzeroLimitTransport SingularRadialEquality SingularRadialNormalForm

variable {K : Type*} [Field K] {n : ℕ}

def positiveRemainder (P : MvPolynomial (Fin n) K) (radial : Fin n) (T : Finset (Fin n)) :=
  exponentPart P (fun d => 0 < monomialWeight (singularRadialWeight radial T T) d)

theorem equals_zeroWeightPart_add_remainder
    (P : MvPolynomial (Fin n) K) (radial : Fin n) (T : Finset (Fin n))
    (hw : HasNonnegativeWeights P (singularRadialWeight radial T T)) :
    P = zeroWeightPart P (singularRadialWeight radial T T) + positiveRemainder P radial T := by
  classical
  ext d
  by_cases hd : coeff d P = 0
  · simp [positiveRemainder, hd]
  have hn := hw d (Finsupp.mem_support_iff.mpr hd)
  by_cases he : monomialWeight (singularRadialWeight radial T T) d = 0
  · simp [positiveRemainder, he]
  · have hp : 0 < monomialWeight (singularRadialWeight radial T T) d := by omega
    simp [positiveRemainder, he, hp]

theorem positive_exponent_distribution
    (radial : Fin n) (T : Finset (Fin n)) (hr : radial ∈ T)
    (d : Fin n →₀ ℕ) (hdeg : d.degree = 3)
    (hw : 0 < monomialWeight (singularRadialWeight radial T T) d) :
    d radial = 0 ∧
      (((∑ i ∈ T.erase radial, d i) = 1 ∧ (∑ i ∈ Tᶜ, d i) = 2) ∨
       ((∑ i ∈ T.erase radial, d i) = 0 ∧ (∑ i ∈ Tᶜ, d i) = 3)) := by
  classical
  have hrad : d radial ≤ ∑ i ∈ T, d i := Finset.single_le_sum (by intros; omega) hr
  have hs := Finset.sum_compl_add_sum T (fun i => d i)
  rw [← Finsupp.degree_eq_sum, hdeg] at hs
  have he := Finset.sum_erase_add T (fun i => d i) hr
  dsimp only at he
  rw [monomialWeight_singularRadialWeight, hdeg] at hw
  omega

theorem positiveRemainder_homogeneous
    {P : MvPolynomial (Fin n) K} (hP : P.IsHomogeneous 3)
    (radial : Fin n) (T : Finset (Fin n)) :
    (positiveRemainder P radial T).IsHomogeneous 3 := exponentPart_homogeneous hP _

theorem positiveRemainder_support
    (P : MvPolynomial (Fin n) K) (hP : P.IsHomogeneous 3)
    (radial : Fin n) (T : Finset (Fin n)) (hr : radial ∈ T) :
    ∀ d ∈ (positiveRemainder P radial T).support, d radial = 0 ∧
      (((∑ i ∈ T.erase radial, d i) = 1 ∧ (∑ i ∈ Tᶜ, d i) = 2) ∨
       ((∑ i ∈ T.erase radial, d i) = 0 ∧ (∑ i ∈ Tᶜ, d i) = 3)) := by
  intro d hd
  have hm := (mem_support_exponentPart P _ d).mp hd
  apply positive_exponent_distribution radial T hr d
  · rw [Finsupp.degree_eq_weight_one]
    exact hP (Finsupp.mem_support_iff.mp hm.1)
  · exact hm.2

theorem positiveRemainder_radial_partial
    (P : MvPolynomial (Fin n) K) (hP : P.IsHomogeneous 3)
    (radial : Fin n) (T : Finset (Fin n)) (hr : radial ∈ T) :
    pderiv radial (positiveRemainder P radial T) = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro hm
  obtain ⟨d, hd, hdr⟩ := (mem_vars radial).mp hm
  exact Finsupp.mem_support_iff.mp hdr (positiveRemainder_support P hP radial T hr d hd).1

theorem derivative_block_degree_pos
    (P : MvPolynomial (Fin n) K) (D : Finset (Fin n))
    (hP : ∀ e ∈ P.support, 2 ≤ ∑ j ∈ D, e j)
    (i : Fin n) (d : Fin n →₀ ℕ) (hd : d ∈ (pderiv i P).support) :
    0 < ∑ j ∈ D, d j := by
  classical
  obtain ⟨e, he, hei, rfl⟩ := derivative_support_preimage P i d hd
  have hle : Finsupp.single i 1 ≤ e := Finsupp.single_le_iff.mpr (by omega)
  have hadd : e - Finsupp.single i 1 + Finsupp.single i 1 = e := tsub_add_cancel_of_le hle
  have hs := congrArg (fun d : Fin n →₀ ℕ => ∑ j ∈ D, d j) hadd
  simp only [Finsupp.add_apply, Finset.sum_add_distrib] at hs
  have hsingle : (∑ j ∈ D, (Finsupp.single i 1 : Fin n →₀ ℕ) j) ≤ 1 := by
    by_cases hi : i ∈ D <;> simp [Finsupp.single_apply, hi]
  have heD := hP e he
  omega

theorem eval_partial_eq_zero_of_block_degree_two
    (P : MvPolynomial (Fin n) K) (D : Finset (Fin n))
    (hP : ∀ e ∈ P.support, 2 ≤ ∑ j ∈ D, e j)
    (y : Fin n → K) (hy : ∀ j ∈ D, y j = 0) (i : Fin n) :
    eval y (pderiv i P) = 0 := by
  classical
  apply eval₂Hom_eq_zero (RingHom.id K) y
  intro d hd
  have hpos := derivative_block_degree_pos P D hP i d (Finsupp.mem_support_iff.mpr hd)
  obtain ⟨j, hj, hjd⟩ : ∃ j ∈ D, d j ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hz : (∑ j ∈ D, d j) = 0 := Finset.sum_eq_zero hn
    omega
  exact ⟨j, Finsupp.mem_support_iff.mpr hjd, hy j hj⟩

theorem positiveRemainder_gradient_zero_on_tangent
    (P : MvPolynomial (Fin n) K) (hP : P.IsHomogeneous 3)
    (radial : Fin n) (T : Finset (Fin n)) (hr : radial ∈ T)
    (y : Fin n → K) (hy : ∀ j ∈ Tᶜ, y j = 0) :
    gradient (positiveRemainder P radial T) y = 0 := by
  ext i
  apply eval_partial_eq_zero_of_block_degree_two _ Tᶜ _ y hy i
  intro e he
  have hs := positiveRemainder_support P hP radial T hr e he
  rcases hs.2 with hs | hs <;> omega

theorem gradient_zeroWeightPart_on_tangent
    (P : MvPolynomial (Fin n) K) (hP : P.IsHomogeneous 3)
    (radial : Fin n) (T : Finset (Fin n)) (hr : radial ∈ T)
    (hw : HasNonnegativeWeights P (singularRadialWeight radial T T))
    (y : Fin n → K) (hy : ∀ j ∈ Tᶜ, y j = 0) :
    gradient P y = gradient (zeroWeightPart P (singularRadialWeight radial T T)) y := by
  have hR := positiveRemainder_gradient_zero_on_tangent P hP radial T hr y hy
  ext i
  have he := congrArg (fun Q => eval y (pderiv i Q))
    (equals_zeroWeightPart_add_remainder P radial T hw)
  simp only [map_add] at he
  have hz := congrFun hR i
  change eval y (pderiv i (positiveRemainder P radial T)) = 0 at hz
  simpa only [hz, add_zero] using he

/-- On the nonradial tangent block the normal derivatives of the full
original cubic are exactly the retained normal-map components. -/
theorem normal_partial_on_tangent
    (P : MvPolynomial (Fin n) K) (hP : P.IsHomogeneous 3)
    (radial : Fin n) (T : Finset (Fin n)) (hr : radial ∈ T)
    (hw : HasNonnegativeWeights P (singularRadialWeight radial T T))
    (y : Fin n → K) (hy : ∀ j ∈ Tᶜ, y j = 0) (hyr : y radial = 0)
    (i : Fin n) (hi : i ∈ Tᶜ) :
    eval y (pderiv i P) = eval y
      (normalMapComponent (zeroWeightPart P (singularRadialWeight radial T T)) radial T i) := by
  have hg := congrFun (gradient_zeroWeightPart_on_tangent P hP radial T hr hw y hy) i
  change eval y (pderiv i P) = eval y (pderiv i (zeroWeightPart P _)) at hg
  rw [hg, SingularNormalEquations.normal_partial _ (zeroWeightPart_homogeneous hP _)
    radial T T hr (Finset.Subset.refl T) (zeroWeightPart_weights P _) i hi]
  simp [hyr]

theorem complementaryPart_eq_zero
    (P : MvPolynomial (Fin n) K) (hP : P.IsHomogeneous 3)
    (radial : Fin n) (T : Finset (Fin n)) (hr : radial ∈ T)
    (hw : ∀ d ∈ P.support, monomialWeight (singularRadialWeight radial T T) d = 0) :
    complementaryPart P radial T = 0 := by
  classical
  apply Finsupp.ext
  intro d
  by_contra hd
  have hm : d ∈ (complementaryPart P radial T).support := Finsupp.mem_support_iff.mpr hd
  have hp := (mem_support_exponentPart P _ d).mp hm
  have hdeg : d.degree = 3 := by
    rw [Finsupp.degree_eq_weight_one]
    exact hP (Finsupp.mem_support_iff.mp hp.1)
  have hc := exponent_distribution radial T T hr (Finset.Subset.refl T) d hdeg (hw d hp.1)
  rcases hc with h | h | h <;> omega

/-- Full polynomial equality, including all positive-weight terms. -/
theorem exact_positive_normal_form
    (P : MvPolynomial (Fin n) K) (hP : P.IsHomogeneous 3)
    (radial : Fin n) (T : Finset (Fin n)) (hr : radial ∈ T)
    (hw : HasNonnegativeWeights P (singularRadialWeight radial T T)) :
    P = X radial * normalQuadratic (zeroWeightPart P (singularRadialWeight radial T T)) radial +
      (∑ i ∈ Tᶜ, X i * normalMapComponent (zeroWeightPart P (singularRadialWeight radial T T)) radial T i) +
      positiveRemainder P radial T := by
  have hz := exact_normal_form (zeroWeightPart P (singularRadialWeight radial T T))
    (zeroWeightPart_homogeneous hP _) radial T T hr (Finset.Subset.refl T) (zeroWeightPart_weights P _)
  rw [complementaryPart_eq_zero _ (zeroWeightPart_homogeneous hP _) radial T hr
    (zeroWeightPart_weights P _), add_zero] at hz
  calc
    P = zeroWeightPart P (singularRadialWeight radial T T) + positiveRemainder P radial T :=
      equals_zeroWeightPart_add_remainder P radial T hw
    _ = _ := congrArg (fun Q => Q + positiveRemainder P radial T) hz

/-- The retained quadratic has the Hessian of the original cubic at the
actual radial coordinate point, despite the positive-weight remainder. -/
theorem retained_normalQuadratic_hessian
    (P : MvPolynomial (Fin n) K) (hP : P.IsHomogeneous 3)
    (radial : Fin n) (T : Finset (Fin n)) (hr : radial ∈ T)
    (hw : HasNonnegativeWeights P (singularRadialWeight radial T T)) :
    LocalCubicNormalForm.quadraticMatrix
      (normalQuadratic (zeroWeightPart P (singularRadialWeight radial T T)) radial) =
      hessian P (Pi.single radial 1) := by
  rw [hessian_at_radial P hP radial]
  have hp : pderiv radial P =
      normalQuadratic (zeroWeightPart P (singularRadialWeight radial T T)) radial := by
    conv_lhs => rw [equals_zeroWeightPart_add_remainder P radial T hw]
    rw [map_add, positiveRemainder_radial_partial P hP radial T hr, add_zero]
    exact radial_partial_eq_normalQuadratic _ (zeroWeightPart_homogeneous hP _) radial T T
      hr (Finset.Subset.refl T) (zeroWeightPart_weights P _)
  rw [hp]

/-- Separate actual polynomial rings for the normal quadratic and the
normal-map tuple, with the full remainder retained in the ambient ring. -/
theorem exists_typed_positive_normal_form
    (P : MvPolynomial (Fin n) K) (hP : P.IsHomogeneous 3)
    (radial : Fin n) (T : Finset (Fin n)) (hr : radial ∈ T)
    (hw : HasNonnegativeWeights P (singularRadialWeight radial T T)) :
    ∃ q : MvPolynomial (↑Tᶜ : Type) K,
    ∃ p : (↑Tᶜ : Type) → MvPolynomial (↑(T.erase radial) : Type) K,
      q.IsHomogeneous 2 ∧ (∀ i, (p i).IsHomogeneous 2) ∧
      rename (fun i : (↑Tᶜ : Type) => (i : Fin n)) q =
        normalQuadratic (zeroWeightPart P (singularRadialWeight radial T T)) radial ∧
      (∀ i, rename (fun j : (↑(T.erase radial) : Type) => (j : Fin n)) (p i) =
        normalMapComponent (zeroWeightPart P (singularRadialWeight radial T T)) radial T i) ∧
      P = X radial * rename (fun i : (↑Tᶜ : Type) => (i : Fin n)) q +
        (∑ i : (↑Tᶜ : Type), X (i : Fin n) *
          rename (fun j : (↑(T.erase radial) : Type) => (j : Fin n)) (p i)) +
        positiveRemainder P radial T := by
  classical
  let P₀ := zeroWeightPart P (singularRadialWeight radial T T)
  obtain ⟨q,hq,hqe⟩ := exists_block_polynomial (normalQuadratic P₀ radial)
    (normalQuadratic_homogeneous (zeroWeightPart_homogeneous hP _) radial) Tᶜ
    (normalQuadratic_vars P₀ (zeroWeightPart_homogeneous hP _) radial T T hr (Finset.Subset.refl T)
      (zeroWeightPart_weights P _))
  have hp : ∀ i : (↑Tᶜ : Type), ∃ Q : MvPolynomial (↑(T.erase radial) : Type) K,
      Q.IsHomogeneous 2 ∧ rename (fun j : (↑(T.erase radial) : Type) => (j : Fin n)) Q =
        normalMapComponent P₀ radial T i := by
    intro i
    exact exists_block_polynomial (normalMapComponent P₀ radial T i)
      (normalMapComponent_homogeneous (zeroWeightPart_homogeneous hP _) radial T i) _
      (normalMapComponent_vars P₀ (zeroWeightPart_homogeneous hP _) radial T T hr (Finset.Subset.refl T)
        (zeroWeightPart_weights P _) i i.property)
  choose p hp hpe using hp
  refine ⟨q,p,hq,hp,hqe,hpe,?_⟩
  simp_rw [hqe,hpe]
  rw [Finset.sum_coe_sort Tᶜ (fun i => X i * normalMapComponent P₀ radial T i)]
  exact exact_positive_normal_form P hP radial T hr hw

theorem adapted_indices_eq_of_tangent_eq_kernel
    (F : GeometricPolynomial n) (x : GeometricPoint n)
    (T : Submodule GeometricField (GeometricPoint n))
    (A : AdaptedFlagBasis T (LinearMap.ker (hessian F x).mulVecLin) x)
    (hT : T = LinearMap.ker (hessian F x).mulVecLin) :
    A.tangentIndices = A.kernelIndices := by
  ext i
  rw [← A.mem_tangent_iff, ← A.mem_kernel_iff]
  exact ⟨fun h => hT.le h, fun h => hT.symm.le h⟩

/-- The retained normal quadratic has the actual original Hessian rank
in an adapted basis whose tangent block is the full Hessian kernel. -/
theorem retained_normalQuadratic_rank_in_adapted_flag
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3) (x : GeometricPoint n)
    (T : Submodule GeometricField (GeometricPoint n))
    (A : AdaptedFlagBasis T (LinearMap.ker (hessian F x).mulVecLin) x)
    (hT : T = LinearMap.ker (hessian F x).mulVecLin)
    (htensor : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0) :
    (LocalCubicNormalForm.quadraticMatrix (normalQuadratic
      (zeroWeightPart (PolynomialRestriction.restrict (HessianTheorem11.basisMatrix A.basis) F)
        (singularRadialWeight A.radial A.tangentIndices A.tangentIndices)) A.radial)).rank =
      (hessian F x).rank := by
  let P := PolynomialRestriction.restrict (HessianTheorem11.basisMatrix A.basis) F
  have hPh : P.IsHomogeneous 3 := PolynomialRestriction.homogeneous_restrict _ _ hF
  have hW := nonnegative_in_adapted_flag F hF x T A htensor
  rw [← adapted_indices_eq_of_tangent_eq_kernel F x T A hT] at hW
  rw [retained_normalQuadratic_hessian P hPh A.radial A.tangentIndices A.radial_mem hW]
  have he := BasisHessianTransport.hessian_rank_restrict A.basis F (Pi.single A.radial 1)
  change (hessian P (Pi.single A.radial 1)).rank =
    (hessian F ((HessianTheorem11.basisMatrix A.basis).mulVec (Pi.single A.radial 1))).rank at he
  rw [he, HessianTheorem11.basisMatrix_mulVec_single, A.radial_eq]

/-- The normal quadratic extracted in its actual coordinate ring is
nondegenerate. Its determinant is proved nonzero from the original
Hessian kernel and rank; it is not an extra normal-form premise. -/
theorem typed_normal_det_ne_zero_in_adapted_flag
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3) (x : GeometricPoint n)
    (T : Submodule GeometricField (GeometricPoint n))
    (A : AdaptedFlagBasis T (LinearMap.ker (hessian F x).mulVecLin) x)
    (hT : T = LinearMap.ker (hessian F x).mulVecLin)
    (htensor : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0)
    (q : MvPolynomial (↑A.tangentIndicesᶜ : Type) GeometricField)
    (hqe : rename (fun i : (↑A.tangentIndicesᶜ : Type) => (i : Fin n)) q =
      normalQuadratic
        (zeroWeightPart (PolynomialRestriction.restrict (HessianTheorem11.basisMatrix A.basis) F)
          (singularRadialWeight A.radial A.tangentIndices A.tangentIndices)) A.radial) :
    (SingularNormalEquations.quadraticHessian q).det ≠ 0 := by
  classical
  apply QuadraticBlockRank.typed_normal_det_ne_zero A.tangentIndices q
  rw [hqe]
  change Fintype.card (↑A.tangentIndicesᶜ : Type) ≤
    (LocalCubicNormalForm.quadraticMatrix _).rank
  rw [retained_normalQuadratic_rank_in_adapted_flag F hF x T A hT htensor]
  have hd := (hessian F x).mulVecLin.finrank_range_add_finrank_ker
  change (hessian F x).rank + finrank GeometricField (LinearMap.ker (hessian F x).mulVecLin) =
    finrank GeometricField (GeometricPoint n) at hd
  rw [show finrank GeometricField (GeometricPoint n) = n by simp] at hd
  have ht : A.tangentIndices.card =
      finrank GeometricField (LinearMap.ker (hessian F x).mulVecLin) := by
    rw [adapted_indices_eq_of_tangent_eq_kernel F x T A hT]
    exact A.kernel_card
  rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
  omega

end HessianTheorem11.SingularPositiveNormalForm
