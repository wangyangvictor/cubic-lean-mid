import HessianTheorem11.SingularNormalJacobian
import HessianTheorem11.SingularRankFourWitness
import HessianTheorem11.SingularExtraRadical
import HessianTheorem11.QuadraticCommonRadical
import HessianTheorem11.TangentBundleGeometry

/-! A genuine differential radical of the extracted normal tuple gives an
additional common radical direction of the original cubic. -/

noncomputable section
namespace HessianTheorem11.SingularNormalPairing
open MvPolynomial Matrix Module PolynomialRestriction TangentHessianRank
open SingularRadialNormalForm SingularPositiveNormalForm NonzeroLimitTransport SingularRadialEquality

variable {n : ℕ}

theorem normal_tuple_linearGradient
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3) (x : GeometricPoint n)
    (T L : Submodule GeometricField (GeometricPoint n)) (A : AdaptedFlagBasis T L x)
    (hW : HasNonnegativeWeights (restrict (HessianTheorem11.basisMatrix A.basis) F)
      (singularRadialWeight A.radial A.tangentIndices A.tangentIndices))
    (p : (↑A.tangentIndicesᶜ : Type) →
      MvPolynomial (↑(A.tangentIndices.erase A.radial) : Type) GeometricField)
    (hpe : ∀ i, rename (fun j : (↑(A.tangentIndices.erase A.radial) : Type) => (j : Fin n)) (p i) =
      normalMapComponent
        (zeroWeightPart (restrict (HessianTheorem11.basisMatrix A.basis) F)
          (singularRadialWeight A.radial A.tangentIndices A.tangentIndices))
        A.radial A.tangentIndices i) :
    p = fun i : (↑A.tangentIndicesᶜ : Type) => ∑ k, C ((HessianTheorem11.basisMatrix A.basis) k i) *
      restrict ((HessianTheorem11.basisMatrix A.basis) *
        (QuadraticBlockRank.renamingMatrix (K := GeometricField)
          (fun j : (↑(A.tangentIndices.erase A.radial) : Type) => (j : Fin n))).transpose) (pderiv k F) := by
  classical
  let B := HessianTheorem11.basisMatrix A.basis
  let E := (QuadraticBlockRank.renamingMatrix (K := GeometricField)
    (fun i : (↑(A.tangentIndices.erase A.radial) : Type) => (i : Fin n))).transpose
  let C₀ := B * E
  let P := restrict B F
  have hP : P.IsHomogeneous 3 := homogeneous_restrict _ _ hF
  have hC (u : (↑(A.tangentIndices.erase A.radial) : Type) → GeometricField) :
      C₀.mulVec u = B.mulVec (blockExtension (A.tangentIndices.erase A.radial) u) := by
    rw [show C₀ = B * E from rfl, ← Matrix.mulVec_mulVec,
      transpose_renaming_mulVec_eq_blockExtension]
  funext i
  apply MvPolynomial.funext
  intro u
  let y := blockExtension (A.tangentIndices.erase A.radial) u
  have hy (j : Fin n) (hj : j ∈ A.tangentIndicesᶜ) : y j = 0 := by
    apply blockExtension_zero
    intro hm
    exact Finset.mem_compl.mp hj (Finset.mem_of_mem_erase hm)
  have hyr : y A.radial = 0 := blockExtension_zero _ u _ (Finset.notMem_erase _ _)
  have hn := normal_partial_on_tangent P hP A.radial A.tangentIndices A.radial_mem hW y hy hyr i i.property
  rw [← hpe i, eval_rename] at hn
  have hyu : (y ∘ fun j : (↑(A.tangentIndices.erase A.radial) : Type) => (j : Fin n)) = u := by
    funext j
    exact blockExtension_coe _ u j
  rw [hyu] at hn
  rw [← hn]
  have hg := congrFun (gradient_restrict B F y) i
  change eval y (pderiv (i : Fin n) P) = (B.transpose.mulVec (gradient F (B.mulVec y))) i at hg
  rw [hg]
  simp only [map_sum, map_mul, eval_C, eval_restrict]
  change (∑ k, B k i * eval (B.mulVec y) (pderiv k F)) =
    ∑ k, B k i * eval (C₀.mulVec u) (pderiv k F)
  rw [hC]

theorem basis_transpose_mulVec_injective
    (b : Basis (Fin n) GeometricField (GeometricPoint n)) :
    Function.Injective (HessianTheorem11.basisMatrix b).transpose.mulVec := by
  apply Matrix.mulVec_injective_iff_isUnit.mpr
  rw [Matrix.isUnit_transpose]
  exact Matrix.mulVec_injective_iff_isUnit.mp (basisMatrix_injective b)

/-- Nonzero tangent tuple radicals lift to actual common radical vectors,
with nonradiality certified in the actual basis coordinates. -/
theorem normal_tuple_radical_lifts
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3) (x : GeometricPoint n)
    (T : Submodule GeometricField (GeometricPoint n))
    (A : AdaptedFlagBasis T (LinearMap.ker (hessian F x).mulVecLin) x)
    (hT : T = LinearMap.ker (hessian F x).mulVecLin)
    (htensor : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0)
    (p : (↑A.tangentIndicesᶜ : Type) →
      MvPolynomial (↑(A.tangentIndices.erase A.radial) : Type) GeometricField)
    (hpe : ∀ i, rename (fun j : (↑(A.tangentIndices.erase A.radial) : Type) => (j : Fin n)) (p i) =
      normalMapComponent
        (zeroWeightPart (restrict (HessianTheorem11.basisMatrix A.basis) F)
          (singularRadialWeight A.radial A.tangentIndices A.tangentIndices))
        A.radial A.tangentIndices i)
    (u : (↑(A.tangentIndices.erase A.radial) : Type) → GeometricField)
    (hu : u ≠ 0) (hpu : ∀ a, (polynomialJacobian p a).mulVec u = 0) :
    ∃ v ∈ singularNormalCommonRadical F T, v ∉ Submodule.span GeometricField {x} := by
  classical
  let B := HessianTheorem11.basisMatrix A.basis
  let E := (QuadraticBlockRank.renamingMatrix (K := GeometricField)
    (fun i : (↑(A.tangentIndices.erase A.radial) : Type) => (i : Fin n))).transpose
  let C₀ := B * E
  let D : Matrix (↑A.tangentIndicesᶜ : Type) (Fin n) GeometricField := fun i k => B k i
  have hC (a : (↑(A.tangentIndices.erase A.radial) : Type) → GeometricField) :
      C₀.mulVec a = B.mulVec (blockExtension (A.tangentIndices.erase A.radial) a) := by
    rw [show C₀ = B * E from rfl, ← Matrix.mulVec_mulVec,
      transpose_renaming_mulVec_eq_blockExtension]
  have hCT (a : (↑(A.tangentIndices.erase A.radial) : Type) → GeometricField) : C₀.mulVec a ∈ T := by
    rw [hC]
    exact blockExtension_in_tangent T _ x A a
  have hW := nonnegative_in_adapted_flag F hF x T A htensor
  rw [← adapted_indices_eq_of_tangent_eq_kernel F x T A hT] at hW
  have hp := normal_tuple_linearGradient F hF x T _ A hW p hpe
  have hJac (a : (↑(A.tangentIndices.erase A.radial) : Type) → GeometricField) :
      polynomialJacobian p a = D * hessian F (C₀.mulVec a) * C₀ := by
    rw [hp]
    exact linearGradient_jacobian F C₀ D a
  have hHu (a : (↑(A.tangentIndices.erase A.radial) : Type) → GeometricField) :
      (hessian F (C₀.mulVec a)).mulVec (C₀.mulVec u) = 0 := by
    apply basis_transpose_mulVec_injective A.basis
    rw [Matrix.mulVec_zero]
    ext i
    by_cases hi : i ∈ A.tangentIndices
    · have he := htensor (A.basis i) ((A.mem_tangent_iff i).mpr hi)
        (C₀.mulVec u) (hT.le (hCT u)) (C₀.mulVec a) (hT.le (hCT a))
      exact he
    · have he := congrFun (hpu a) ⟨i,Finset.mem_compl.mpr hi⟩
      rw [hJac, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at he
      exact he
  let V : Submodule GeometricField (GeometricPoint n) :=
    LinearMap.ker (pencilVariation (hessianLinearMap F hF) (C₀.mulVec u))
  have hTV : T ≤ V := by
    rw [← A.tangent_span]
    apply Submodule.span_le.mpr
    rintro v ⟨i,hi,rfl⟩
    by_cases hir : i = A.radial
    · subst i
      change (hessian F (A.basis A.radial)).mulVec (C₀.mulVec u) = 0
      rw [A.radial_eq]
      exact hT.le (hCT u)
    · let j : (↑(A.tangentIndices.erase A.radial) : Type) := ⟨i,Finset.mem_erase.mpr ⟨hir,hi⟩⟩
      have he : C₀.mulVec (Pi.single j 1) = A.basis i := by
        rw [hC]
        have hy : blockExtension (A.tangentIndices.erase A.radial) (Pi.single j 1) = Pi.single i 1 := by
          ext k
          by_cases hk : k ∈ A.tangentIndices.erase A.radial
          · simp only [blockExtension, dif_pos hk, Pi.single_apply]
            have heq : (⟨k,hk⟩ : (↑(A.tangentIndices.erase A.radial) : Type)) = j ↔ k = i := Subtype.ext_iff
            simp only [heq]
          · have hki : k ≠ i := by rintro rfl; exact hk j.property
            simp [blockExtension, hk, Pi.single_apply, hki]
        rw [hy, HessianTheorem11.basisMatrix_mulVec_single]
      change (hessian F (A.basis i)).mulVec (C₀.mulVec u) = 0
      rw [← he]
      exact hHu _
  refine ⟨C₀.mulVec u, ⟨hCT u, ?_⟩, ?_⟩
  · intro v hv w
    rw [polarization_rotate hF]
    change dotProduct w ((hessian F v).mulVec (C₀.mulVec u)) = 0
    have he : (hessian F v).mulVec (C₀.mulVec u) = 0 := hTV hv
    rw [he]
    simp
  · intro hm
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hm
    have hx : x = B.mulVec (Pi.single A.radial 1) := by
      rw [HessianTheorem11.basisMatrix_mulVec_single, A.radial_eq]
    rw [hC] at hc
    have hc' : c • B.mulVec (Pi.single A.radial 1) =
        B.mulVec (blockExtension (A.tangentIndices.erase A.radial) u) :=
      (congrArg (fun z : GeometricPoint n => c • z) hx).symm.trans hc
    rw [← Matrix.mulVec_smul] at hc'
    have he := basisMatrix_injective A.basis hc' 
    have hc0 : c = 0 := by
      have hr := congrFun he A.radial
      simpa [blockExtension, Pi.single_apply] using hr
    rw [hc0] at he
    apply hu
    funext i
    have hi := congrFun he i
    simpa only [zero_smul, Pi.zero_apply, blockExtension_coe] using hi.symm

/-- Semistability excludes every nonzero normal-tuple differential radical
in the dimensions used for S11 and S12. -/
theorem normal_tuple_radical_impossible
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3) (hsemi : WeightSemistable F)
    (x : GeometricPoint n) (T : Submodule GeometricField (GeometricPoint n))
    (A : AdaptedFlagBasis T (LinearMap.ker (hessian F x).mulVecLin) x)
    (hT : T = LinearMap.ker (hessian F x).mulVecLin)
    (htensor : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0)
    (hdim : 2 * n < 3 * finrank GeometricField T + 6)
    (p : (↑A.tangentIndicesᶜ : Type) →
      MvPolynomial (↑(A.tangentIndices.erase A.radial) : Type) GeometricField)
    (hpe : ∀ i, rename (fun j : (↑(A.tangentIndices.erase A.radial) : Type) => (j : Fin n)) (p i) =
      normalMapComponent
        (zeroWeightPart (restrict (HessianTheorem11.basisMatrix A.basis) F)
          (singularRadialWeight A.radial A.tangentIndices A.tangentIndices))
        A.radial A.tangentIndices i)
    (u : (↑(A.tangentIndices.erase A.radial) : Type) → GeometricField)
    (hu : u ≠ 0) (hpu : ∀ a, (polynomialJacobian p a).mulVec u = 0) : False := by
  classical
  have hx : x ≠ 0 := by rw [← A.radial_eq]; exact A.basis.ne_zero A.radial
  have hxT : x ∈ T := by
    have h := (A.mem_tangent_iff A.radial).mpr A.radial_mem
    rwa [A.radial_eq] at h
  have hk : ∀ t ∈ T, (hessian F x).mulVec t = 0 := fun t ht => hT.le ht
  have ht : ∀ u ∈ T, ∀ v ∈ T, ∀ w ∈ T, polarization F u v w = 0 :=
    fun u hu v hv w hw => htensor u hu v (hT.le hv) w (hT.le hw)
  have hbound := singularNormalCommonRadical_finrank_le_one F hF hsemi x hx T hxT hk ht hdim
  obtain ⟨v,hv,hvn⟩ := normal_tuple_radical_lifts F hF x T A hT htensor p hpe u hu hpu
  have hxS : x ∈ singularNormalCommonRadical F T := by
    refine ⟨hxT, ?_⟩
    intro v hv w
    rw [polarization_rotate hF, polarization_swap_last hF]
    change dotProduct w ((hessian F x).mulVec v) = 0
    rw [hk v hv]
    simp
  have hle : Submodule.span GeometricField {x} ≤ singularNormalCommonRadical F T :=
    (Submodule.span_singleton_le_iff_mem x _).mpr hxS
  have he : Submodule.span GeometricField {x} = singularNormalCommonRadical F T := by
    apply Submodule.eq_of_le_of_finrank_le hle
    simpa [finrank_span_singleton hx] using hbound
  exact hvn (he.symm ▸ hv)


/-- Reindexing a normal tuple transports its actual common differential radical. -/
theorem normalTuple_radical_coordinates {r s : ℕ}
    {T : Finset (Fin n)} {c : Fin n} (D : GradedIndexCoordinates T c r s)
    (p : (↑Tᶜ : Type) → MvPolynomial (↑(T.erase c) : Type) GeometricField)
    (u : GeometricPoint s) (hu : u ≠ 0)
    (hpu : u ∈ polynomialTupleDifferentialRadical (D.normalTuple p)) :
    (u ∘ D.tangent.symm) ≠ 0 ∧
      ∀ a, (polynomialJacobian p a).mulVec (u ∘ D.tangent.symm) = 0 := by
  classical
  refine ⟨?_, ?_⟩
  · intro he
    apply hu
    funext i
    have hi := congrFun he (D.tangent i)
    simpa using hi
  · intro a
    have hzero : (polynomialJacobian (D.normalTuple p) (a ∘ D.tangent)).mulVec u = 0 := by
      ext i
      simpa only [polynomialDifferential_apply, polynomialJacobian, Matrix.mulVec,
        dotProduct, Pi.zero_apply] using
        (mem_polynomialTupleDifferentialRadical _ u).mp hpu (a ∘ D.tangent) i
    rw [D.normalTuple_jacobian] at hzero
    have hae : (a ∘ D.tangent) ∘ D.tangent.symm = a := by funext i; simp
    rw [hae] at hzero
    ext i
    have hi := congrFun hzero (D.normal.symm i)
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, D.normal.apply_symm_apply,
      Pi.zero_apply] at hi ⊢
    rw [← D.tangent.sum_comp (fun j => polynomialJacobian p a i j * (u ∘ D.tangent.symm) j)]
    simpa only [Function.comp_apply, D.tangent.symm_apply_apply] using hi

theorem normal_tuple_differentialRadical_eq_bot {r s : ℕ}
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3) (hsemi : WeightSemistable F)
    (x : GeometricPoint n) (T : Submodule GeometricField (GeometricPoint n))
    (A : AdaptedFlagBasis T (LinearMap.ker (hessian F x).mulVecLin) x)
    (hT : T = LinearMap.ker (hessian F x).mulVecLin)
    (htensor : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0)
    (hdim : 2 * n < 3 * finrank GeometricField T + 6)
    (p : (↑A.tangentIndicesᶜ : Type) →
      MvPolynomial (↑(A.tangentIndices.erase A.radial) : Type) GeometricField)
    (hpe : ∀ i, rename (fun j : (↑(A.tangentIndices.erase A.radial) : Type) => (j : Fin n)) (p i) =
      normalMapComponent
        (zeroWeightPart (restrict (HessianTheorem11.basisMatrix A.basis) F)
          (singularRadialWeight A.radial A.tangentIndices A.tangentIndices))
        A.radial A.tangentIndices i)
    (D : GradedIndexCoordinates A.tangentIndices A.radial r s) :
    polynomialTupleDifferentialRadical (D.normalTuple p) = ⊥ := by
  classical
  apply le_antisymm _ bot_le
  intro u hu
  change u = 0
  by_contra hune
  obtain ⟨hne,hJac⟩ := normalTuple_radical_coordinates D p u hune hu
  exact normal_tuple_radical_impossible F hF hsemi x T A hT htensor hdim p hpe
    (u ∘ D.tangent.symm) hne hJac

end HessianTheorem11.SingularNormalPairing
