import HessianTheorem11.SingularNormalPairing

/-! The derivative of the actual extracted normal tuple is a compression
of the original Hessian restricted to the singular tangent space. -/

noncomputable section
namespace HessianTheorem11.SingularNormalPairing
open MvPolynomial Module Matrix PolynomialRestriction
open SingularRadialNormalForm SingularPositiveNormalForm SingularNormalEquations
open SingularRadialEquality NonzeroLimitTransport TangentHessianRank

variable {n : ℕ}

theorem transpose_renaming_mulVec_eq_blockExtension
    (T : Finset (Fin n)) (a : (↑T : Type) → GeometricField) :
    (QuadraticBlockRank.renamingMatrix (fun i : (↑T : Type) => (i : Fin n))).transpose.mulVec a =
      blockExtension T a := by
  classical
  ext i
  by_cases hi : i ∈ T
  · exact (transpose_renaming_mulVec_coe T a ⟨i,hi⟩).trans
      (blockExtension_coe T a ⟨i,hi⟩).symm
  · rw [transpose_renaming_mulVec_zero T a i hi, blockExtension_zero T a i hi]

theorem linearGradient_jacobian {σ τ : Type*} [Fintype σ] [Fintype τ]
    (F : GeometricPolynomial n) (C₀ : Matrix (Fin n) σ GeometricField)
    (D : Matrix τ (Fin n) GeometricField) (a : σ → GeometricField) :
    polynomialJacobian (fun i => ∑ k, C (D i k) * restrict C₀ (pderiv k F)) a =
      D * hessian F (C₀.mulVec a) * C₀ := by
  classical
  ext i j
  simp only [polynomialJacobian, map_sum, Derivation.leibniz, pderiv_C, smul_eq_mul,
    zero_mul, mul_zero, add_zero, pderiv_restrict, map_mul, eval_C, eval_restrict,
    hessian, hessianPolynomial, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Rank of the literal normal Jacobian is bounded by the original
Hessian map restricted to the actual tangent space. -/
theorem normal_jacobian_rank_le_tangent_hessian
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
    (a : (↑(A.tangentIndices.erase A.radial) : Type) → GeometricField) :
    (polynomialJacobian p a).rank ≤ finrank GeometricField (LinearMap.range
      ((hessian F ((HessianTheorem11.basisMatrix A.basis).mulVec
        (blockExtension (A.tangentIndices.erase A.radial) a))).mulVecLin.domRestrict T)) := by
  classical
  let B := HessianTheorem11.basisMatrix A.basis
  let E := (QuadraticBlockRank.renamingMatrix (K := GeometricField)
    (fun i : (↑(A.tangentIndices.erase A.radial) : Type) => (i : Fin n))).transpose
  let C₀ := B * E
  let D : Matrix (↑A.tangentIndicesᶜ : Type) (Fin n) GeometricField := fun i k => B k i
  let P := restrict B F
  have hP : P.IsHomogeneous 3 := homogeneous_restrict _ _ hF
  have hW := nonnegative_in_adapted_flag F hF x T A htensor
  rw [← adapted_indices_eq_of_tangent_eq_kernel F x T A hT] at hW
  have hC (u : (↑(A.tangentIndices.erase A.radial) : Type) → GeometricField) :
      C₀.mulVec u = B.mulVec (blockExtension (A.tangentIndices.erase A.radial) u) := by
    rw [show C₀ = B * E from rfl, ← Matrix.mulVec_mulVec,
      transpose_renaming_mulVec_eq_blockExtension]
  have hp : p = fun i => ∑ k, C (D i k) * restrict C₀ (pderiv k F) := by
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
    simp only [map_sum, map_mul, eval_C, eval_restrict, hC]
    change (∑ k, B k i * eval (B.mulVec y) (pderiv k F)) = _
    rfl
  rw [hp, linearGradient_jacobian]
  have hr := Matrix.rank_mul_le_right D (hessian F (C₀.mulVec a) * C₀)
  rw [← Matrix.mul_assoc] at hr
  apply hr.trans
  change finrank GeometricField (LinearMap.range
    (hessian F (C₀.mulVec a) * C₀).mulVecLin) ≤ _
  rw [Matrix.mulVecLin_mul, LinearMap.range_comp, hC, LinearMap.range_domRestrict]
  apply Submodule.finrank_mono
  apply Submodule.map_mono
  rintro v ⟨u,rfl⟩
  change C₀.mulVec u ∈ T
  rw [hC]
  exact blockExtension_in_tangent T _ x A u

end HessianTheorem11.SingularNormalPairing
