import HessianTheorem11.SaturatedScalarCommonRadical

/-! Actual tangent-pair vanishing in the scalar branch. The tangent
space is recovered from the constructed basis by dimension and span. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix Module
set_option maxRecDepth 4000
set_option maxHeartbeats 1200000

namespace CoisotropicBasis.Data
variable {n m d q : ℕ} {F : GeometricPolynomial n} {x : GeometricPoint n}
  {T : Submodule GeometricField (GeometricPoint n)}
  (D : Data (hessianBilinear F x) T x m d q)

def tangentGenerator : (Fin m ⊕ (Fin q ⊕ Fin d)) → GeometricPoint n :=
  Sum.elim D.radicalVector (Sum.elim D.middleVector D.isotropicVector)

theorem tangentGenerator_span
    (hker : LinearMap.ker (hessian F x).mulVecLin ≤ T) :
    Submodule.span GeometricField (Set.range D.tangentGenerator) = T := by
  classical
  let f : (Fin m ⊕ (Fin q ⊕ Fin d)) → CoisotropicBasis.Index m d q :=
    Sum.elim Sum.inl (Sum.elim (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inr ∘ Sum.inl))
  have hf : Function.Injective f := by
    intro i j hij
    rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
      simp_all [f]
  have hli : LinearIndependent GeometricField D.tangentGenerator := by
    have he : D.tangentGenerator = D.basis ∘ f := by
      funext i
      rcases i with i | (i | i) <;> rfl
    rw [he]
    exact D.basis.linearIndependent.comp f hf
  have hle : Submodule.span GeometricField (Set.range D.tangentGenerator) ≤ T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    rcases i with i | (i | i)
    · exact hker (D.radical_hessian_kernel i)
    · exact D.tangent_middle i
    · exact D.tangent_isotropic i
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hs := finrank_span_eq_card hli
  simp only [Fintype.card_sum,Fintype.card_fin] at hs
  have hc := D.codimension
  have hd := D.dimension
  simp only [Module.finrank_pi,Fintype.card_fin] at hc hd
  change d + finrank GeometricField T = n at hc
  omega

theorem bilinear_zero_on_tangent_of_generators
    (hker : LinearMap.ker (hessian F x).mulVecLin ≤ T)
    (B : LinearMap.BilinForm GeometricField (GeometricPoint n))
    (hB : ∀ i j, B (D.tangentGenerator i) (D.tangentGenerator j) = 0) :
    ∀ t ∈ T, ∀ u ∈ T, B t u = 0 := by
  intro t ht u hu
  rw [← D.tangentGenerator_span hker] at ht hu
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨i,rfl⟩ := ht
    induction hu using Submodule.span_induction with
    | mem u hu => obtain ⟨j,rfl⟩ := hu; exact hB i j
    | zero => exact map_zero _
    | add u v hu hv ihu ihv => rw [map_add,ihu,ihv,add_zero]
    | smul c u hu ihu => rw [map_smul,ihu,smul_zero]
  | zero => simp
  | add t v ht hv iht ihv => simp only [map_add,LinearMap.add_apply,iht,ihv,add_zero]
  | smul c t ht iht => simp only [map_smul,LinearMap.smul_apply,iht,smul_zero]

end CoisotropicBasis.Data

namespace CoisotropicBasis.Data
variable {F : GeometricPolynomial 13} {x : GeometricPoint 13}
  {T : Submodule GeometricField (GeometricPoint 13)}
  (D : Data (hessianBilinear F x) T x 5 2 4)

theorem scalar_tangent_pair_zero (hF : F.IsHomogeneous 3)
    (hker : LinearMap.ker (hessian F x).mulVecLin ≤ T)
    (η : Fin 2) (hη : η ≠ D.radial)
    (z : GeometricPoint 5) (he : D.fourE hF η z = 0) (hM : D.fourM hF z = 0)
    (hC : D.isotropicGramAt (D.radicalMatrix.mulVec z) = 0)
    (hUA : ∀ a y, polarization F (D.radicalMatrix.mulVec z) (D.radicalMatrix.mulVec a) y = 0) :
    ∀ t ∈ T, ∀ u ∈ T, polarization F (D.radicalMatrix.mulVec z) t u = 0 := by
  let v := D.radicalMatrix.mulVec z
  have hrad (y : GeometricPoint 13) : polarization F v x y = 0 := by
    rw [polarization_swap_first,polarization_swap_last hF]
    change dotProduct x ((hessian F v).mulVec y) = 0
    rw [← polarization]
    rw [polarization_swap_first,polarization_swap_last hF]
    change dotProduct y ((hessian F x).mulVec v) = 0
    rw [show (hessian F x).mulVec v = 0 from D.radicalMatrix_mem_kernel z]
    simp
  have hBB (i j : Fin 4) : polarization F v (D.middleVector i) (D.middleVector j) = 0 := by
    have hh := D.fourM_pairing hF z (Pi.single i 1) (Pi.single j 1)
    rw [hM] at hh
    simpa only [LinearMap.zero_apply,map_zero,LinearMap.zero_apply,
      Matrix.mulVec_single_one] using hh.symm
  have hKB (i : Fin 2) (j : Fin 4) :
      polarization F v (D.isotropicVector i) (D.middleVector j) = 0 := by
    by_cases hi : i = D.radial
    · subst i
      change polarization F v (D.basis (Sum.inr (Sum.inr (Sum.inl D.radial)))) _ = 0
      rw [D.radial_eq]
      exact hrad _
    · have hiη : i = η := by
        apply Fin.ext
        have h₁ : i.val ≠ D.radial.val := fun h => hi (Fin.ext h)
        have h₂ : η.val ≠ D.radial.val := fun h => hη (Fin.ext h)
        have hi' := i.isLt
        have hη' := η.isLt
        have hr' := D.radial.isLt
        omega
      subst i
      have hh := D.fourE_pairing hF η z (Pi.single j 1)
      rw [he] at hh
      simpa only [map_zero,LinearMap.zero_apply,Matrix.mulVec_single_one] using hh.symm
  have hKK (i j : Fin 2) : polarization F v (D.isotropicVector i) (D.isotropicVector j) = 0 := by
    have hh := congrFun (congrFun hC i) j
    change polarization F (D.isotropicVector i) (D.isotropicVector j) v = 0 at hh
    rwa [polarization_rotate hF] at hh
  have hA (i : Fin 5) (y : GeometricPoint 13) :
      polarization F v (D.radicalVector i) y = 0 := by
    simpa only [Matrix.mulVec_single_one] using hUA (Pi.single i 1) y
  have hgen (i j : Fin 5 ⊕ (Fin 4 ⊕ Fin 2)) :
      polarization F v (D.tangentGenerator i) (D.tangentGenerator j) = 0 := by
    rcases i with i | (i | i) <;> rcases j with j | (j | j)
    · exact hA i _
    · exact hA i _
    · exact hA i _
    · rw [polarization_swap_last hF]; exact hA j _
    · exact hBB i j
    · rw [polarization_swap_last hF]; exact hKB j i
    · rw [polarization_swap_last hF]; exact hA j _
    · exact hKB i j
    · exact hKK i j
  intro t ht u hu
  have hh := D.bilinear_zero_on_tangent_of_generators hker (hessianBilinear F v)
    (fun i j => by
      rw [hessianBilinear_apply,polarization_rotate hF]
      exact hgen i j) t ht u hu
  rw [hessianBilinear_apply] at hh
  exact (polarization_rotate hF t u v).symm.trans hh

end CoisotropicBasis.Data
end HessianTheorem11
