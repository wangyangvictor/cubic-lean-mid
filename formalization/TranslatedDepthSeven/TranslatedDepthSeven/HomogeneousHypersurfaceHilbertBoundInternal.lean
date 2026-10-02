import TranslatedDepthSeven.ProjectiveZerofoldFirstChartInternal
import TranslatedDepthSeven.ProjectiveCurveSalbergerConstant

/-!
# The Hilbert-function inequality for a proper hypersurface section

Multiplication by a form outside a prime ideal is injective.  Its image in
one homogeneous piece lies in the kernel of the map to the hypersurface
section.  Rank-nullity therefore gives the needed inequality without any
geometric Bezout input or an assumption that the section is reduced.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

universe u v

variable {K : Type u} [Field K] {σ : Type v} [Finite σ]

/-- The two adjacent homogeneous pieces inject and surject around a
proper homogeneous hypersurface section.  Only the resulting inequality
is needed; no exactness assertion is assumed. -/
theorem finrank_homogeneous_hypersurface_section_add_le
    (I : Ideal (MvPolynomial σ K)) (hI : I.IsPrime)
    (G : MvPolynomial σ K) {k : ℕ} (hGhom : G.IsHomogeneous k)
    (hGI : G ∉ I) (n : ℕ) :
    Module.finrank K
        (quotientHomogeneousComponent K σ
          (I ⊔ Ideal.span ({G} : Set _)) (k + n)) +
      Module.finrank K (quotientHomogeneousComponent K σ I n) ≤
        Module.finrank K (quotientHomogeneousComponent K σ I (k + n)) := by
  classical
  letI : I.IsPrime := hI
  let J := I ⊔ Ideal.span ({G} : Set (MvPolynomial σ K))
  let A := MvPolynomial σ K ⧸ I
  let B := MvPolynomial σ K ⧸ J
  let H := quotientHomogeneousComponent K σ I
  let HJ := quotientHomogeneousComponent K σ J
  let q : A →ₐ[K] B := Ideal.Quotient.factorₐ K le_sup_left
  let f : H (k + n) →ₗ[K] HJ (k + n) :=
    (q.toLinearMap.comp (H (k + n)).subtype).codRestrict _ (by
      intro x
      obtain ⟨a, ha, hax⟩ := Submodule.mem_map.1 x.2
      refine Submodule.mem_map.2 ⟨a, ha, ?_⟩
      change Ideal.Quotient.mk J a = q x.1
      rw [← hax]
      rfl)
  have hfSurj : Function.Surjective f := by
    intro y
    obtain ⟨a, ha, hay⟩ := Submodule.mem_map.1 y.2
    refine ⟨⟨Ideal.Quotient.mk I a,
      Submodule.mem_map.2 ⟨a, ha, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    exact hay
  let g : H n →ₗ[K] H (k + n) :=
    ((LinearMap.mulLeft K (Ideal.Quotient.mk I G)).comp (H n).subtype).codRestrict _
      (by
        intro x
        obtain ⟨a, ha, hax⟩ := Submodule.mem_map.1 x.2
        refine Submodule.mem_map.2 ⟨G * a, hGhom.mul ha, ?_⟩
        change Ideal.Quotient.mk I (G * a) = Ideal.Quotient.mk I G * x.1
        rw [map_mul, ← hax]
        rfl)
  have hgInj : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    have hval := congrArg Subtype.val hxy
    change Ideal.Quotient.mk I G * x.1 = Ideal.Quotient.mk I G * y.1 at hval
    apply mul_left_cancel₀ _ hval
    exact fun hz ↦ hGI ((Ideal.Quotient.eq_zero_iff_mem).1 hz)
  have hGJ : G ∈ J :=
    (show Ideal.span ({G} : Set (MvPolynomial σ K)) ≤ J from le_sup_right)
      (Ideal.subset_span (Set.mem_singleton _))
  have hgKer : ∀ x, g x ∈ LinearMap.ker f := by
    intro x
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change q (Ideal.Quotient.mk I G * x.1) = 0
    rw [map_mul]
    have hz : q (Ideal.Quotient.mk I G) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).2 hGJ
    rw [hz, zero_mul]
  let gKer : H n →ₗ[K] LinearMap.ker f := g.codRestrict _ hgKer
  have hgKerInj : Function.Injective gKer := by
    intro x y hxy
    apply hgInj
    exact congrArg Subtype.val hxy
  have hrank := LinearMap.finrank_le_finrank_of_injective hgKerInj
  have hnull := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.2 hfSurj] at hnull
  simp only [finrank_top] at hnull
  change Module.finrank K (H n) ≤ Module.finrank K (LinearMap.ker f) at hrank
  change Module.finrank K (HJ (k + n)) + Module.finrank K (H n) ≤
    Module.finrank K (H (k + n))
  omega

end

end TranslatedDepthSeven
