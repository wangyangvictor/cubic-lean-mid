import TranslatedDepthSeven.HomogeneousColonChainInternal
import TranslatedDepthSeven.StandardGradedQuotientFiltration

/-!
# The homogeneous Hilbert-function identity for a principal colon

This is the exact sequence
`0 → (S/(I:G))_n → (S/I)_(n+k) → (S/(I+(G)))_(n+k) → 0`
for a homogeneous ideal and a degree-`k` form.  Primality and reducedness are
not required.  Together with stabilization of principal colons, it is the
algebraic recurrence in the elementary proof of Hilbert--Serre.
-/

namespace TranslatedDepthSeven

noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

/-- Multiplication by `G`, with exactly its kernel divided out. -/
def colonQuotientMultiplication
    (K : Type*) [Field K] {R : Type*} [CommRing R] [Algebra K R]
    (I : Ideal R) (G : R) :
    (R ⧸ I.colon (Ideal.span ({G} : Set R))) →ₗ[K] R ⧸ I :=
  (I.colon (Ideal.span ({G} : Set R))).restrictScalars K |>.liftQ
    ((Ideal.Quotient.mkₐ K I).toLinearMap.comp (LinearMap.mulRight K G)) (by
      intro p hp
      change Ideal.Quotient.mk I (p * G) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_colon_singleton.mp hp))

@[simp] theorem colonQuotientMultiplication_mk
    (K : Type*) [Field K] {R : Type*} [CommRing R] [Algebra K R]
    (I : Ideal R) (G p : R) :
    colonQuotientMultiplication K I G
      (Ideal.Quotient.mk (I.colon (Ideal.span ({G} : Set R))) p) =
        Ideal.Quotient.mk I (p * G) := rfl

theorem colonQuotientMultiplication_injective
    (K : Type*) [Field K] {R : Type*} [CommRing R] [Algebra K R]
    (I : Ideal R) (G : R) : Function.Injective (colonQuotientMultiplication K I G) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  apply Ideal.Quotient.eq.mpr
  apply Ideal.mem_colon_singleton.mpr
  rw [sub_mul]
  exact Ideal.Quotient.eq.mp hxy

/-- Exact homogeneous Hilbert-function recurrence, also valid for a
nonreduced quotient and for forms that are zero divisors. -/
theorem finrank_homogeneous_section_add_colon_eq
    {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    (G : MvPolynomial σ K) {k : ℕ} (hG : G.IsHomogeneous k) (n : ℕ) :
    Module.finrank K (quotientHomogeneousComponent K σ
      (I ⊔ Ideal.span ({G} : Set (MvPolynomial σ K))) (n + k)) +
    Module.finrank K (quotientHomogeneousComponent K σ
      (I.colon (Ideal.span ({G} : Set (MvPolynomial σ K)))) n) =
    Module.finrank K (quotientHomogeneousComponent K σ I (n + k)) := by
  classical
  let C := I.colon (Ideal.span ({G} : Set (MvPolynomial σ K)))
  let J := I ⊔ Ideal.span ({G} : Set (MvPolynomial σ K))
  let H := quotientHomogeneousComponent K σ I
  let HC := quotientHomogeneousComponent K σ C
  let HJ := quotientHomogeneousComponent K σ J
  let q := Ideal.Quotient.factorₐ K (show I ≤ J from le_sup_left)
  let f : H (n + k) →ₗ[K] HJ (n + k) :=
    (q.toLinearMap.comp (H (n + k)).subtype).codRestrict _ (by
      intro x
      obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.2
      refine Submodule.mem_map.mpr ⟨p, hp, ?_⟩
      change Ideal.Quotient.mk J p = q x.1
      rw [← hpx]
      rfl)
  have hfSurj : Function.Surjective f := by
    intro y
    obtain ⟨p, hp, hpy⟩ := Submodule.mem_map.mp y.2
    exact ⟨⟨Ideal.Quotient.mk I p, Submodule.mem_map.mpr ⟨p, hp, rfl⟩⟩,
      Subtype.ext hpy⟩
  let μ := colonQuotientMultiplication K I G
  let g : HC n →ₗ[K] H (n + k) :=
    (μ.comp (HC n).subtype).codRestrict _ (by
      intro x
      obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.2
      refine Submodule.mem_map.mpr ⟨p * G, hp.mul hG, ?_⟩
      change Ideal.Quotient.mk I (p * G) = μ x.1
      rw [← hpx]
      rfl)
  have hgInj : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    exact colonQuotientMultiplication_injective K I G (congrArg Subtype.val hxy)
  have hgKer : ∀ x, g x ∈ LinearMap.ker f := by
    intro x
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.2
    change q (μ x.1) = 0
    rw [← hpx]
    change Ideal.Quotient.mk J (p * G) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact (show Ideal.span ({G} : Set _) ≤ J from le_sup_right)
      (Ideal.mem_span_singleton'.mpr ⟨p, rfl⟩)
  let gKer : HC n →ₗ[K] LinearMap.ker f := g.codRestrict _ hgKer
  have hgKerInj : Function.Injective gKer := by
    intro x y hxy
    exact hgInj (congrArg Subtype.val hxy)
  have hgKerSurj : Function.Surjective gKer := by
    intro y
    obtain ⟨p, hp, hpy⟩ := Submodule.mem_map.mp y.1.2
    have hpJ : p ∈ J := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      have hy := congrArg Subtype.val (LinearMap.mem_ker.mp y.2)
      change q y.1.1 = 0 at hy
      rw [← hpy] at hy
      exact hy
    obtain ⟨a, b, hb, hab⟩ :=
      Ideal.mem_span_singleton_sup.mp (show p ∈ Ideal.span ({G} : Set _) ⊔ I by
        simpa only [J, sup_comm] using hpJ)
    let a₀ := homogeneousComponent n a
    let b₀ := homogeneousComponent (n + k) b
    have hb₀ : b₀ ∈ I := by
      have hh := hI (n + k) hb
      change (MvPolynomial.decomposition.decompose' b (n + k) : MvPolynomial σ K) ∈ I at hh
      simpa only [MvPolynomial.decomposition.decompose'_apply] using hh
    have hcomponent : homogeneousComponent (n + k) (a * G) = a₀ * G := by
      have hh := DirectSum.coe_decompose_mul_add_of_right_mem
        (MvPolynomial.homogeneousSubmodule σ K) (a := a) (i := n) hG
      change (MvPolynomial.decomposition.decompose' (a * G) (n + k) : MvPolynomial σ K) =
        (MvPolynomial.decomposition.decompose' a n : MvPolynomial σ K) * G at hh
      simpa only [MvPolynomial.decomposition.decompose'_apply] using hh
    have heq : a₀ * G + b₀ = p := by
      have hh := congrArg (homogeneousComponent (n + k)) hab
      simpa only [map_add, hcomponent, homogeneousComponent_of_mem hp, if_true] using hh
    let x : HC n := ⟨Ideal.Quotient.mk C a₀,
      Submodule.mem_map.mpr ⟨a₀, homogeneousComponent_isHomogeneous n a, rfl⟩⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change Ideal.Quotient.mk I (a₀ * G) = y.1.1
    rw [← hpy, ← heq]
    change Ideal.Quotient.mk I (a₀ * G) = Ideal.Quotient.mk I (a₀ * G + b₀)
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hb₀, add_zero]
  have hkerDim : Module.finrank K (HC n) = Module.finrank K (LinearMap.ker f) :=
    (LinearEquiv.ofBijective gKer ⟨hgKerInj, hgKerSurj⟩).finrank_eq
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.mpr hfSurj, finrank_top, ← hkerDim] at hrank
  exact hrank

end
end TranslatedDepthSeven
