import TranslatedDepthSeven.ProjectiveCurveSeparatorBridgeInternal
import TranslatedDepthSeven.FiniteComponentFrontier

/-!
# A Hilbert-function injection separating finitely many prime components

Linear sections of homogeneous quotient pieces, not quotient-algebra maps,
are multiplied by separating forms.  Reduction modulo each prime detects
one summand.  Thus the original ideal need not be radical.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 300000

universe u v w

/-- A homogeneous quotient piece admits a linear section consisting of
literal homogeneous polynomial representatives. -/
theorem exists_linear_section_quotientHomogeneousComponent
    {K : Type u} [Field K] {σ : Type v}
    (I : Ideal (MvPolynomial σ K)) (k : ℕ) :
    ∃ lift : quotientHomogeneousComponent K σ I k →ₗ[K]
      homogeneousSubmodule σ K k,
      ∀ x, Ideal.Quotient.mk I (lift x : MvPolynomial σ K) = x.1 := by
  let q := quotientHomogeneousComponentMap K σ I k
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.mp x.2
    exact ⟨⟨f, hf⟩, Subtype.ext hfx⟩
  obtain ⟨lift, hlift⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  refine ⟨lift, ?_⟩
  intro x
  exact congrArg Subtype.val (LinearMap.congr_fun hlift x)

/-- Equal-degree separating forms inject the direct sum of the homogeneous
pieces of the prime components into one shifted piece of the original
quotient. No reducedness or primality of the original ideal is used. -/
theorem sum_finrank_homogeneousComponents_le_of_separating_forms
    {K : Type u} [Field K] {σ : Type v} [Finite σ]
    {ι : Type w} [Fintype ι]
    (I : Ideal (MvPolynomial σ K))
    (P : ι → Ideal (MvPolynomial σ K))
    (hprime : ∀ i, (P i).IsPrime) (hcontain : ∀ i, I ≤ P i)
    (E : ℕ) (g : ι → MvPolynomial σ K)
    (hhom : ∀ i, (g i).IsHomogeneous E)
    (hown : ∀ i, g i ∉ P i)
    (hother : ∀ i j, i ≠ j → g i ∈ P j)
    (k : ℕ) :
    (∑ i, Module.finrank K (quotientHomogeneousComponent K σ (P i) k)) ≤
      Module.finrank K (quotientHomogeneousComponent K σ I (k + E)) := by
  classical
  choose lift hlift using fun i ↦ exists_linear_section_quotientHomogeneousComponent (P i) k
  let V := fun i ↦ quotientHomogeneousComponent K σ (P i) k
  let W := quotientHomogeneousComponent K σ I (k + E)
  let L : ((i : ι) → V i) →ₗ[K] W :=
    { toFun x := ⟨Ideal.Quotient.mk I
        (∑ i, g i * (lift i (x i) : MvPolynomial σ K)), by
        apply Submodule.mem_map.mpr
        refine ⟨∑ i, g i * (lift i (x i) : MvPolynomial σ K), ?_, rfl⟩
        apply IsHomogeneous.sum Finset.univ _ _
        intro i _
        simpa only [Nat.add_comm] using (hhom i).mul (lift i (x i)).2⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        change Ideal.Quotient.mk I
            (∑ i, g i * (lift i (x i + y i) : MvPolynomial σ K)) =
          Ideal.Quotient.mk I (∑ i, g i * (lift i (x i) : MvPolynomial σ K)) +
            Ideal.Quotient.mk I (∑ i, g i * (lift i (y i) : MvPolynomial σ K))
        simp only [map_add, Submodule.coe_add, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        apply Subtype.ext
        change Ideal.Quotient.mk I
            (∑ i, g i * (lift i (c • x i) : MvPolynomial σ K)) =
          c • Ideal.Quotient.mk I (∑ i, g i * (lift i (x i) : MvPolynomial σ K))
        simp only [map_smul, Submodule.coe_smul, mul_smul_comm, ← Finset.smul_sum]
        exact (Ideal.Quotient.mkₐ K I).toLinearMap.map_smul c _ }
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hmem : (∑ i, g i * (lift i (x i) : MvPolynomial σ K)) ∈ I :=
      Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val hx)
    funext i
    letI : (P i).IsPrime := hprime i
    have hzero : Ideal.Quotient.mk (P i)
        (∑ j, g j * (lift j (x j) : MvPolynomial σ K)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (hcontain i hmem)
    rw [map_sum, Finset.sum_eq_single i] at hzero
    · rw [map_mul, hlift i] at hzero
      apply Subtype.ext
      exact (mul_eq_zero.mp hzero).resolve_left
        (fun h ↦ hown i (Ideal.Quotient.eq_zero_iff_mem.mp h))
    · intro j _ hji
      rw [map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (hother j i hji), zero_mul]
    · exact fun hi ↦ (hi (Finset.mem_univ i)).elim
  have hfin := L.finrank_le_finrank_of_injective hinj
  simpa only [Module.finrank_pi_fintype, V, W] using hfin

end

end TranslatedDepthSeven
