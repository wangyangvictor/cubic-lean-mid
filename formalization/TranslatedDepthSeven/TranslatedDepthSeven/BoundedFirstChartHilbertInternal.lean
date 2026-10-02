import TranslatedDepthSeven.ProjectiveZerofoldFirstChartInternal

/-!
# Bounded Hilbert functions on arbitrary standard affine charts

Dehomogenization gives a surjection from a homogeneous quotient piece onto
the corresponding affine filtration piece.  The homogeneous ideal need
not be prime or reduced.  A uniform bound for the latter filtration gives
a finite spanning family for the entire coordinate algebra.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

universe u

variable {K : Type u} [Field K]

/-- Dehomogenizing can decrease, but cannot increase, the dimension of a
homogeneous quotient piece.  No primality assumption is used. -/
theorem finrank_affine_dehomogenization_le_projective
    {n k : ℕ} (I : Ideal (MvPolynomial (Option (Fin n)) K)) :
    Module.finrank K
        (affineHilbertFiltration K n
          (I.map multivariateDehomogenization.toRingHom) k) ≤
      Module.finrank K (quotientHomogeneousComponent K (Option (Fin n)) I k) := by
  let J := I.map multivariateDehomogenization.toRingHom
  let phi : MvPolynomial (Option (Fin n)) K →ₐ[K]
      (MvPolynomial (Fin n) K ⧸ J) :=
    (Ideal.Quotient.mkₐ K J).comp multivariateDehomogenization
  let q : (MvPolynomial (Option (Fin n)) K ⧸ I) →ₐ[K]
      (MvPolynomial (Fin n) K ⧸ J) :=
    Ideal.Quotient.liftₐ I phi (by
      intro f hf
      exact (Ideal.Quotient.eq_zero_iff_mem).2
        (Ideal.mem_map_of_mem multivariateDehomogenization.toRingHom hf))
  let H := quotientHomogeneousComponent K (Option (Fin n)) I k
  let F := affineHilbertFiltration K n J k
  let f : H →ₗ[K] F :=
    (q.toLinearMap.comp H.subtype).codRestrict _ (by
      intro x
      obtain ⟨a, ha, hax⟩ := Submodule.mem_map.1 x.2
      refine Submodule.mem_map.2 ⟨multivariateDehomogenization a, ?_, ?_⟩
      · exact (MvPolynomial.mem_restrictTotalDegree _ _ _).2
          (multivariateHomogenization_dehomogenization_of_isHomogeneous a ha).1
      · change Ideal.Quotient.mk J (multivariateDehomogenization a) = q x.1
        rw [← hax]
        rfl)
  have hfSurj : Function.Surjective f := by
    intro y
    obtain ⟨a, ha, hay⟩ := Submodule.mem_map.1 y.2
    let ah := multivariateHomogenization a k
    have hah : ah.IsHomogeneous k := multivariateHomogenization_isHomogeneous a k
    refine ⟨⟨Ideal.Quotient.mk I ah, Submodule.mem_map.2 ⟨ah, hah, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change Ideal.Quotient.mk J (multivariateDehomogenization ah) = y.1
    rw [multivariateDehomogenization_homogenization a k
      ((MvPolynomial.mem_restrictTotalDegree _ _ _).1 ha)]
    exact hay
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.2 hfSurj] at hrank
  simp only [finrank_top] at hrank
  change Module.finrank K F ≤ Module.finrank K H
  omega

/-- Padding by zero turns a spanning family of size `e` into one of any
specified larger size.  This includes `e = 0`. -/
theorem exists_spanningFamily_of_spanningFamily_le
    {V : Type*} [AddCommGroup V] [Module K V] {e d : ℕ}
    (hed : e ≤ d) (v : Fin e → V)
    (hv : Submodule.span K (Set.range v) = ⊤) :
    ∃ w : Fin d → V, Submodule.span K (Set.range w) = ⊤ := by
  classical
  let w : Fin d → V := fun i ↦ if h : i.1 < e then v ⟨i.1, h⟩ else 0
  refine ⟨w, top_unique ?_⟩
  rw [← hv]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  refine ⟨i.castLE hed, ?_⟩
  simp [w, i.2]

/-- An eventual upper bound for a cumulative affine Hilbert function
gives a spanning family of that size, without assuming a Hilbert
polynomial or reducedness. -/
theorem exists_affineQuotient_spanningFamily_of_eventual_bounded_hilbert
    {N d : ℕ} (I : Ideal (MvPolynomial (Fin N) K))
    (k₀ : ℕ)
    (hbounded : ∀ k ≥ k₀,
      Module.finrank K (affineHilbertFiltration K N I k) ≤ d) :
    ∃ v : Fin d → (MvPolynomial (Fin N) K ⧸ I),
      Submodule.span K (Set.range v) = ⊤ := by
  classical
  let F := affineHilbertFiltration K N I
  let s := (Finset.range (d + 1)).filter
    fun e ↦ ∃ k, k₀ ≤ k ∧ Module.finrank K (F k) = e
  have hs : s.Nonempty := by
    refine ⟨Module.finrank K (F k₀), ?_⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2
      (Nat.lt_succ_of_le (hbounded k₀ le_rfl)), k₀, le_rfl, rfl⟩
  obtain ⟨k₁, hk₁, he₁⟩ := (Finset.mem_filter.1 (Finset.max'_mem s hs)).2
  have heBound : s.max' hs ≤ d := by
    exact Nat.le_of_lt_succ (Finset.mem_range.1
      (Finset.mem_filter.1 (Finset.max'_mem s hs)).1)
  have hmono : Monotone F := by
    intro a b hab
    apply Submodule.map_mono
    intro f hf
    exact (MvPolynomial.mem_restrictTotalDegree _ _ _).2
      (((MvPolynomial.mem_restrictTotalDegree _ _ _).1 hf).trans hab)
  have hconstant : ∀ k ≥ k₁, Module.finrank K (F k) = s.max' hs := by
    intro k hk
    apply le_antisymm
    · apply Finset.le_max'
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2
        (Nat.lt_succ_of_le (hbounded k (hk₁.trans hk))), k, hk₁.trans hk, rfl⟩
    · rw [← he₁]
      exact Submodule.finrank_mono (hmono hk)
  obtain ⟨v, hv⟩ :=
    exists_affineQuotient_spanningFamily_of_eventual_constant_hilbert I k₁ hconstant
  exact exists_spanningFamily_of_spanningFamily_le heBound v hv

end

end TranslatedDepthSeven
