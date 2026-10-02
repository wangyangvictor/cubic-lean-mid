import TranslatedDepthSeven.ProjectiveBertiniSmoothGenericHyperplane

/-!
# A smooth marked chart on the generic hyperplane over a field

The parameter polynomial ring may inject into any field. In particular,
the argument survives extension from the generic coefficient field to its
algebraic closure. The affine ideal is the actual coefficient extension of
the original ideal plus the actual generic linear hyperplane equation.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000

/-- Injecting the coefficient polynomial ring into a field preserves the
generic marked-point minor. -/
theorem bertiniGenericMarkedHyperplane_field_selectedMinor_ne_zero
    {K L : Type*} [Field K] [Field L] {N c : ℕ}
    (φ : MvPolynomial (Fin N) K →+* L) (hφ : Function.Injective φ)
    (equations : Fin c → MvPolynomial (Fin N) K)
    (cols : Fin c → Fin N) (z : Fin N → K)
    (j : Fin N) (hj : j ∉ Set.range cols)
    (hminor : eval z (selectedJacobianDeterminant equations cols) ≠ 0) :
    eval (fun i : Fin N ↦ φ (C (z i)))
      (selectedJacobianDeterminant
        (fun i : Fin (c + 1) ↦ MvPolynomial.map φ
          (bertiniGenericMarkedEquations equations z i))
        (Fin.cons j cols)) ≠ 0 := by
  have hnon := bertiniGenericMarkedHyperplane_selectedMinor_ne_zero
    equations cols z j hj hminor
  intro hzero
  apply hnon
  apply hφ
  rw [map_zero, MvPolynomial.map_eval, map_selectedJacobianDeterminant]
  exact hzero

/-- The original denominator still clears the extended affine equations
after a coefficient map. -/
theorem bertini_map_local_equations
    {K L : Type*} [CommRing K] [CommRing L] {N c : ℕ}
    (ψ : K →+* L) (J : Ideal (MvPolynomial (Fin N) K))
    (equations : Fin c → MvPolynomial (Fin N) K) (u : MvPolynomial (Fin N) K)
    (hIJ : Ideal.span (Set.range equations) ≤ J)
    (hclear : ∀ f ∈ J, u * f ∈ Ideal.span (Set.range equations)) :
    let equationsL := fun i ↦ MvPolynomial.map ψ (equations i)
    Ideal.span (Set.range equationsL) ≤ J.map (MvPolynomial.map ψ) ∧
      ∀ f ∈ J.map (MvPolynomial.map ψ),
        MvPolynomial.map ψ u * f ∈ Ideal.span (Set.range equationsL) := by
  have hmap : (Ideal.span (Set.range equations)).map (MvPolynomial.map ψ) =
      Ideal.span (Set.range (fun i ↦ MvPolynomial.map ψ (equations i))) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have hmul : Ideal.span {u} * J ≤ Ideal.span (Set.range equations) := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := Ideal.mem_span_singleton_mul.mp hf
    exact hclear g hg
  have hmulL := Ideal.map_mono (f := MvPolynomial.map ψ) hmul
  rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton, hmap] at hmulL
  refine ⟨?_, ?_⟩
  · rw [← hmap]
    exact Ideal.map_mono hIJ
  · intro f hf
    exact hmulL (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hf)

/-- Appending an arbitrary equation preserves the local-equation
denominator. This is used for the generic linear equation. -/
theorem bertini_adjoin_equation_local_equations
    {K : Type*} [CommRing K] {N c : ℕ}
    (J : Ideal (MvPolynomial (Fin N) K))
    (equations : Fin c → MvPolynomial (Fin N) K) (u H : MvPolynomial (Fin N) K)
    (hIJ : Ideal.span (Set.range equations) ≤ J)
    (hclear : ∀ f ∈ J, u * f ∈ Ideal.span (Set.range equations)) :
    Ideal.span (Set.range (Fin.cons H equations)) ≤ J ⊔ Ideal.span {H} ∧
      ∀ f ∈ J ⊔ Ideal.span {H},
        u * f ∈ Ideal.span (Set.range (Fin.cons H equations)) := by
  have hspan : Ideal.span (Set.range (Fin.cons H equations)) =
      Ideal.span (Set.range equations) ⊔ Ideal.span {H} := by
    rw [Fin.range_cons, Ideal.span_insert, sup_comm]
  rw [hspan]
  refine ⟨sup_le_sup_right hIJ _, ?_⟩
  intro f hf
  obtain ⟨g, hg, h, hh, rfl⟩ := Submodule.mem_sup.mp hf
  rw [mul_add]
  exact Submodule.mem_sup.mpr ⟨u * g, hclear g hg, u * h,
    (Ideal.span {H}).mul_mem_left u hh, rfl⟩

/-- The actual generic hyperplane section has a standard-smooth
principal chart containing the marked point, even after an arbitrary
injective extension of its coefficient polynomial ring into a field. -/
theorem bertiniGenericMarkedHyperplane_field_standardSmooth_chart
    {K L : Type*} [Field K] [Field L] {N c : ℕ}
    (φ : MvPolynomial (Fin N) K →+* L) (hφ : Function.Injective φ)
    (J : Ideal (MvPolynomial (Fin N) K))
    (equations : Fin c → MvPolynomial (Fin N) K)
    (cols : Fin c → Fin N) (hcols : Function.Injective cols)
    (u : MvPolynomial (Fin N) K)
    (hIJ : Ideal.span (Set.range equations) ≤ J)
    (hclear : ∀ f ∈ J, u * f ∈ Ideal.span (Set.range equations))
    (z : Fin N → K) (hz : J ≤ RingHom.ker (aeval z).toRingHom)
    (hminor : aeval z (u * selectedJacobianDeterminant equations cols) ≠ 0)
    (j : Fin N) (hj : j ∉ Set.range cols) :
    let ψ := φ.comp (C : K →+* MvPolynomial (Fin N) K)
    let zL := fun i ↦ ψ (z i)
    let H := MvPolynomial.map φ (bertiniGenericMarkedHyperplane z)
    let J' := J.map (MvPolynomial.map ψ) ⊔ Ideal.span {H}
    ∃ G : MvPolynomial (Fin N) L,
      J' ≤ RingHom.ker (aeval zL).toRingHom ∧ aeval zL G ≠ 0 ∧
      Algebra.IsStandardSmoothOfRelativeDimension (N - (c + 1)) L
        (Localization.Away (Ideal.Quotient.mk J' G)) := by
  let ψ : K →+* L := φ.comp C
  let zL : Fin N → L := fun i ↦ ψ (z i)
  let H : MvPolynomial (Fin N) L := MvPolynomial.map φ (bertiniGenericMarkedHyperplane z)
  let JL := J.map (MvPolynomial.map ψ)
  let equationsL : Fin c → MvPolynomial (Fin N) L := fun i ↦ MvPolynomial.map ψ (equations i)
  let equations' : Fin (c + 1) → MvPolynomial (Fin N) L := Fin.cons H equationsL
  let cols' : Fin (c + 1) → Fin N := Fin.cons j cols
  have hvalues : eval z u ≠ 0 ∧ eval z (selectedJacobianDeterminant equations cols) ≠ 0 := by
    simpa only [map_mul, mul_ne_zero_iff] using hminor
  have hmapEquations : (fun i : Fin (c + 1) ↦ MvPolynomial.map φ
      (bertiniGenericMarkedEquations equations z i)) = equations' := by
    funext i
    refine Fin.cases rfl (fun i ↦ ?_) i
    simp only [bertiniGenericMarkedEquations, Fin.cons_succ, equations', equationsL,
      MvPolynomial.map_map]
    rfl
  have hminorL := bertiniGenericMarkedHyperplane_field_selectedMinor_ne_zero
    φ hφ equations cols z j hj hvalues.2
  rw [hmapEquations] at hminorL
  have huL : eval zL (MvPolynomial.map ψ u) ≠ 0 := by
    change eval (ψ ∘ z) (MvPolynomial.map ψ u) ≠ 0
    rw [← MvPolynomial.map_eval]
    exact fun h ↦ hvalues.1 ((RingHom.injective ψ) (h.trans (map_zero ψ).symm))
  have hzL : JL ≤ RingHom.ker (aeval zL).toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    change eval (ψ ∘ z) (MvPolynomial.map ψ f) = 0
    rw [← MvPolynomial.map_eval, show eval z f = 0 from hz hf, map_zero]
  have hH : aeval zL H = 0 := by
    change eval (φ ∘ fun i : Fin N ↦ C (z i))
      (MvPolynomial.map φ (bertiniGenericMarkedHyperplane z)) = 0
    rw [← MvPolynomial.map_eval]
    simp [bertiniGenericMarkedHyperplane]
  have hz' : JL ⊔ Ideal.span {H} ≤ RingHom.ker (aeval zL).toRingHom := by
    refine sup_le hzL (Ideal.span_le.mpr ?_)
    intro f hf
    obtain rfl := Set.mem_singleton_iff.mp hf
    exact hH
  obtain ⟨hIJL, hclearL⟩ := bertini_map_local_equations ψ J equations u hIJ hclear
  obtain ⟨hIJ', hclear'⟩ := bertini_adjoin_equation_local_equations
    JL equationsL (MvPolynomial.map ψ u) H hIJL hclearL
  refine ⟨MvPolynomial.map ψ u * selectedJacobianDeterminant equations' cols', hz', ?_, ?_⟩
  · change eval zL (MvPolynomial.map ψ u * selectedJacobianDeterminant equations' cols') ≠ 0
    rw [map_mul]
    exact mul_ne_zero huL hminorL
  · exact local_equations_selectedJacobian_standardSmooth_principalOpen
      (JL ⊔ Ideal.span {H}) equations' cols' (Fin.cons_injective_of_injective hj hcols)
      (MvPolynomial.map ψ u) hIJ' hclear'

end
end TranslatedDepthSeven
