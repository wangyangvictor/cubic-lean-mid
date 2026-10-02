import TranslatedDepthSeven.ProjectiveSmallDegreeSpanInternal

/-!
# Scalar extension in the degree--span inequality

The dimension of the space of linear equations is unchanged by extension
of coefficient fields.  This proves the descent needed to apply the usual
algebraically closed-field degree--span theorem to a rational ideal.  No
Galois action, rational-point existence, or extra geometric input is used.
The degree--span inequality over the algebraically closed field itself is
not asserted here.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 2400000

/-- Rank-nullity for the literal degree-one subspace of an arbitrary ideal.
No homogeneity or primality condition is necessary. -/
theorem finrank_degreeOnePart_add_quotientHomogeneousComponent_eq
    {K : Type*} [Field K] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin N) K)) :
    Module.finrank K (StandardAG.degreeOnePartInIdeal I) +
      Module.finrank K (quotientHomogeneousComponent K (Fin N) I 1) = N := by
  let H := MvPolynomial.homogeneousSubmodule (Fin N) K 1
  let q := quotientHomogeneousComponentMap K (Fin N) I 1
  have hsurjective : Function.Surjective q := by
    intro x
    obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.mp x.property
    refine ⟨⟨f, hf⟩, ?_⟩
    apply Subtype.ext
    exact hfx
  let f : LinearMap.ker q →ₗ[K] StandardAG.degreeOnePartInIdeal I :=
    { toFun := fun p ↦ ⟨p.1.1, by
        have hp := congrArg Subtype.val p.property
        change Ideal.Quotient.mk I p.1.1 = 0 at hp
        exact ⟨Ideal.Quotient.eq_zero_iff_mem.mp hp, p.1.property⟩⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : StandardAG.degreeOnePartInIdeal I ↦ z.1) hxy
    · intro y
      refine ⟨⟨⟨y.1, y.property.2⟩, ?_⟩, ?_⟩
      · apply Subtype.ext
        exact Ideal.Quotient.eq_zero_iff_mem.mpr y.property.1
      · rfl
  have hker := (LinearEquiv.ofBijective f hf).finrank_eq
  have hsum := q.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurjective, finrank_top, hker] at hsum
  have hH : Module.finrank K H = N := by
    simpa only [Nat.add_sub_cancel, Nat.choose_one_right] using
      finrank_mvPolynomial_homogeneousSubmodule_fin K N 1
  change _ + _ = Module.finrank K H at hsum
  rw [hH] at hsum
  omega

/-- Coefficient extension preserves the exact number of independent linear
equations, even for nonhomogeneous or nonprime ideals. -/
theorem finrank_degreeOnePart_coefficientExtension_eq
    {K L : Type*} [Field K] [Field L] [Algebra K L] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) :
    Module.finrank L (StandardAG.degreeOnePartInIdeal
      (I.map (MvPolynomial.map (algebraMap K L)))) =
        Module.finrank K (StandardAG.degreeOnePartInIdeal I) := by
  have hK := finrank_degreeOnePart_add_quotientHomogeneousComponent_eq I
  have hL := finrank_degreeOnePart_add_quotientHomogeneousComponent_eq
    (I.map (MvPolynomial.map (algebraMap K L)))
  have hpiece := projectiveHilbertPiece_finrank_map_eq (K := K) (L := L) N 1 I
  change Module.finrank L (quotientHomogeneousComponent L (Fin (N + 1))
      (I.map (MvPolynomial.map (algebraMap K L))) 1) =
    Module.finrank K (quotientHomogeneousComponent K (Fin (N + 1)) I 1) at hpiece
  omega

/-- The numerical degree--span assertion descends from any field extension.
This is a pointwise implication, not an additional assumed theorem. -/
theorem projectiveDegreeSpan_descends_coefficientExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L] {N r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hspan : N + 1 ≤ Module.finrank L (StandardAG.degreeOnePartInIdeal
      (I.map (MvPolynomial.map (algebraMap K L)))) + r + d) :
    N + 1 ≤ Module.finrank K (StandardAG.degreeOnePartInIdeal I) + r + d := by
  simpa only [finrank_degreeOnePart_coefficientExtension_eq I] using hspan

end

end TranslatedDepthSeven
