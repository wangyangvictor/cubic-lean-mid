import TranslatedDepthSeven.BoundedPointSpanEquations
import TranslatedDepthSeven.ProjectiveLinearSpanIsolation

/-!
# Bounded containing equations or a proper hyperplane section

Let `Q` contain two independent linear forms and let `Z` be a finite set of
bounded integral zeros of `Q`. Cramer's rule gives two bounded independent
equations vanishing on `Z`. If both belong to `Q`, they give a bounded
codimension-two linear space containing the component. Otherwise one is a
linear form outside `Q` vanishing on every point of `Z`.

There is no component-height theorem in this argument. Primality is not
needed until the second alternative is used for a dimension drop.
-/

namespace TranslatedDepthSeven

noncomputable section

open Matrix MvPolynomial

set_option maxHeartbeats 5000000

/-- Two equations of the ideal give the required point-span codimension. -/
theorem finrank_integralPointSpan_le_of_two_linearForms
    {N : ℕ} (Q : Ideal (MvPolynomial (Fin N) ℚ))
    (hlinear : 2 ≤ Module.finrank ℚ (rationalLinearFormsInIdeal Q))
    (Z : Finset (IntVector N))
    (hzero : ∀ z ∈ Z,
      (fun i ↦ (z i : ℚ)) ∈ affineIdealZeroLocus Q) :
    2 ≤ N ∧
      Module.finrank ℚ
        (Submodule.span ℚ (Set.range fun z : {z // z ∈ Z} ↦
          fun j ↦ (z.1 j : ℚ))) ≤ N - 2 := by
  obtain ⟨v, _hv, hrank, hrows⟩ :=
    exists_twoRow_rationalLinearFormMatrix_of_two_le_finrank Q hlinear
  let A := rationalLinearFormMatrix v
  have hsub : Submodule.span ℚ
      (Set.range fun z : {z // z ∈ Z} ↦ fun j ↦ (z.1 j : ℚ)) ≤
      LinearMap.ker A.mulVecLin := by
    apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    exact mulVec_rationalLinearFormMatrix_eq_zero_of_zeroLocus
      v Q hrows (hzero z.1 z.2)
  have hdimension := A.mulVecLin.finrank_range_add_finrank_ker
  have hrange : Module.finrank ℚ (LinearMap.range A.mulVecLin) = 2 := hrank
  have hdimension' : 2 + Module.finrank ℚ (LinearMap.ker A.mulVecLin) = N := by
    simpa only [hrange, Module.finrank_pi, Fintype.card_fin]
      using hdimension
  refine ⟨by omega, ?_⟩
  have hle := Submodule.finrank_mono hsub
  omega

/-- Explicit two-alternative statement suitable for a low-degree component.
The height depends only on the actual point box, never on chosen component
equations. -/
theorem bounded_containing_twoRowSection_or_proper_hyperplane
    {N M : ℕ} (Q : Ideal (MvPolynomial (Fin N) ℚ))
    (hlinear : 2 ≤ Module.finrank ℚ (rationalLinearFormsInIdeal Q))
    (Z : Finset (IntVector N))
    (hzero : ∀ z ∈ Z,
      (fun i ↦ (z i : ℚ)) ∈ affineIdealZeroLocus Q)
    (hcoord : ∀ z ∈ Z, ∀ i, (z i).natAbs ≤ M) :
    (∃ A : Matrix (Fin 2) (Fin N) ℚ,
      A.rank = 2 ∧
      finiteEquationIdeal (rationalMatrixRowLinearEquationFamily A) ≤ Q ∧
      rationalProjectiveLinearHeight A ≤
        Nat.factorial 2 * ((N - 2).factorial * (max 1 M) ^ (N - 2)) ^ 2) ∨
    (∃ f : MvPolynomial (Fin N) ℚ,
      f.IsHomogeneous 1 ∧ f ∉ Q ∧
        ∀ z ∈ Z, MvPolynomial.eval (fun i ↦ (z i : ℚ)) f = 0) := by
  classical
  obtain ⟨hN, hspan⟩ :=
    finrank_integralPointSpan_le_of_two_linearForms Q hlinear Z hzero
  obtain ⟨A, hArank, hAzero, _hAentries, hAheight⟩ :=
    exists_bounded_integral_equations_of_pointSpan_finrank_le hN Z hspan hcoord
  let AQ : Matrix (Fin 2) (Fin N) ℚ := A.map ((↑) : ℤ → ℚ)
  by_cases hrows : ∀ i, rationalMatrixRowLinearPolynomial AQ i ∈ Q
  · left
    refine ⟨AQ, hArank, ?_, hAheight⟩
    rw [finiteEquationIdeal]
    apply Ideal.span_le.mpr
    intro f hf
    rw [Finset.mem_coe, rationalMatrixRowLinearEquationFamily,
      Finset.mem_image] at hf
    obtain ⟨i, _hi, rfl⟩ := hf
    exact hrows i
  · right
    push_neg at hrows
    obtain ⟨i, hi⟩ := hrows
    refine ⟨rationalMatrixRowLinearPolynomial AQ i,
      rationalMatrixRowLinearPolynomial_isHomogeneous AQ i, hi, ?_⟩
    intro z hz
    rw [eval_rationalMatrixRowLinearPolynomial]
    have hmap := (Int.castRingHom ℚ).map_mulVec A z i
    have hzeroi := congrFun (hAzero z hz) i
    have hcast : ((Matrix.mulVec A z) i : ℚ) = 0 := by exact_mod_cast hzeroi
    exact hmap.symm.trans hcast

end

end TranslatedDepthSeven
