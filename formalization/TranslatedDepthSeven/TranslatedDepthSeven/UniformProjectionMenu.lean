import TranslatedDepthSeven.IntegerGridAvoidance

/-!
# A uniform finite menu for polynomially detected projections

Suppose goodness of a linear projection is detected, for each member of a
family, by a nonzero integral polynomial in finitely many projection
coefficients.  A uniform degree bound gives one fixed finite integer grid of
candidate projections which contains a good candidate for every family
member.  This is the constructive finite-cover step used in the proposed
relative Noether-normalization argument.

The file does not construct the detecting polynomial.  In the application it
must be a literal resultant, discriminant, minor, or norm whose degree and
coefficient height are proved separately.
-/

namespace TranslatedDepthSeven

noncomputable section

open Finset Fintype MvPolynomial

/-- The fixed finite menu of integral coefficient vectors in the box
`{0, ..., D}^N`. -/
def boundedIntegerProjectionMenu (N D : ℕ) : Finset (Fin N → ℤ) :=
  Fintype.piFinset fun _ : Fin N ↦ nonnegativeIntegerGrid D

@[simp]
theorem card_boundedIntegerProjectionMenu (N D : ℕ) :
    (boundedIntegerProjectionMenu N D).card = (D + 1) ^ N := by
  simp [boundedIntegerProjectionMenu]

@[simp]
theorem mem_boundedIntegerProjectionMenu_iff
    {N D : ℕ} {x : Fin N → ℤ} :
    x ∈ boundedIntegerProjectionMenu N D ↔
      ∀ i, 0 ≤ x i ∧ x i ≤ D := by
  simp [boundedIntegerProjectionMenu, mem_nonnegativeIntegerGrid_iff]

/-- Every nonzero integral polynomial of degree at most `D` is nonzero at one
member of the fixed menu. -/
theorem exists_mem_boundedIntegerProjectionMenu_eval_ne_zero
    {N D : ℕ} (f : MvPolynomial (Fin N) ℤ)
    (hf : f ≠ 0) (hdegree : f.totalDegree ≤ D) :
    ∃ x ∈ boundedIntegerProjectionMenu N D,
      MvPolynomial.eval x f ≠ 0 := by
  obtain ⟨x, hx, hfx⟩ :=
    exists_nonzero_eval_on_nonnegativeIntegerGrid f hf hdegree
  exact ⟨x, mem_boundedIntegerProjectionMenu_iff.mpr hx, hfx⟩

/-- Uniform family form: the menu depends only on the number of projection
coefficients and the common degree bound, not on the family member. -/
theorem exists_projection_from_uniform_polynomial_menu
    {Θ : Type*} {N D : ℕ} (detector : Θ → MvPolynomial (Fin N) ℤ)
    (hne : ∀ θ, detector θ ≠ 0)
    (hdegree : ∀ θ, (detector θ).totalDegree ≤ D) :
    ∀ θ, ∃ x ∈ boundedIntegerProjectionMenu N D,
      MvPolynomial.eval x (detector θ) ≠ 0 := by
  intro θ
  exact exists_mem_boundedIntegerProjectionMenu_eval_ne_zero
    (detector θ) (hne θ) (hdegree θ)

/-- The same finite-menu choice with an explicit bound for the resulting
nonzero chart integer. -/
theorem exists_mem_boundedIntegerProjectionMenu_bounded_eval
    {N D S C : ℕ} (f : MvPolynomial (Fin N) ℤ)
    (hf : f ≠ 0)
    (hdegree : f.totalDegree ≤ D)
    (hsupport : f.support.card ≤ S)
    (hcoeff : ∀ m ∈ f.support, (f.coeff m).natAbs ≤ C) :
    ∃ x ∈ boundedIntegerProjectionMenu N D,
      MvPolynomial.eval x f ≠ 0 ∧
      (MvPolynomial.eval x f).natAbs ≤
        S * C * max 1 D ^ D := by
  obtain ⟨x, hx, hne, hbound⟩ :=
    exists_bounded_nonzero_eval_on_nonnegativeIntegerGrid
      f hf hdegree hsupport hcoeff
  exact ⟨x, mem_boundedIntegerProjectionMenu_iff.mpr hx, hne, hbound⟩

/-- Uniform bounded family form.  Once the detector coefficients are bounded
after substituting parameters of height `H`, the selected chart denominator
is bounded by the displayed polynomial expression. -/
theorem exists_projection_from_uniform_bounded_polynomial_menu
    {Θ : Type*} {N D S C : ℕ}
    (detector : Θ → MvPolynomial (Fin N) ℤ)
    (hne : ∀ θ, detector θ ≠ 0)
    (hdegree : ∀ θ, (detector θ).totalDegree ≤ D)
    (hsupport : ∀ θ, (detector θ).support.card ≤ S)
    (hcoeff : ∀ θ m, m ∈ (detector θ).support →
      ((detector θ).coeff m).natAbs ≤ C) :
    ∀ θ, ∃ x ∈ boundedIntegerProjectionMenu N D,
      MvPolynomial.eval x (detector θ) ≠ 0 ∧
      (MvPolynomial.eval x (detector θ)).natAbs ≤
        S * C * max 1 D ^ D := by
  intro θ
  exact exists_mem_boundedIntegerProjectionMenu_bounded_eval
    (detector θ) (hne θ) (hdegree θ) (hsupport θ) (hcoeff θ)

end

end TranslatedDepthSeven
