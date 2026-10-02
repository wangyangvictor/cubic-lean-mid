import TranslatedDepthSeven.UniformProjectionMenu
import TranslatedDepthSeven.CharacteristicPolynomialHeight

/-!
# Relative detector polynomials and explicit projection charts

Let `Delta(t,L)` be one polynomial in family parameters `t` and projection
coefficients `L`.  Specializing either group of variables first gives the
same value.  If `Delta(t,-)` is nonzero of uniformly bounded degree for every
integral parameter value, the fixed bounded projection menu produces a
finite family of literal chart polynomials `Delta(-,L_i)`, one of which is
nonzero at every such parameter value.

This is the static algebraic form of a relative projection cover.  The
application still has to construct `Delta` and prove that its nonvanishing
implies the required finite, birational, or etale projection property.
-/

namespace TranslatedDepthSeven

noncomputable section

open Finset MvPolynomial

universe u

variable {R : Type u} [CommSemiring R]

/-- Substitute projection coefficients and retain the family parameters as
polynomial variables. -/
def specializeProjectionVariables {τ ν : Type*} (x : ν → R) :
    MvPolynomial (Sum τ ν) R →+* MvPolynomial τ R :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (Sum.elim MvPolynomial.X (fun j ↦ MvPolynomial.C (x j)))

/-- Substitute family parameters and retain the projection coefficients as
polynomial variables. -/
def specializeParameterVariables {τ ν : Type*} (t : τ → R) :
    MvPolynomial (Sum τ ν) R →+* MvPolynomial ν R :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (Sum.elim (fun i ↦ MvPolynomial.C (t i)) MvPolynomial.X)

/-- Evaluation after substituting the projection variables is simultaneous
evaluation of all variables. -/
theorem eval_specializeProjectionVariables {τ ν : Type*}
    (t : τ → R) (x : ν → R) (f : MvPolynomial (Sum τ ν) R) :
    MvPolynomial.eval t (specializeProjectionVariables x f) =
      MvPolynomial.eval (Sum.elim t x) f := by
  change (MvPolynomial.eval t)
      (MvPolynomial.eval₂Hom MvPolynomial.C
        (Sum.elim MvPolynomial.X (fun j ↦ MvPolynomial.C (x j))) f) = _
  rw [MvPolynomial.map_eval₂Hom]
  unfold MvPolynomial.eval
  apply MvPolynomial.eval₂Hom_congr
  · ext r
    simp
  · funext i
    cases i <;> simp
  · rfl

/-- Evaluation after substituting the parameter variables is the same
simultaneous evaluation. -/
theorem eval_specializeParameterVariables {τ ν : Type*}
    (t : τ → R) (x : ν → R) (f : MvPolynomial (Sum τ ν) R) :
    MvPolynomial.eval x (specializeParameterVariables t f) =
      MvPolynomial.eval (Sum.elim t x) f := by
  change (MvPolynomial.eval x)
      (MvPolynomial.eval₂Hom MvPolynomial.C
        (Sum.elim (fun i ↦ MvPolynomial.C (t i)) MvPolynomial.X) f) = _
  rw [MvPolynomial.map_eval₂Hom]
  unfold MvPolynomial.eval
  apply MvPolynomial.eval₂Hom_congr
  · ext r
    simp
  · funext i
    cases i <;> simp
  · rfl

/-- The two orders of partial specialization give exactly the same scalar. -/
theorem eval_specializeProjectionVariables_eq_eval_specializeParameterVariables
    {τ ν : Type*} (t : τ → R) (x : ν → R)
    (f : MvPolynomial (Sum τ ν) R) :
    MvPolynomial.eval t (specializeProjectionVariables x f) =
      MvPolynomial.eval x (specializeParameterVariables t f) := by
  rw [eval_specializeProjectionVariables, eval_specializeParameterVariables]

/-- The finite family of parameter-space chart polynomials obtained by
substituting every member of the bounded projection menu. -/
def relativeProjectionChartFamily {τ : Type*} (N D : ℕ)
    (detector : MvPolynomial (Sum τ (Fin N)) ℤ) :
    Finset (MvPolynomial τ ℤ) := by
  classical
  exact (boundedIntegerProjectionMenu N D).image fun x ↦
    specializeProjectionVariables x detector

/-- If every integral parameter specialization leaves a nonzero detector of
degree at most `D` in the projection variables, the displayed finite chart
family contains a polynomial nonvanishing at every integral parameter. -/
theorem exists_relativeProjectionChart_nonzero
    {τ : Type*} {N D : ℕ}
    (detector : MvPolynomial (Sum τ (Fin N)) ℤ)
    (hne : ∀ t : τ → ℤ,
      specializeParameterVariables t detector ≠ 0)
    (hdegree : ∀ t : τ → ℤ,
      (specializeParameterVariables t detector).totalDegree ≤ D)
    (t : τ → ℤ) :
    ∃ δ ∈ relativeProjectionChartFamily N D detector,
      MvPolynomial.eval t δ ≠ 0 := by
  classical
  obtain ⟨x, hx, hnonzero⟩ :=
    exists_mem_boundedIntegerProjectionMenu_eval_ne_zero
      (specializeParameterVariables t detector) (hne t) (hdegree t)
  refine ⟨specializeProjectionVariables x detector, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  · rwa [eval_specializeProjectionVariables_eq_eval_specializeParameterVariables]

/-- A fixed relative detector makes the height dependence automatic.  If the
family parameters have height at most `H`, then one member of the same finite
projection menu gives a nonzero chart integer whose size is bounded by direct
evaluation of the single polynomial `detector`. -/
theorem exists_relativeProjectionChart_nonzero_bounded
    {τ : Type*} {N D S C E H : ℕ}
    (detector : MvPolynomial (Sum τ (Fin N)) ℤ)
    (hne : ∀ t : τ → ℤ,
      specializeParameterVariables t detector ≠ 0)
    (hprojectionDegree : ∀ t : τ → ℤ,
      (specializeParameterVariables t detector).totalDegree ≤ D)
    (hsupport : detector.support.card ≤ S)
    (hcoeff : ∀ m ∈ detector.support,
      (detector.coeff m).natAbs ≤ C)
    (htotalDegree : detector.totalDegree ≤ E)
    (t : τ → ℤ)
    (ht : ∀ i, (t i).natAbs ≤ H) :
    ∃ δ ∈ relativeProjectionChartFamily N D detector,
      MvPolynomial.eval t δ ≠ 0 ∧
      (MvPolynomial.eval t δ).natAbs ≤
        S * C * max 1 (max H D) ^ E := by
  classical
  obtain ⟨x, hx, hnonzero⟩ :=
    exists_mem_boundedIntegerProjectionMenu_eval_ne_zero
      (specializeParameterVariables t detector) (hne t)
      (hprojectionDegree t)
  have hxcoord : ∀ j, (x j).natAbs ≤ D := by
    intro j
    have hxj := mem_boundedIntegerProjectionMenu_iff.mp hx j
    have hcoerced : ((x j).natAbs : ℤ) ≤ (D : ℤ) := by
      rw [Int.natAbs_of_nonneg hxj.1]
      exact hxj.2
    exact_mod_cast hcoerced
  have hall : ∀ i : Sum τ (Fin N),
      ((Sum.elim t x) i).natAbs ≤ max H D := by
    intro i
    cases i with
    | inl i => exact (ht i).trans (Nat.le_max_left _ _)
    | inr j => exact (hxcoord j).trans (Nat.le_max_right _ _)
  have hbound :
      (MvPolynomial.eval (Sum.elim t x) detector).natAbs ≤
        S * C * max 1 (max H D) ^ E := by
    refine (eval_natAbs_le_support_mul_coeff_mul_pow_generic
      detector (Sum.elim t x) hcoeff htotalDegree hall).trans ?_
    simpa [Nat.mul_assoc] using
      Nat.mul_le_mul_right (C * max 1 (max H D) ^ E) hsupport
  refine ⟨specializeProjectionVariables x detector, ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  · rwa [eval_specializeProjectionVariables_eq_eval_specializeParameterVariables]
  · rwa [eval_specializeProjectionVariables]

end

end TranslatedDepthSeven
