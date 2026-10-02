import CubicTenVariables.ProjectiveLinearSectionVariance
import CubicTenVariables.ProjectiveFourierIdentity

/-! Literal polynomial-zero-set forms of the projective section variance.
All cardinalities refer to actual quotient projective points or actual
vectors satisfying the equations. Homogeneity supplies the representative
invariance and the affine-cone identity. No literature input is used. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace CubicTenVariables.ProjectivePolynomialSectionVariance
open MvPolynomial ProjectiveFourierIdentity ProjectiveLinearSectionVariance

variable {K : Type*} [Field K] [Fintype K] {n k d : ℕ}

local instance : Fintype (Projectivization K (Fin n → K)) := Fintype.ofFinite _

/-- The finite set underlying the existing literal projective hypersurface. -/
def polynomialPoints (F : MvPolynomial (Fin n) K) :
    Finset (Projectivization K (Fin n → K)) :=
  Finset.univ.filter (fun p => eval p.rep F = 0)

/-- Actual points cut out by the polynomial and every row of the equation tuple. -/
def linearSectionPoints (F : MvPolynomial (Fin n) K) (γ : Fin k → Fin n → K) :=
  {p : Projectivization K (Fin n → K) // eval p.rep F = 0 ∧ incident γ p}

theorem card_polynomialPoints (F : MvPolynomial (Fin n) K) :
    (polynomialPoints F).card = Nat.card (zeroPoints F) := by
  simp [polynomialPoints, zeroPoints, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem sectionCount_polynomialPoints (F : MvPolynomial (Fin n) K)
    (γ : Fin k → Fin n → K) :
    sectionCount (polynomialPoints F) γ = Nat.card (linearSectionPoints F γ) := by
  simp [sectionCount, polynomialPoints, linearSectionPoints,
    Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_filter]

omit [Fintype K] in
/-- The simultaneous linear equations are independent of the representative. -/
theorem incident_mk_iff (γ : Fin k → Fin n → K) (x : Fin n → K) (hx : x ≠ 0) :
    incident γ (Projectivization.mk K x hx) ↔ ∀ j, dotProduct (γ j) x = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K x hx
  simp only [incident, ← ha, Units.smul_def, dotProduct_smul,
    smul_eq_mul, mul_eq_zero, a.ne_zero, false_or]

/-- Exact cone/projective conversion for simultaneous homogeneous equations. -/
theorem affine_linearSection_card (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous d) (hd : 0 < d) (γ : Fin k → Fin n → K) :
    Nat.card {x : Fin n → K // eval x F = 0 ∧ ∀ j, dotProduct (γ j) x = 0} =
      Nat.card (linearSectionPoints F γ) * (Fintype.card K - 1) + 1 := by
  apply cone_card (fun x => eval x F = 0 ∧ ∀ j, dotProduct (γ j) x = 0)
  · exact ⟨eval_origin_zero F hF hd, by intro j; simp⟩
  · intro a ha x
    simp only [eval_smul_zero_iff F hF a ha, dotProduct_smul,
      smul_eq_mul, mul_eq_zero, ha, false_or]

/-- The variance identity on the literal hypersurface and its actual linear sections. -/
theorem variance (hn : 2 ≤ n) (F : MvPolynomial (Fin n) K) :
    (∑ γ : Fin k → Fin n → K,
      ((Nat.card (zeroPoints F) : ℝ) - (Nat.card K : ℝ) ^ k *
        (Nat.card (linearSectionPoints F γ) : ℝ)) ^ 2) =
      (Nat.card (zeroPoints F) : ℝ) * (Nat.card K : ℝ) ^ (n * k) *
        ((Nat.card K : ℝ) ^ k - 1) := by
  simpa only [card_polynomialPoints, sectionCount_polynomialPoints] using
    ProjectiveLinearSectionVariance.variance (k := k) hn (polynomialPoints F)

/-- Select a member of any majority of literal section tuples. -/
theorem exists_good_section_of_card (hn : 2 ≤ n) (F : MvPolynomial (Fin n) K)
    (G : Finset (Fin k → Fin n → K))
    (hG : Fintype.card (Fin k → Fin n → K) < 2 * G.card) :
    ∃ γ ∈ G, ((Nat.card (zeroPoints F) : ℝ) - (Nat.card K : ℝ) ^ k *
      (Nat.card (linearSectionPoints F γ) : ℝ)) ^ 2 ≤
      2 * (Nat.card (zeroPoints F) : ℝ) * ((Nat.card K : ℝ) ^ k - 1) := by
  simpa only [card_polynomialPoints, sectionCount_polynomialPoints] using
    ProjectiveLinearSectionVariance.exists_good_section_of_card hn (polynomialPoints F) G hG

end CubicTenVariables.ProjectivePolynomialSectionVariance
