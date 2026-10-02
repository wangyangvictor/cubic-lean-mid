import HessianTheorem11.UnconditionalOrbitCharacters

/-! Full special-linear characters have exactly equal diagonal factors
under determinant-one diagonal matrices. This controls cancellation inside
character components over valuation fields, not just their valuations. -/
noncomputable section
namespace HessianTheorem11.UnconditionalOrbitIdeal
open MvPolynomial UnconditionalOrbitWeights
variable {n d : ℕ}

theorem equationExponent_difference_constant (hn : 0 < n)
    (e f : DegreeIndex n d →₀ ℕ) (he : equationCharacter e = equationCharacter f) :
    ∃ a : ℤ, ∀ i, equationExponent e i = equationExponent f i + a := by
  let i₀ : Fin n := ⟨0,hn⟩
  refine ⟨equationExponent e i₀ - equationExponent f i₀,?_⟩
  intro i
  have hi := congrFun he i
  have h0 := congrFun he i₀
  change (n : ℤ) * equationExponent e i - ∑ j, equationExponent e j =
    (n : ℤ) * equationExponent f i - ∑ j, equationExponent f j at hi
  change (n : ℤ) * equationExponent e i₀ - ∑ j, equationExponent e j =
    (n : ℤ) * equationExponent f i₀ - ∑ j, equationExponent f j at h0
  have hm : (n : ℤ) * (equationExponent e i - equationExponent f i) =
      (n : ℤ) * (equationExponent e i₀ - equationExponent f i₀) := by nlinarith
  have hh := mul_left_cancel₀ (by omega : (n : ℤ) ≠ 0) hm
  omega

/-- The exact diagonal eigenvalue, expressed in any commutative group. -/
def diagonalCharacterFactor {G : Type*} [CommGroup G]
    (δ : Fin n → G) (e : DegreeIndex n d →₀ ℕ) : G :=
  ∏ i, δ i ^ equationExponent e i

theorem diagonalCharacterFactor_eq {G : Type*} [CommGroup G] (hn : 0 < n)
    (δ : Fin n → G) (hδ : ∏ i, δ i = 1)
    (e f : DegreeIndex n d →₀ ℕ) (he : equationCharacter e = equationCharacter f) :
    diagonalCharacterFactor δ e = diagonalCharacterFactor δ f := by
  obtain ⟨a,ha⟩ := equationExponent_difference_constant hn e f he
  simp only [diagonalCharacterFactor,ha,zpow_add,Finset.prod_mul_distrib]
  rw [Finset.prod_zpow,hδ,one_zpow,mul_one]

theorem prod_zpow_eq_zpow_sum {G α : Type*} [CommGroup G]
    (s : Finset α) (f : α → ℤ) (g : G) : (∏ i ∈ s, g ^ f i) = g ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi,ih,zpow_add]

variable {K : Type*} [Field K]

def coefficientDiagonal (δ : Fin n → Kˣ) (m : DegreeIndex n d) : Kˣ :=
  ∏ i, δ i ^ m.val i

theorem coefficientDiagonal_monomial (δ : Fin n → Kˣ) (e : DegreeIndex n d →₀ ℕ) :
    (∏ m, coefficientDiagonal δ m ^ e m) = diagonalCharacterFactor δ e := by
  classical
  simp only [coefficientDiagonal,← Finset.prod_pow,← pow_mul]
  rw [Finset.prod_comm]
  unfold diagonalCharacterFactor equationExponent
  apply Finset.prod_congr rfl
  intro i _
  rw [← prod_zpow_eq_zpow_sum]
  apply Finset.prod_congr rfl
  intro m _
  rw [mul_comm (e m : ℤ),← Int.natCast_mul,zpow_natCast]

end HessianTheorem11.UnconditionalOrbitIdeal
