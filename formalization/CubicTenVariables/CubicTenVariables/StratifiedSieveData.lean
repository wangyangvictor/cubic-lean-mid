import CubicTenVariables.SimultaneousResidueCount
import CubicTenVariables.DyadicPowerSum
import CubicTenVariables.TranslatedIntegerBoxes

/-! Literal finite data and the explicitly stated progression hypothesis
for the manuscript's stratified composite sieve. -/
noncomputable section
namespace CubicTenVariables.StratifiedSieveData
open MvPolynomial SimultaneousResidueCount
open scoped BigOperators
variable {n s : ℕ}

/-- The hypothesis of the stratified sieve, uniform in all progression data. -/
def ProgressionHypothesis (U : Set (Fin n → ℤ)) (α : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 1 ≤ A ∧ ProgressionBound U α ε A

def ideal (t : Fin s → ℕ) (G : ∀ i, Fin (t i) → MvPolynomial (Fin n) ℤ)
    (i : Fin s) : Ideal (MvPolynomial (Fin n) ℤ) := Ideal.span (Set.range (G i))

/-- Every condition in the counted tuple--point set uses original integral
models, including the outside condition and composite modular equations. -/
structure ValidTuple (t : Fin s → ℕ) (G : ∀ i, Fin (t i) → MvPolynomial (Fin n) ℤ)
    (U : Set (Fin n → ℤ)) (u : Fin n → ℝ) (L : ℝ) (m : ℕ)
    (b : Fin n → ℤ) (R : Fin s → ℝ) (p : (Fin s → ℕ) × (Fin n → ℤ)) : Prop where
  squarefree : ∀ i, Squarefree (p.1 i)
  coprime : Pairwise (fun i j => (p.1 i).Coprime (p.1 j))
  base_coprime : ∀ i, m.Coprime (p.1 i)
  mem : p.2 ∈ U
  box : ∀ i, |(p.2 i : ℝ)-u i| ≤ L
  progression : ∀ i, (m : ℤ) ∣ p.2 i-b i
  outside : ∀ i, ∃ f ∈ ideal t G i, eval p.2 f ≠ 0
  equations : ∀ i, ∀ f ∈ ideal t G i, (p.1 i : ℤ) ∣ eval p.2 f
  dyadic : ∀ i, R i ≤ (p.1 i : ℝ) ∧ (p.1 i : ℝ) ≤ 2*R i

theorem ValidTuple.generator_equations {t : Fin s → ℕ}
    {G : ∀ i, Fin (t i) → MvPolynomial (Fin n) ℤ}
    {U : Set (Fin n → ℤ)} {u : Fin n → ℝ} {L : ℝ} {m : ℕ}
    {b : Fin n → ℤ} {R : Fin s → ℝ} {p : (Fin s → ℕ) × (Fin n → ℤ)}
    (hp : ValidTuple t G U u L m b R p) (i : Fin s) (j : Fin (t i)) :
    (p.1 i : ℤ) ∣ eval p.2 (G i j) :=
  hp.equations i _ (Ideal.subset_span (Set.mem_range_self j))

/-- The exact finite enumeration, with closed dyadic and spatial boundaries. -/
def pairs (t : Fin s → ℕ) (G : ∀ i, Fin (t i) → MvPolynomial (Fin n) ℤ)
    (U : Set (Fin n → ℤ)) (u : Fin n → ℝ) (L : ℝ) (m : ℕ)
    (b : Fin n → ℤ) (R : Fin s → ℝ) : Finset ((Fin s → ℕ) × (Fin n → ℤ)) := by
  classical
  exact ((Fintype.piFinset fun i => DyadicPowerSum.interval (R i)).product
    (TranslatedIntegerBoxes.box u L)).filter (ValidTuple t G U u L m b R)

/-- The dimension/profile expression on the right of the source bound. -/
def profile (d : Fin s → ℕ) (R : Fin s → ℝ) (T α : ℝ) : ℝ :=
  1 + T^α/(∏ i, (R i)^(α-(d i : ℝ)-1)) +
    ∑ j, T^((d j : ℝ)+1)/(∏ i, if j < i then (R i)^((d j : ℝ)-(d i : ℝ)) else 1)

end CubicTenVariables.StratifiedSieveData
