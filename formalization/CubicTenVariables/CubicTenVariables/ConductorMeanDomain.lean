import CubicTenVariables.NumericalConductorRadical
import CubicTenVariables.ConductorFixedFrequency

/-! The finite summation domain for the positive conductor mean. Every
condition here is a restriction on an actual modulus/frequency pair;
none is an assumed counting estimate. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ConductorMeanDomain
open MvPolynomial NumericalPrimeDepth NumericalConductorRadical
open ConductorFixedFrequency

abbrev Sample := (ℕ × ℕ) × (Fin 10 → ℤ)

variable {F : MvPolynomial (Fin 10) ℤ} {C : ℝ}

def tag (h : CoarseBounds F C) (x : Sample) : ℕ × ℕ :=
  (primeHigh h x.1.1 x.2,squareHigh h x.1.2 x.2)

/-- A stronger tail domain than the source's dyadic bands: the upper
conductor cutoff and lower modulus cutoff are unnecessary here. -/
structure InWindow {t : ℕ} (h : CoarseBounds F C)
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10)
    (tables : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1))
    (D K0 : ℝ) (m : ℕ) (u : Fin 10 → ℝ) (L : ℝ)
    (v₀ : Fin 10 → ℤ) (x : Sample) : Prop where
  positive_left : 1 ≤ x.1.1
  positive_right : 1 ≤ x.1.2
  squarefree_left : Squarefree x.1.1
  squarefree_right : Squarefree x.1.2
  coprime : x.1.1.Coprime x.1.2
  size : (x.1.1 : ℝ)*(x.1.2 : ℝ)^2 ≤ 2*D
  good : GoodFrequency F f tables x.2
  box : ∀ i, |(x.2 i : ℝ)-u i| ≤ L
  residue : ∀ i, (m : ℤ) ∣ x.2 i-v₀ i
  modulus_coprime : m.Coprime (x.1.1*x.1.2)
  radical_cutoff : (R22 h x.1.1 x.1.2 x.2 : ℝ) ≤ 1+L/(m : ℝ)
  conductor_lower : K0 ≤ NumericalConductor.K h x.1.1 x.1.2 x.2

theorem tag_positive (h : CoarseBounds F C) (x : Sample) :
    1 ≤ (tag h x).1 ∧ 1 ≤ (tag h x).2 :=
  ⟨primeHigh_pos h x.1.1 x.2,squareHigh_pos h x.1.2 x.2⟩

theorem tag_conductor (h : CoarseBounds F C) (x : Sample) :
    NumericalConductor.K h x.1.1 x.1.2 x.2 =
      NumericalConductor.K h (tag h x).1 (tag h x).2 x.2 :=
  K_eq_high h x.1.1 x.1.2 x.2

theorem tag_prime_depth (h : CoarseBounds F C) (x : Sample)
    (p : ℕ) (hp : p ∈ (tag h x).1.primeFactors) :
    2 ≤ NumericalConductor.primeDepth h p x.2 := by
  simp only [tag,primeFactors_primeHigh,Finset.mem_filter] at hp
  exact hp.2

theorem tag_square_depth (h : CoarseBounds F C) (x : Sample)
    (p : ℕ) (hp : p ∈ (tag h x).2.primeFactors) :
    2 ≤ NumericalConductor.squareDepth h p x.2 := by
  simp only [tag,primeFactors_squareHigh,Finset.mem_filter] at hp
  exact hp.2

variable {t : ℕ} {h : CoarseBounds F C}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
  {tables : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)}
  {D K0 : ℝ} {m : ℕ} {u : Fin 10 → ℝ} {L : ℝ}
  {v₀ : Fin 10 → ℤ} {x : Sample}

theorem InWindow.tag_squarefree (hx : InWindow h f tables D K0 m u L v₀ x) :
    Squarefree (tag h x).1 ∧ Squarefree (tag h x).2 := by
  have hs := parts_squarefree h x.1.1 x.1.2 hx.squarefree_left hx.squarefree_right x.2
  exact ⟨hs.2.1,hs.2.2.2⟩

theorem InWindow.tag_coprime (hx : InWindow h f tables D K0 m u L v₀ x) :
    (tag h x).1.Coprime (tag h x).2 :=
  (parts_pairwise_coprime h x.1.1 x.1.2 hx.squarefree_left hx.squarefree_right
    hx.coprime x.2).2.2.2.2.2

theorem InWindow.tag_modulus_coprime (hx : InWindow h f tables D K0 m u L v₀ x) :
    m.Coprime ((tag h x).1*(tag h x).2) :=
  Nat.Coprime.of_dvd_right (R22_dvd_mul h x.1.1 x.1.2 x.2) hx.modulus_coprime

theorem InWindow.tag_cutoff (hx : InWindow h f tables D K0 m u L v₀ x) :
    (((tag h x).1*(tag h x).2 : ℕ) : ℝ) ≤ 1+L/(m : ℝ) := hx.radical_cutoff

end CubicTenVariables.ConductorMeanDomain
