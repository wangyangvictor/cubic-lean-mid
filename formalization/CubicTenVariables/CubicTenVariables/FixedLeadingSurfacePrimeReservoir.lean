import CubicTenVariables.FixedDegreeGradientPrimeSum
import CubicTenVariables.RankSevenActualSurfaceGoodRecordPrimeBounds
import TranslatedDepthSeven.PrimeSubsetPrefixReservoirBridge

/-!
# Actual prime reservoirs uniform in bounded-height equations

The canonical base pool is chosen from d,e,a,H before the equation or point.
Primes dividing m are deleted globally. Each actual nonzero gradient then
has enough surviving smooth primes. The certificate exponent is e+d+2,
not a constant chosen after the varying equation.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace CubicTenVariables.FixedLeadingSurfacePrimeReservoir
open MvPolynomial TranslatedDepthSeven Filter
open scoped BigOperators Topology

/-- The actual primes at which at least one affine partial stays nonzero. -/
def smoothAllowedPrimes (P : Finset ℕ) (F : MvPolynomial (Fin 4) ℤ)
    (x : Fin 3 → ℤ) : Finset ℕ := by
  classical
  exact P.filter fun p => ∃ i, (eval x
    (pderiv i (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0

@[simp] theorem mem_smoothAllowedPrimes (P : Finset ℕ)
    (F : MvPolynomial (Fin 4) ℤ) (x : Fin 3 → ℤ) (p : ℕ) :
    p ∈ smoothAllowedPrimes P F x ↔ p ∈ P ∧ ∃ i, (eval x
      (pderiv i (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0 := by
  classical
  simp [smoothAllowedPrimes]

theorem smoothAllowedPrimes_subset (P : Finset ℕ)
    (F : MvPolynomial (Fin 4) ℤ) (x : Fin 3 → ℤ) :
    smoothAllowedPrimes P F x ⊆ P := by
  intro p hp
  exact (mem_smoothAllowedPrimes P F x p).mp hp |>.1

/-- A fixed natural exponent controls every prefix times the progression
modulus. It is independent of the equation, its coefficients and the point. -/
def prefixHeightExponent (d e : ℕ) (a : ℝ) : ℕ :=
  ⌈2 * (manuscriptPoolDepthCoefficient (e + d + 2 : ℕ) a + 1)⌉₊ + 1

theorem prefix_modulus_mul_le_of_pool_product
    {P₀ P : Finset ℕ} {H A m depth : ℕ}
    (hprime : ∀ p ∈ P₀, p.Prime) (hP : P ⊆ P₀)
    (hpool : primeProduct P₀ ≤ H ^ A) (hm : m ≤ H)
    (v : PrimeSubsetPrefix.Vertex P depth) :
    m * PrimeSubsetPrefix.modulus v ≤ H ^ (A + 1) := by
  have hv : v.1 ⊆ P₀ := (PrimeSubsetPrefix.mem_vertices.mp v.2).1.trans hP
  have hprod : primeProduct v.1 ≤ primeProduct P₀ := by
    exact Finset.prod_le_prod_of_subset_of_one_le' hv
      (fun p hp _ => (hprime p hp).one_lt.le)
  calc
    m * PrimeSubsetPrefix.modulus v ≤ H * H ^ A :=
      Nat.mul_le_mul hm (hprod.trans hpool)
    _ = H ^ (A + 1) := by rw [pow_succ]; exact Nat.mul_comm _ _

/-- The usable prime pool and depth are literal canonical constructions.
All constants and both choices precede every varying equation. The final
clause proves room for each actual nonsingular point, rather than assuming
an abstract coverage or bad-prime bound. -/
theorem exists_uniform_actual_smooth_prime_reservoir
    (d e : ℕ) (a Cres δ : ℝ)
    (ha : 0 < a) (haOne : a < 1) (hCres : 1 < Cres) (hδ : 0 < δ) :
    ∃ H₀ : ℕ, 2 ≤ H₀ ∧ ∀ H : ℕ, H₀ ≤ H →
      ∀ T : ℝ, 1 ≤ T → T ≤ H → ∀ m : ℕ, 0 < m → m ≤ H →
      let P := certificateAllowedPrimes
        (manuscriptPrimePoolAt (e + d + 2 : ℕ) a H) (m : ℤ)
      let depth := manuscriptCrossingAt (e + d + 2 : ℕ) a Cres H T
      (∀ p ∈ P, p.Prime) ∧ (∀ p ∈ P, ¬ p ∣ m) ∧
      depth ≤ P.card ∧
      P.card ≤ reservoirDepth (manuscriptPoolDepthCoefficient (e + d + 2 : ℕ) a) H ∧
      (∀ p ∈ P,
        ⌊manuscriptPrimeIntervalCoefficient (e + d + 2 : ℕ) a * Real.log H⌋₊ < p ∧
        p ≤ ⌊2 * (manuscriptPrimeIntervalCoefficient (e + d + 2 : ℕ) a * Real.log H)⌋₊) ∧
      (∀ v : PrimeSubsetPrefix.Vertex P depth,
        m * PrimeSubsetPrefix.modulus v ≤ H ^ prefixHeightExponent d e a) ∧
      (∀ q ∈ modulusReservoir P depth, Squarefree q ∧ Cres * T ^ a ≤ (q : ℝ) ∧
        (q : ℝ) ≤ (4 * manuscriptPrimeIntervalCoefficient (e + d + 2 : ℕ) a *
          (δ / 3)⁻¹) * Cres * T ^ a * H ^ δ) ∧
      ∀ F : MvPolynomial (Fin 4) ℤ,
        (surfaceHypersurfaceFirstChartDehomogenize F).totalDegree ≤ d →
        mvPolynomialCoefficientNatAbsMax (surfaceHypersurfaceFirstChartDehomogenize F) ≤ H ^ e →
        ∀ x : Fin 3 → ℤ, (∀ i, (x i).natAbs ≤ H) →
        (∃ i, eval x (pderiv i (surfaceHypersurfaceFirstChartDehomogenize F)) ≠ 0) →
        depth ≤ (smoothAllowedPrimes P F x).card := by
  classical
  let E : ℕ := e + d + 2
  have hE : (0 : ℝ) ≤ (E : ℝ) := Nat.cast_nonneg E
  have hres := tendsto_natCast_atTop_atTop.eventually
    (eventually_exists_manuscriptReservoir hE ha haOne hCres hδ)
  have hprod := eventually_primeProduct_manuscriptPrimePoolAt_le_nat_pow hE ha haOne
  obtain ⟨H₁, hH₁⟩ := eventually_atTop.mp (hres.and hprod)
  let threshold := max 2 ((d + 1) ^ 3 * d)
  refine ⟨max threshold H₁, (Nat.le_max_left _ _).trans (Nat.le_max_left _ _), ?_⟩
  intro H hH T hT hTH m hm hmH
  have hthreshold : threshold ≤ H := (Nat.le_max_left _ _).trans hH
  have hHone : 1 ≤ H := by dsimp [threshold] at hthreshold; omega
  obtain ⟨hresH, hprodH⟩ := hH₁ H ((Nat.le_max_right _ _).trans hH)
  obtain ⟨P₀, depth, hP₀, hdepth, hcard, hprimes, _hdepthP₀,
    hmoduli, _hmass, _hlcm, hcertOne, hcertTwo⟩ := hresH T hT hTH
  let P := certificateAllowedPrimes P₀ (m : ℤ)
  have hsub : P ⊆ P₀ := Finset.filter_subset _ _
  have hprime : ∀ p ∈ P₀, p.Prime := fun p hp => (hprimes p hp).1
  have hmzero : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmheight : (((m : ℤ).natAbs : ℕ) : ℝ) ≤ (H : ℝ) ^ (E : ℝ) := by
    rw [Real.rpow_natCast]
    have hb : m ≤ H ^ E := hmH.trans (by
      calc H = H ^ 1 := by simp
           _ ≤ H ^ E := Nat.pow_le_pow_right hHone (by dsimp [E]; omega))
    exact_mod_cast hb
  have hroom : depth ≤ P.card := by
    obtain ⟨_, ⟨s⟩, _⟩ := hcertOne (m : ℤ) hmzero hmheight
    exact s.2.2.symm.trans_le (Finset.card_le_card s.2.1)
  change (∀ p ∈ certificateAllowedPrimes _ _, _) ∧ _
  rw [← hP₀, ← hdepth]
  change (∀ p ∈ P, _) ∧ _
  refine ⟨fun p hp => hprime p (hsub hp), ?_, hroom,
    (Finset.card_le_card hsub).trans_eq hcard, ?_, ?_, ?_, ?_⟩
  · intro p hp hdiv
    exact (Finset.mem_filter.mp hp).2 (by exact_mod_cast hdiv)
  · intro p hp
    exact (hprimes p (hsub hp)).2
  · intro v
    apply prefix_modulus_mul_le_of_pool_product hprime hsub _ hmH v
    simpa only [hP₀] using hprodH
  · intro q hq
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
    have hs' := Finset.mem_powersetCard.mp hs
    exact hmoduli s (Finset.mem_powersetCard.mpr ⟨hs'.1.trans hsub, hs'.2⟩)
  · intro F hdegree hcoeff x hx hgrad
    obtain ⟨i, hi⟩ := hgrad
    let J := eval x (pderiv i (surfaceHypersurfaceFirstChartDehomogenize F))
    have hJheight : (J.natAbs : ℝ) ≤ (H : ℝ) ^ (E : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast FixedDegreeGradientPrimeSum.eval_pderiv_natAbs_le_uniform_height_power
        _ hthreshold hdegree hcoeff x hx i
    obtain ⟨_, ⟨s⟩, _⟩ := hcertTwo (m : ℤ) J hmzero hi hmheight hJheight
    apply s.2.2.symm.trans_le
    apply Finset.card_le_card
    intro p hp
    obtain ⟨hp₀, hpm, hpJ⟩ := Finset.mem_filter.mp (s.2.1 hp)
    apply (mem_smoothAllowedPrimes P F x p).mpr
    refine ⟨Finset.mem_filter.mpr ⟨hp₀, hpm⟩, i, ?_⟩
    intro hz
    exact hpJ ((ZMod.intCast_zmod_eq_zero_iff_dvd J p).mp hz)

end CubicTenVariables.FixedLeadingSurfacePrimeReservoir
