import TranslatedDepthSeven.PublishedCountingApplications
import TranslatedDepthSeven.PilaSubpower

/-!
# Pila for affine dimension five and degree at least three

For affine dimension at most five and degree at least three, Pila's main
power is at most `4 + 1/3 = 13/3`.  This is already strictly below the
target `94/21`; consequently only degrees one and two require a separate
geometric argument in the strict low-rank branch.
-/

namespace TranslatedDepthSeven

noncomputable section

open Published

/-- The main power in Pila's theorem is at most `B^(13/3)` in affine
dimension at most five and degree at least three. -/
theorem pilaMainPower_le_thirteenThirds
    {n d : ℕ} {B : ℝ} (hn : n ≤ 5) (hd : 3 ≤ d) (hB : 1 ≤ B) :
    B ^ ((n : ℝ) - 1 + (d : ℝ)⁻¹) ≤ B ^ (13 / 3 : ℝ) := by
  apply Real.rpow_le_rpow_of_exponent_le hB
  have hnReal : (n : ℝ) ≤ 5 := by exact_mod_cast hn
  have hdReal : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hinv : (d : ℝ)⁻¹ ≤ (3 : ℝ)⁻¹ := by
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3) hdReal)
  norm_num at hinv ⊢
  linarith

/-- Pila's coefficient-uniform estimate for one affine variety in the
range `n ≤ 5`, `3 ≤ d`. -/
theorem pila1995_thirteenThirds_uniform
    (hPila : Pila1995TheoremA)
    (N n d : ℕ) (hn : n ≤ 5) (hd : 3 ≤ d)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (I : Ideal (MvPolynomial (Fin N) ℝ)),
        HasAffineHilbertDimensionDegree I n d →
        ∀ B : ℝ, 1 < B →
          ((pilaIntegralPoints I B).card : ℝ) ≤
            C * B ^ ((13 / 3 : ℝ) + ε) := by
  have hdOne : 1 ≤ d := by omega
  obtain ⟨c, hc, hsource⟩ := hPila n d N hdOne
  let C : ℝ := c * pilaConstant d ε
  have hconstant : 0 < pilaConstant d ε := by
    unfold pilaConstant
    positivity
  refine ⟨C, mul_pos hc hconstant, ?_⟩
  intro I hI B hB
  have hprinted := hsource I hI B hB
  have hfactor := pilaFactor_le_const_mul_rpow
    (d := (d : ℝ)) (ε := ε) (H := B) (by positivity) hε hB.le
  have hmain := pilaMainPower_le_thirteenThirds hn hd hB.le
  have hproduct :
      B ^ ((n : ℝ) - 1 + (d : ℝ)⁻¹) * pilaFactor d B ≤
        B ^ (13 / 3 : ℝ) * (pilaConstant d ε * B ^ ε) := by
    exact mul_le_mul hmain hfactor
      (by unfold pilaFactor; positivity) (by positivity)
  calc
    ((pilaIntegralPoints I B).card : ℝ) ≤
        c * B ^ ((n : ℝ) - 1 + (d : ℝ)⁻¹) * pilaFactor d B := by
      simpa [pilaFactor] using hprinted
    _ = c * (B ^ ((n : ℝ) - 1 + (d : ℝ)⁻¹) * pilaFactor d B) := by
      ring
    _ ≤ c * (B ^ (13 / 3 : ℝ) * (pilaConstant d ε * B ^ ε)) := by
      exact mul_le_mul_of_nonneg_left hproduct hc.le
    _ = C * B ^ ((13 / 3 : ℝ) + ε) := by
      rw [Real.rpow_add (by positivity : 0 < B)]
      simp only [C]
      ring

/-- One coefficient-uniform constant for all affine dimensions at most five
and all degrees in the fixed interval `[3,D]`. -/
theorem pila1995_affineDimensionAtMostFive_degreeAtLeastThree_boundedDegree
    (hPila : Pila1995TheoremA)
    (N D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n d : ℕ), n ≤ 5 → 3 ≤ d → d ≤ D →
        ∀ (I : Ideal (MvPolynomial (Fin N) ℝ)),
          HasAffineHilbertDimensionDegree I n d →
          ∀ B : ℝ, 1 < B →
            ((pilaIntegralPoints I B).card : ℝ) ≤
              C * B ^ ((13 / 3 : ℝ) + ε) := by
  let S : Finset (ℕ × ℕ) :=
    (Finset.range 6).product (Finset.Icc 3 D)
  let J := {j : ℕ × ℕ // j ∈ S}
  have hEach : ∀ j : J, ∃ C : ℝ, 0 < C ∧
      ∀ (I : Ideal (MvPolynomial (Fin N) ℝ)),
        HasAffineHilbertDimensionDegree I j.1.1 j.1.2 →
        ∀ B : ℝ, 1 < B →
          ((pilaIntegralPoints I B).card : ℝ) ≤
            C * B ^ ((13 / 3 : ℝ) + ε) := by
    intro j
    have hj := Finset.mem_product.mp j.2
    have hn : j.1.1 ≤ 5 := by
      have := Finset.mem_range.mp hj.1
      omega
    have hd : 3 ≤ j.1.2 := (Finset.mem_Icc.mp hj.2).1
    exact pila1995_thirteenThirds_uniform
      hPila N j.1.1 j.1.2 hn hd ε hε
  choose c hc hbound using hEach
  let C : ℝ := 1 + ∑ j : J, c j
  have hC : 0 < C := by
    dsimp only [C]
    have hsum : 0 ≤ ∑ j : J, c j :=
      Finset.sum_nonneg fun j _ ↦ (hc j).le
    linarith
  refine ⟨C, hC, ?_⟩
  intro n d hn hd hdD I hI B hB
  have hmem : (n, d) ∈ S := Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (by omega), Finset.mem_Icc.mpr ⟨hd, hdD⟩⟩
  let j : J := ⟨(n, d), hmem⟩
  have hjbound := hbound j I (by simpa [j] using hI) B hB
  have hcSum : c j ≤ ∑ k : J, c k := by
    exact Finset.single_le_sum
      (fun k _ ↦ (hc k).le) (Finset.mem_univ j)
  have hcC : c j ≤ C := by
    dsimp only [C]
    linarith
  exact hjbound.trans
    (mul_le_mul_of_nonneg_right hcC (by positivity))

end

end TranslatedDepthSeven
