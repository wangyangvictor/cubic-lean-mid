import TranslatedDepthSeven.PublishedCountingApplications
import TranslatedDepthSeven.PilaSubpower

/-!
# Pila for affine dimension five and degree at least eight

The rank-at-most-six locus has possible affine-cone components of dimension
five.  For projective degree at least eight, Pila's printed exponent is

`5 - 1 + 1 / d <= 4 + 1 / 8 = 33 / 8`.

This file records that direct specialization, uniformly over a bounded set
of dimensions and degrees.  It avoids any birational projection to a
hypersurface.
-/

namespace TranslatedDepthSeven

noncomputable section

open Published

/-- The main power in Pila's theorem is at most `B^(33/8)` in affine
dimension at most five and degree at least eight. -/
theorem pilaMainPower_le_thirtyThreeEighths
    {n d : ℕ} {B : ℝ} (hn : n ≤ 5) (hd : 8 ≤ d) (hB : 1 ≤ B) :
    B ^ ((n : ℝ) - 1 + (d : ℝ)⁻¹) ≤ B ^ (33 / 8 : ℝ) := by
  apply Real.rpow_le_rpow_of_exponent_le hB
  have hnReal : (n : ℝ) ≤ 5 := by exact_mod_cast hn
  have hdReal : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have hinv : (d : ℝ)⁻¹ ≤ (8 : ℝ)⁻¹ := by
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8) hdReal)
  norm_num at hinv ⊢
  linarith

/-- Pila's coefficient-uniform estimate for one affine variety in the
range `n <= 5`, `8 <= d`. -/
theorem pila1995_thirtyThreeEighths_uniform
    (hPila : Pila1995TheoremA)
    (N n d : ℕ) (hn : n ≤ 5) (hd : 8 ≤ d)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (I : Ideal (MvPolynomial (Fin N) ℝ)),
        HasAffineHilbertDimensionDegree I n d →
        ∀ B : ℝ, 1 < B →
          ((pilaIntegralPoints I B).card : ℝ) ≤
            C * B ^ ((33 / 8 : ℝ) + ε) := by
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
  have hmain := pilaMainPower_le_thirtyThreeEighths hn hd hB.le
  have hproduct :
      B ^ ((n : ℝ) - 1 + (d : ℝ)⁻¹) * pilaFactor d B ≤
        B ^ (33 / 8 : ℝ) * (pilaConstant d ε * B ^ ε) := by
    exact mul_le_mul hmain hfactor
      (by unfold pilaFactor; positivity) (by positivity)
  calc
    ((pilaIntegralPoints I B).card : ℝ) ≤
        c * B ^ ((n : ℝ) - 1 + (d : ℝ)⁻¹) * pilaFactor d B := by
      simpa [pilaFactor] using hprinted
    _ = c * (B ^ ((n : ℝ) - 1 + (d : ℝ)⁻¹) * pilaFactor d B) := by
      ring
    _ ≤ c * (B ^ (33 / 8 : ℝ) * (pilaConstant d ε * B ^ ε)) := by
      exact mul_le_mul_of_nonneg_left hproduct hc.le
    _ = C * B ^ ((33 / 8 : ℝ) + ε) := by
      rw [Real.rpow_add (by positivity : 0 < B)]
      simp only [C]
      ring

/-- One coefficient-uniform constant for all affine dimensions at most five
and all degrees in the fixed interval `[8,D]`. -/
theorem pila1995_affineDimensionAtMostFive_degreeAtLeastEight_boundedDegree
    (hPila : Pila1995TheoremA)
    (N D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n d : ℕ), n ≤ 5 → 8 ≤ d → d ≤ D →
        ∀ (I : Ideal (MvPolynomial (Fin N) ℝ)),
          HasAffineHilbertDimensionDegree I n d →
          ∀ B : ℝ, 1 < B →
            ((pilaIntegralPoints I B).card : ℝ) ≤
              C * B ^ ((33 / 8 : ℝ) + ε) := by
  let S : Finset (ℕ × ℕ) :=
    (Finset.range 6).product (Finset.Icc 8 D)
  let J := {j : ℕ × ℕ // j ∈ S}
  have hEach : ∀ j : J, ∃ C : ℝ, 0 < C ∧
      ∀ (I : Ideal (MvPolynomial (Fin N) ℝ)),
        HasAffineHilbertDimensionDegree I j.1.1 j.1.2 →
        ∀ B : ℝ, 1 < B →
          ((pilaIntegralPoints I B).card : ℝ) ≤
            C * B ^ ((33 / 8 : ℝ) + ε) := by
    intro j
    have hj := Finset.mem_product.mp j.2
    have hn : j.1.1 ≤ 5 := by
      have := Finset.mem_range.mp hj.1
      omega
    have hd : 8 ≤ j.1.2 := (Finset.mem_Icc.mp hj.2).1
    exact pila1995_thirtyThreeEighths_uniform
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
