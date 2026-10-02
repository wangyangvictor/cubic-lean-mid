import TranslatedDepthSeven.PublishedCountingApplications
import TranslatedDepthSeven.PilaSubpower

/-!
# Pila's theorem in affine dimensions at most four

Pila's coefficient-uniform theorem counts every geometrically integral
piece of affine dimension at most four by `O(B^(4+epsilon))`.  This removes
the projection step for those pieces.  It does **not** treat the affine cone
over a projective fourfold, whose affine dimension is five; that single case
still requires the birational hypersurface projection used in the
manuscript.

This file first proves the estimate for one displayed affine dimension and degree.
It then takes a finite sum of the source constants, obtaining one constant
uniform for all `n <= 4` and all `1 <= d <= D`.
-/

namespace TranslatedDepthSeven

noncomputable section

open Published

/-- Pila's printed main power in dimension `n` and positive degree `d` is no
larger than `B^n` on the range `B >= 1`. -/
theorem pilaMainPower_le_dimensionPower
    {n d : ℕ} {B : ℝ} (hd : 1 ≤ d) (hB : 1 ≤ B) :
    B ^ ((n : ℝ) - 1 + (d : ℝ)⁻¹) ≤ B ^ (n : ℝ) := by
  apply Real.rpow_le_rpow_of_exponent_le hB
  have hdReal : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hinv : (d : ℝ)⁻¹ ≤ 1 := by
    exact (inv_le_one₀ (by positivity : (0 : ℝ) < d)).2 hdReal
  linarith

/-- Direct specialization of Pila 1995, Theorem A, to the clean exponent
`n + epsilon`.  Its constant is coefficient-uniform. -/
theorem pila1995_dimensionPower_uniform
    (hPila : Pila1995TheoremA)
    (N n d : ℕ) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (I : Ideal (MvPolynomial (Fin N) ℝ)),
        HasAffineDimensionDegree I n d →
        ∀ B : ℝ, 1 < B →
          ((pilaIntegralPoints I B).card : ℝ) ≤
            C * B ^ ((n : ℝ) + ε) := by
  obtain ⟨c, hc, hsource⟩ := hPila n d N hd
  let C : ℝ := c * pilaConstant d ε
  have hconstant : 0 < pilaConstant d ε := by
    unfold pilaConstant
    positivity
  refine ⟨C, mul_pos hc hconstant, ?_⟩
  intro I hI B hB
  have hB' : 1 ≤ B := hB.le
  have hprinted := hsource I
    (HasAffineDimensionDegree.toHilbert hI) B hB
  have hfactor := pilaFactor_le_const_mul_rpow
    (d := (d : ℝ)) (ε := ε) (H := B) (by positivity) hε hB'
  have hpower := pilaMainPower_le_dimensionPower (n := n) hd hB'
  have hmain_nonneg : 0 ≤ B ^ ((n : ℝ) - 1 + (d : ℝ)⁻¹) :=
    Real.rpow_nonneg (by positivity) _
  have hdim_nonneg : 0 ≤ B ^ (n : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  have hproduct :
      B ^ ((n : ℝ) - 1 + (d : ℝ)⁻¹) * pilaFactor d B ≤
        B ^ (n : ℝ) * (pilaConstant d ε * B ^ ε) := by
    exact mul_le_mul hpower hfactor
      (by unfold pilaFactor; positivity) hdim_nonneg
  calc
    ((pilaIntegralPoints I B).card : ℝ) ≤
        c * B ^ ((n : ℝ) - 1 + (d : ℝ)⁻¹) * pilaFactor d B := by
      simpa [pilaFactor] using hprinted
    _ = c * (B ^ ((n : ℝ) - 1 + (d : ℝ)⁻¹) * pilaFactor d B) := by
      ring
    _ ≤ c * (B ^ (n : ℝ) * (pilaConstant d ε * B ^ ε)) := by
      exact mul_le_mul_of_nonneg_left hproduct hc.le
    _ = C * B ^ ((n : ℝ) + ε) := by
      rw [Real.rpow_add (by positivity : 0 < B)]
      simp only [C]
      ring

/-- One coefficient-uniform constant for every affine dimension at most four
and every positive degree at most the fixed bound `D`.  This is the precise
source specialization used for proper pieces and nonsmooth stars. -/
theorem pila1995_dimensionAtMostFour_boundedDegree
    (hPila : Pila1995TheoremA)
    (N D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n d : ℕ), n ≤ 4 → 1 ≤ d → d ≤ D →
        ∀ (I : Ideal (MvPolynomial (Fin N) ℝ)),
          HasAffineDimensionDegree I n d →
          ∀ B : ℝ, 1 < B →
            ((pilaIntegralPoints I B).card : ℝ) ≤
              C * B ^ ((4 : ℝ) + ε) := by
  let S : Finset (ℕ × ℕ) :=
    (Finset.range 5).product (Finset.Icc 1 D)
  let J := {j : ℕ × ℕ // j ∈ S}
  have hEach : ∀ j : J, ∃ C : ℝ, 0 < C ∧
      ∀ (I : Ideal (MvPolynomial (Fin N) ℝ)),
        HasAffineDimensionDegree I j.1.1 j.1.2 →
        ∀ B : ℝ, 1 < B →
          ((pilaIntegralPoints I B).card : ℝ) ≤
            C * B ^ ((j.1.1 : ℝ) + ε) := by
    intro j
    have hjd : 1 ≤ j.1.2 := by
      have hj : j.1.1 ∈ Finset.range 5 ∧
          j.1.2 ∈ Finset.Icc 1 D := by
        exact Finset.mem_product.mp j.2
      exact (Finset.mem_Icc.mp hj.2).1
    exact pila1995_dimensionPower_uniform hPila N j.1.1 j.1.2 hjd ε hε
  choose c hc hbound using hEach
  let C : ℝ := 1 + ∑ j : J, c j
  have hc_nonneg : ∀ j : J, 0 ≤ c j := fun j ↦ (hc j).le
  have hC : 0 < C := by
    dsimp only [C]
    have hsum : 0 ≤ ∑ j : J, c j :=
      Finset.sum_nonneg fun j _ ↦ hc_nonneg j
    linarith
  refine ⟨C, hC, ?_⟩
  intro n d hn hd hdD I hI B hB
  have hmem : (n, d) ∈ S := by
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega), Finset.mem_Icc.mpr ⟨hd, hdD⟩⟩
  let j : J := ⟨(n, d), hmem⟩
  have hjbound := hbound j I (by simpa [j] using hI) B hB
  have hc_sum : c j ≤ ∑ k : J, c k := by
    classical
    exact Finset.single_le_sum
      (fun k _ ↦ hc_nonneg k) (Finset.mem_univ j)
  have hcC : c j ≤ C := by
    dsimp only [C]
    linarith
  have hBnonneg : 0 ≤ B ^ ((n : ℝ) + ε) :=
    Real.rpow_nonneg (by positivity) _
  have hcoefficient :
      c j * B ^ ((n : ℝ) + ε) ≤
        C * B ^ ((n : ℝ) + ε) :=
    mul_le_mul_of_nonneg_right hcC hBnonneg
  have hnReal : (n : ℝ) ≤ 4 := by exact_mod_cast hn
  have hpower : B ^ ((n : ℝ) + ε) ≤ B ^ ((4 : ℝ) + ε) := by
    apply Real.rpow_le_rpow_of_exponent_le hB.le
    linarith
  exact hjbound.trans <| hcoefficient.trans <|
    mul_le_mul_of_nonneg_left hpower hC.le

/-- Transfer the uniform low-dimensional Pila estimate to any literal finite
set through an injective integral-coordinate map. -/
theorem finiteSet_card_le_pila_dimensionAtMostFour
    (hPila : Pila1995TheoremA)
    {Point : Type*} [DecidableEq Point]
    (N D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n d : ℕ), n ≤ 4 → 1 ≤ d → d ≤ D →
        ∀ (I : Ideal (MvPolynomial (Fin N) ℝ)),
          HasAffineDimensionDegree I n d →
          ∀ B : ℝ, 1 < B →
            ∀ (points : Finset Point) (coordinate : Point → IntVector N),
              Set.InjOn coordinate (↑points : Set Point) →
              (∀ x ∈ points, coordinate x ∈ pilaIntegralPoints I B) →
              (points.card : ℝ) ≤ C * B ^ ((4 : ℝ) + ε) := by
  classical
  obtain ⟨C, hC, hbound⟩ :=
    pila1995_dimensionAtMostFour_boundedDegree hPila N D ε hε
  refine ⟨C, hC, ?_⟩
  intro n d hn hd hdD I hI B hB points coordinate hinjective hcoordinate
  let image := points.image coordinate
  have hcard : image.card = points.card :=
    Finset.card_image_iff.mpr hinjective
  have hsubset : image ⊆ pilaIntegralPoints I B := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact hcoordinate x hx
  calc
    (points.card : ℝ) = (image.card : ℝ) := by rw [hcard]
    _ ≤ ((pilaIntegralPoints I B).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ C * B ^ ((4 : ℝ) + ε) :=
      hbound n d hn hd hdD I hI B hB

end

end TranslatedDepthSeven
