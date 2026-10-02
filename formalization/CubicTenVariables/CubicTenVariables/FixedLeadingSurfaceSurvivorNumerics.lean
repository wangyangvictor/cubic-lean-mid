import CubicTenVariables.FixedLeadingSurfaceSurvivorResidual
import TranslatedDepthSeven.QuantitativePrefixChangedEdgeModulusSensitive
import TranslatedDepthSeven.ReservoirSubpower
import TranslatedDepthSeven.QuantitativePrefixSurfaceCountEffectiveTwoCapNumerics
import TranslatedDepthSeven.QuantitativePrefixSurfaceCountEffectiveTwoCapCenteredCurve

/-!
# Numerical bounds for the actual survivor auxiliary family

The root and terminal cuts retain different caps. The global edge sum retains
both inverse-modulus factors and pays only a subpower for the finite prefix
family. All estimates are unconditional and apply to point-dependent survivors.
-/

namespace CubicTenVariables.FixedLeadingSurfaceSurvivorNumerics
noncomputable section
open MvPolynomial TranslatedDepthSeven Published
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000

/-- The uniform root cap is the literal ceiling emitted by the degree bound. -/
theorem root_degree_cap
    {P : Finset ℕ} {depth H B b : ℕ} {η α : ℝ}
    (hP : ∀ p ∈ P, p.Prime)
    (blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ)
    (hblock : ∀ v, (blockDegree v : ℝ) ≤ 2 * (H : ℝ) ^ η *
      (1 + (B : ℝ) ^ α / (PrimeSubsetPrefix.modulus v : ℝ))) :
    b + blockDegree (PrimeSubsetPrefix.root P depth) ≤
      b + quantitativePrefixUniformBlockDegree H B η α := by
  exact Nat.add_le_add_left
    (blockDegree_le_quantitativePrefixUniformBlockDegree
      hP blockDegree hblock (PrimeSubsetPrefix.root P depth)) b

/-- Any vertex whose modulus reaches `B^α` has the small terminal cap. -/
theorem terminal_degree_cap
    {P : Finset ℕ} {depth H B b : ℕ} {η α : ℝ}
    (hP : ∀ p ∈ P, p.Prime)
    (blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ)
    (hblock : ∀ v, (blockDegree v : ℝ) ≤ 2 * (H : ℝ) ^ η *
      (1 + (B : ℝ) ^ α / (PrimeSubsetPrefix.modulus v : ℝ)))
    (v : PrimeSubsetPrefix.Vertex P depth)
    (hlower : (B : ℝ) ^ α ≤ (PrimeSubsetPrefix.modulus v : ℝ)) :
    b + blockDegree v ≤ b + ⌈4 * (H : ℝ) ^ η⌉₊ := by
  have hprime : ∀ p ∈ v.1, p.Prime := fun p hp =>
    hP p ((PrimeSubsetPrefix.mem_vertices.mp v.2).1 hp)
  have hq : (0 : ℝ) < PrimeSubsetPrefix.modulus v := by
    exact_mod_cast Nat.pos_of_ne_zero (primeProduct_ne_zero hprime)
  have hdiv : (B : ℝ) ^ α / (PrimeSubsetPrefix.modulus v : ℝ) ≤ 1 :=
    (div_le_one hq).mpr hlower
  have hk : (blockDegree v : ℝ) ≤ 4 * (H : ℝ) ^ η := by
    calc
      (blockDegree v : ℝ) ≤ 2 * (H : ℝ) ^ η *
          (1 + (B : ℝ) ^ α / (PrimeSubsetPrefix.modulus v : ℝ)) := hblock v
      _ ≤ 2 * (H : ℝ) ^ η * 2 := by gcongr; linarith
      _ = 4 * (H : ℝ) ^ η := by ring
  have hceil : blockDegree v ≤ ⌈4 * (H : ℝ) ^ η⌉₊ := by
    exact_mod_cast hk.trans (Nat.le_ceil _)
  exact Nat.add_le_add_left hceil b

/-- Point-dependent survivor auxiliaries give the sharp global edge bound. -/
theorem sum_changedEdges_le_modulusSensitive
    {d b H B Q R : ℕ} {eta a : ℝ}
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    (hgeometricPrime : ((finiteEquationIdeal sourceEquations).map
      (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime)
    (hhom : (finiteEquationIdeal sourceEquations).IsHomogeneous
      (homogeneousSubmodule (Fin 4) ℚ))
    (hdegree : HasProjectiveDimensionDegree
      (finiteEquationIdeal sourceEquations) 2 d)
    (F : MvPolynomial (Fin 4) ℤ)
    (P : Finset ℕ) (depth : ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (m : ℕ) (hm : 0 < m) (hPm : ∀ p ∈ P, ¬ p ∣ m)
    (u : Fin 3 → ℤ) (X : Finset (Fin 3 → ℤ))
    (allowed : (Fin 3 → ℤ) → Finset ℕ)
    (blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ)
    (auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
        MvPolynomial (Fin 4) ℚ)
    (hH : (1 : ℝ) ≤ H) (heta : 0 ≤ eta)
    (hallowed : ∀ z ∈ X, allowed z ⊆ P)
    (hroom : ∀ z ∈ X, depth ≤ (allowed z).card)
    (hterminal : ∀ z ∈ X,
      ∀ t ∈ PrimeSubsetPrefix.survivingVertices P (allowed z) depth,
        t.1.card = depth → PrimeSubsetPrefix.modulus t ≤ Q)
    (hprimeCap : ∀ p ∈ P, p ≤ R)
    (hblock : ∀ t,
      ((blockDegree t : ℕ) : ℝ) ≤ 2 * (H : ℝ) ^ eta *
        (1 + (B : ℝ) ^ a /
          (PrimeSubsetPrefix.modulus t : ℝ)))
    (hauxiliary : ∀ z ∈ X, ∀ v ∈
      PrimeSubsetPrefix.survivingVertices P (allowed z) depth,
        (auxiliary v (integralResidueVector z)).IsHomogeneous (b + blockDegree v) ∧
          auxiliary v (integralResidueVector z) ∉ finiteEquationIdeal sourceEquations)
    (hauxZero : ∀ z ∈ X, ∀ v ∈
      PrimeSubsetPrefix.survivingVertices P (allowed z) depth,
      MvPolynomial.eval
        (fun i => (progressionHomogeneousPoint u m z i : ℚ))
          (auxiliary v (integralResidueVector z)) = 0)
    (hsource : ∀ z ∈ X,
      (fun i => (progressionHomogeneousPoint u m z i : ℚ)) ∈
        finiteAffineCommonZeroLocus sourceEquations)
    (hzero : ∀ z ∈ X,
      MvPolynomial.eval (progressionHomogeneousPoint u m z) F = 0)
    (hsmooth : ∀ z ∈ X, ∀ p ∈ allowed z, ∃ i,
      (MvPolynomial.eval (fun j => u j + (m : ℤ) * z j)
        (MvPolynomial.pderiv i
          (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0) :
    ((∑ v : PrimeSubsetPrefix.Vertex P depth,
      ∑ w : PrimeSubsetPrefix.Vertex P depth,
        (quantitativePrefixChangedEdgeCell sourceEquations auxiliary
          u m X allowed v w).card : ℕ) : ℝ) ≤
      (PrimeSubsetPrefix.directedEdges P depth).card *
        quantitativePrefixModulusSensitiveEdgeMajorant
          (surfaceHypersurfaceFirstChartDehomogenize F).totalDegree
          depth d b H B Q R eta a := by
  apply sum_card_quantitativePrefixChangedEdgeCell_le_modulusSensitive
    sourceEquations P depth hP u m X allowed blockDegree auxiliary hH heta
      hallowed hroom hterminal hprimeCap hblock
  intro v w
  exact FixedLeadingSurfaceSurvivorResidual.card_changedEdge_le_squarefree_of_survivor_auxiliaries
    sourceEquations hgeometricPrime hhom hdegree F P depth hP m hm hPm
      u X allowed blockDegree auxiliary hauxiliary hauxZero hsource
      hzero hsmooth v w


/-- Both the number of edges and the local degree factor are absorbed by
one explicit reservoir threshold. -/
theorem directedEdge_degree_mass_le_subpower
    (P : Finset ℕ) (depth Δ : ℕ) (M H δ : ℝ)
    (hM : 0 ≤ M) (hδ : 0 < δ)
    (hcard : P.card ≤ reservoirDepth M H)
    (hdepth : depth ≤ reservoirDepth M H)
    (hthreshold : reservoirSubpowerThreshold M
      (4 * ((max 1 Δ : ℕ) : ℝ)) δ ≤ H) :
    ((PrimeSubsetPrefix.directedEdges P depth).card : ℝ) *
      ((max 1 Δ : ℕ) : ℝ) ^ depth ≤ H ^ δ := by
  have hΔ : 0 < max 1 Δ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hcomb : (PrimeSubsetPrefix.directedEdges P depth).card *
      (max 1 Δ) ^ depth ≤ (4 * max 1 Δ) ^ reservoirDepth M H := by
    calc
      (PrimeSubsetPrefix.directedEdges P depth).card * (max 1 Δ) ^ depth ≤
          4 ^ P.card * (max 1 Δ) ^ depth :=
        Nat.mul_le_mul_right _ (PrimeSubsetPrefix.card_directedEdges_le_four_pow P depth)
      _ ≤ 4 ^ reservoirDepth M H * (max 1 Δ) ^ reservoirDepth M H :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hcard)
          (Nat.pow_le_pow_right hΔ hdepth)
      _ = (4 * max 1 Δ) ^ reservoirDepth M H := by rw [mul_pow]
  have hcast : ((PrimeSubsetPrefix.directedEdges P depth).card : ℝ) *
      ((max 1 Δ : ℕ) : ℝ) ^ depth ≤
      (4 * ((max 1 Δ : ℕ) : ℝ)) ^ reservoirDepth M H := by
    exact_mod_cast hcomb
  exact hcast.trans (reservoirBase_pow_depth_le_rpow hM
    (by have h : (1 : ℝ) ≤ ((max 1 Δ : ℕ) : ℝ) := by exact_mod_cast le_max_left 1 Δ
        linarith) hδ hthreshold)

/-- Substituting the actual logarithmic-prime reservoir scales costs only
`H^(2η+3δ) B^(2α)`. The constants in this statement do not depend on the
surface equation or its lower coefficients. -/
theorem edge_majorant_le_twoRadius
    (P : Finset ℕ) (depth Δ d b H B Q R : ℕ)
    (η α δ Cq Cr : ℝ)
    (hH : (1 : ℝ) ≤ H) (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hCq : 0 ≤ Cq) (hCr : 0 ≤ Cr)
    (hmass : ((PrimeSubsetPrefix.directedEdges P depth).card : ℝ) *
      ((max 1 Δ : ℕ) : ℝ) ^ depth ≤ (H : ℝ) ^ δ)
    (hQ : (Q : ℝ) ≤ Cq * (H : ℝ) ^ δ * (B : ℝ) ^ α)
    (hR : (R : ℝ) ≤ Cr * (H : ℝ) ^ δ) :
    ((PrimeSubsetPrefix.directedEdges P depth).card : ℝ) *
      quantitativePrefixModulusSensitiveEdgeMajorant
        Δ depth d b H B Q R η α ≤
      ((d : ℝ) * ((b : ℝ) + 2)) ^ 2 *
        (Cq ^ 2 + Cq * Cr + Cq + Cr) *
        (H : ℝ) ^ (2 * η + 3 * δ) * (B : ℝ) ^ (2 * α) := by
  have hHp : (0 : ℝ) < H := zero_lt_one.trans_le hH
  have hBp : (0 : ℝ) < B := by exact_mod_cast hB
  have hHδ : 1 ≤ (H : ℝ) ^ δ := Real.one_le_rpow hH hδ
  have hHδsq : (H : ℝ) ^ δ ≤ ((H : ℝ) ^ δ) ^ 2 := by nlinarith
  have hHδ0 : 0 ≤ (H : ℝ) ^ δ := by positivity
  have hBα0 : 0 ≤ (B : ℝ) ^ α := by positivity
  have hQ2 : (Q : ℝ) ^ 2 ≤ Cq ^ 2 * ((H : ℝ) ^ δ) ^ 2 *
      ((B : ℝ) ^ α) ^ 2 := by
    calc
      (Q : ℝ) ^ 2 ≤ (Cq * (H : ℝ) ^ δ * (B : ℝ) ^ α) ^ 2 := by gcongr
      _ = _ := by ring
  have hQR : (B : ℝ) ^ α * (Q : ℝ) * (R : ℝ) ≤
      Cq * Cr * ((H : ℝ) ^ δ) ^ 2 * ((B : ℝ) ^ α) ^ 2 := by
    calc
      (B : ℝ) ^ α * (Q : ℝ) * (R : ℝ) ≤
          (B : ℝ) ^ α * (Cq * (H : ℝ) ^ δ * (B : ℝ) ^ α) *
            (Cr * (H : ℝ) ^ δ) := by gcongr
      _ = _ := by ring
  have hQa : (B : ℝ) ^ α * (Q : ℝ) ≤
      Cq * ((H : ℝ) ^ δ) ^ 2 * ((B : ℝ) ^ α) ^ 2 := by
    calc
      (B : ℝ) ^ α * (Q : ℝ) ≤
          (B : ℝ) ^ α * (Cq * (H : ℝ) ^ δ * (B : ℝ) ^ α) := by gcongr
      _ = Cq * (H : ℝ) ^ δ * ((B : ℝ) ^ α) ^ 2 := by ring
      _ ≤ _ := by gcongr
  have hRa : ((B : ℝ) ^ α) ^ 2 * (R : ℝ) ≤
      Cr * ((H : ℝ) ^ δ) ^ 2 * ((B : ℝ) ^ α) ^ 2 := by
    calc
      ((B : ℝ) ^ α) ^ 2 * (R : ℝ) ≤
          ((B : ℝ) ^ α) ^ 2 * (Cr * (H : ℝ) ^ δ) := by gcongr
      _ = Cr * (H : ℝ) ^ δ * ((B : ℝ) ^ α) ^ 2 := by ring
      _ ≤ _ := by gcongr
  have hsum : (Q : ℝ) ^ 2 + (B : ℝ) ^ α * (Q : ℝ) * (R : ℝ) +
      (B : ℝ) ^ α * (Q : ℝ) + ((B : ℝ) ^ α) ^ 2 * (R : ℝ) ≤
      (Cq ^ 2 + Cq * Cr + Cq + Cr) *
        ((H : ℝ) ^ δ) ^ 2 * ((B : ℝ) ^ α) ^ 2 := by nlinarith
  have hHsquared : ((H : ℝ) ^ δ) ^ 2 = (H : ℝ) ^ (2 * δ) := by
    rw [pow_two, ← Real.rpow_add hHp]
    congr 1
    ring
  have hBsquared : ((B : ℝ) ^ α) ^ 2 = (B : ℝ) ^ (2 * α) := by
    rw [pow_two, ← Real.rpow_add hBp]
    congr 1
    ring
  dsimp only [quantitativePrefixModulusSensitiveEdgeMajorant]
  calc
    ((PrimeSubsetPrefix.directedEdges P depth).card : ℝ) *
        (((max 1 Δ : ℕ) : ℝ) ^ depth *
          (((d : ℝ) * ((b : ℝ) + 2)) ^ 2 * (H : ℝ) ^ (2 * η) *
            ((Q : ℝ) ^ 2 + (B : ℝ) ^ α * Q * R +
              (B : ℝ) ^ α * Q + ((B : ℝ) ^ α) ^ 2 * R))) ≤
        (H : ℝ) ^ δ *
          (((d : ℝ) * ((b : ℝ) + 2)) ^ 2 * (H : ℝ) ^ (2 * η) *
            ((Cq ^ 2 + Cq * Cr + Cq + Cr) *
              ((H : ℝ) ^ δ) ^ 2 * ((B : ℝ) ^ α) ^ 2)) := by
      rw [← mul_assoc]
      exact mul_le_mul hmass (mul_le_mul_of_nonneg_left hsum (by positivity))
        (by positivity) (by positivity)
    _ = _ := by
      rw [hHsquared, hBsquared]
      rw [show 2 * η + 3 * δ = δ + (2 * η + 2 * δ) by ring,
        Real.rpow_add hHp, Real.rpow_add hHp]
      ring

/-- A fixed dilation between source and displacement height only changes
the constant; the explicit exponent condition gives `B^(1+ε)`. -/
theorem edge_majorant_le_target
    (P : Finset ℕ) (depth Δ d b H B Q R : ℕ)
    (η α δ Cq Cr CH ε : ℝ)
    (hH : (1 : ℝ) ≤ H) (hB : 1 ≤ B)
    (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    (hCq : 0 ≤ Cq) (hCr : 0 ≤ Cr) (hCH : 0 ≤ CH)
    (hheight : (H : ℝ) ≤ CH * (B : ℝ))
    (hmass : ((PrimeSubsetPrefix.directedEdges P depth).card : ℝ) *
      ((max 1 Δ : ℕ) : ℝ) ^ depth ≤ (H : ℝ) ^ δ)
    (hQ : (Q : ℝ) ≤ Cq * (H : ℝ) ^ δ * (B : ℝ) ^ α)
    (hR : (R : ℝ) ≤ Cr * (H : ℝ) ^ δ)
    (hexponent : 2 * η + 3 * δ + 2 * α ≤ 1 + ε) :
    ((PrimeSubsetPrefix.directedEdges P depth).card : ℝ) *
      quantitativePrefixModulusSensitiveEdgeMajorant
        Δ depth d b H B Q R η α ≤
      (((d : ℝ) * ((b : ℝ) + 2)) ^ 2 *
        (Cq ^ 2 + Cq * Cr + Cq + Cr) * CH ^ (2 * η + 3 * δ)) *
        (B : ℝ) ^ (1 + ε) := by
  have hBp : (0 : ℝ) < B := by exact_mod_cast hB
  have hBone : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hscale : (H : ℝ) ^ (2 * η + 3 * δ) ≤
      CH ^ (2 * η + 3 * δ) * (B : ℝ) ^ (2 * η + 3 * δ) := by
    rw [← Real.mul_rpow hCH (by positivity)]
    exact Real.rpow_le_rpow (by positivity) hheight (by positivity)
  have htarget : (H : ℝ) ^ (2 * η + 3 * δ) * (B : ℝ) ^ (2 * α) ≤
      CH ^ (2 * η + 3 * δ) * (B : ℝ) ^ (1 + ε) := by
    calc
      _ ≤ (CH ^ (2 * η + 3 * δ) * (B : ℝ) ^ (2 * η + 3 * δ)) *
          (B : ℝ) ^ (2 * α) := mul_le_mul_of_nonneg_right hscale (by positivity)
      _ = CH ^ (2 * η + 3 * δ) *
          (B : ℝ) ^ (2 * η + 3 * δ + 2 * α) := by rw [Real.rpow_add hBp (2 * η + 3 * δ) (2 * α)]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hBone hexponent) (by positivity)
  have hbase := edge_majorant_le_twoRadius P depth Δ d b H B Q R
    η α δ Cq Cr hH hB hδ hCq hCr hmass hQ hR
  calc
    _ ≤ ((d : ℝ) * ((b : ℝ) + 2)) ^ 2 * (Cq ^ 2 + Cq * Cr + Cq + Cr) *
          ((H : ℝ) ^ (2 * η + 3 * δ) * (B : ℝ) ^ (2 * α)) := by
      simpa only [mul_assoc] using hbase
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left htarget
        (show 0 ≤ ((d : ℝ) * ((b : ℝ) + 2)) ^ 2 *
          (Cq ^ 2 + Cq * Cr + Cq + Cr) by positivity)

/-- For every degree at least four, the finite-field count constant may be
chosen above one while retaining enough exponent slack for both the sharp
edge sum and the nonlinear two-cap residual. -/
theorem exists_exponent_parameters {d : ℕ} (hd : 4 ≤ d)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K α η δ : ℝ,
      1 < K ∧ 0 < α ∧ α < 1 ∧ 0 < η ∧ 0 < δ ∧
      Real.sqrt K / Real.sqrt (d : ℝ) < α ∧
      2 * η + 3 * δ + 2 * α ≤ 1 + ε ∧
      (1 / 2 : ℝ) + α + 6 * η ≤ 1 + ε := by
  let t : ℝ := min ε 1
  have ht : 0 < t := lt_min hε (by norm_num)
  have htε : t ≤ ε := min_le_left _ _
  have ht1 : t ≤ 1 := min_le_right _ _
  let K : ℝ := (1 + t / 16) ^ 2
  let α : ℝ := 1 / 2 + t / 16
  have hK : 1 < K := by dsimp [K]; nlinarith
  have hα : 0 < α := by dsimp [α]; linarith
  have hα1 : α < 1 := by dsimp [α]; linarith
  have hroot : Real.sqrt K = 1 + t / 16 := by
    dsimp [K]
    exact Real.sqrt_sq (by linarith)
  have hdreal : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hdroot : (2 : ℝ) ≤ Real.sqrt (d : ℝ) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (d : ℝ) by positivity), Real.sqrt_nonneg (d : ℝ)]
  have hrange : Real.sqrt K / Real.sqrt (d : ℝ) < α := by
    apply (div_lt_iff₀ (by linarith : 0 < Real.sqrt (d : ℝ))).mpr
    rw [hroot]
    have hmul := mul_le_mul_of_nonneg_left hdroot hα.le
    dsimp [α] at hmul ⊢
    nlinarith
  refine ⟨K, α, t / 64, t / 64, hK, hα, hα1, by positivity, by positivity,
    hrange, ?_, ?_⟩
  · dsimp [α]
    linarith
  · dsimp [α]
    linarith

/-- A fixed upper degree bound fixes the subpower threshold before the
varying equation, even if its actual affine degree drops. -/
theorem directedEdge_degree_mass_le_subpower_of_degree_le
    (P : Finset ℕ) (depth Δ D : ℕ) (M H δ : ℝ)
    (hΔ : Δ ≤ D) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hcard : P.card ≤ reservoirDepth M H)
    (hdepth : depth ≤ reservoirDepth M H)
    (hthreshold : reservoirSubpowerThreshold M
      (4 * ((max 1 D : ℕ) : ℝ)) δ ≤ H) :
    ((PrimeSubsetPrefix.directedEdges P depth).card : ℝ) *
      ((max 1 Δ : ℕ) : ℝ) ^ depth ≤ H ^ δ := by
  have hmax : max 1 Δ ≤ max 1 D := max_le_max (le_refl _) hΔ
  have hp : ((max 1 Δ : ℕ) : ℝ) ^ depth ≤ ((max 1 D : ℕ) : ℝ) ^ depth := by
    exact_mod_cast Nat.pow_le_pow_left hmax depth
  exact (mul_le_mul_of_nonneg_left hp (by positivity)).trans
    (directedEdge_degree_mass_le_subpower P depth D M H δ
      hM hδ hcard hdepth hthreshold)

/-- The actual centered nonlinear residual uses the same natural root and
terminal caps. A chosen common height dominates only the translated box
radius; the theorem needs no bound for its center. -/
theorem centered_residual_le_commonHeight
    (C : ℝ) (d b H B Y m : ℕ) (Rbox η α ε : ℝ)
    (hC : 0 ≤ C) (hη : 0 < η) (hα : 0 ≤ α) (hRbox : 0 ≤ Rbox)
    (hH : (H : ℝ) ≤ (Y : ℝ) + 1)
    (hB : (B : ℝ) ≤ (Y : ℝ) + 1)
    (hbox : 2 * Rbox / (m : ℝ) + 2 ≤ (Y : ℝ) + 1)
    (hexponent : (1 / 2 : ℝ) + α + 6 * η ≤ 1 + ε) :
    quantitativePrefixEffectiveCurveResidualTwoCapCentered C d
      (b + quantitativePrefixUniformBlockDegree H B η α)
      (b + ⌈4 * (H : ℝ) ^ η⌉₊) Rbox m ≤
      C * ((d : ℝ) * ((b : ℝ) + 5)) ^ 5 *
        (η⁻¹ + (d : ℝ) * ((b : ℝ) + 5)) *
        ((Y : ℝ) + 1) ^ (1 + ε) := by
  have hradius : 0 ≤ 2 * Rbox / (m : ℝ) := div_nonneg (by positivity) (by positivity)
  have hsmall : 0 < 2 * Rbox / (m : ℝ) + 2 := by linarith
  have hlog : 0 ≤ Real.log (2 * Rbox / (m : ℝ) + 2) :=
    Real.log_nonneg (by linarith)
  have hmono :
      quantitativePrefixEffectiveCurveResidualTwoCapCentered C d
        (b + quantitativePrefixUniformBlockDegree H B η α)
        (b + ⌈4 * (H : ℝ) ^ η⌉₊) Rbox m ≤
      quantitativePrefixEffectiveCurveResidualTwoCap C d
        (b + quantitativePrefixUniformBlockDegree H B η α)
        (b + ⌈4 * (H : ℝ) ^ η⌉₊) Y := by
    dsimp only [quantitativePrefixEffectiveCurveResidualTwoCapCentered,
      quantitativePrefixEffectiveCurveResidualTwoCap]
    gcongr
  exact hmono.trans
    (quantitativePrefixEffectiveCurveResidualTwoCap_le_target
      C d b H B Y η α ε hC hη hα hH hB hexponent)

end
end CubicTenVariables.FixedLeadingSurfaceSurvivorNumerics
