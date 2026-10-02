import CubicTenVariables.FixedLeadingSurfaceLogarithmicActualSurvivorPackets
import CubicTenVariables.FixedLeadingSurfaceSurvivorDegreeSplitCountInternal
import CubicTenVariables.FixedLeadingSurfaceSurvivorNumerics

/-!
# The actual normalized surface partition through Salberger's degree split

This is the singleton-surface specialization of the persistent-root degree
split.  It consumes the same literal survivor auxiliaries as the normalized
surface proof and replaces the CDHNV terminal-curve estimate by three pieces:

* one multiplicity-free union of degree-one root components;
* the internally proved bounded-degree nonlinear-curve error;
* the uniform high-degree error appearing in Salberger 2023, Theorem 3.16.

The changed-edge cells are bounded here by the already proved
modulus-sensitive estimate.  No terminal curve-count theorem occurs in this
file.
-/

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

namespace CubicTenVariables.FixedLeadingSurfaceLogarithmicActualRootDegreeSplitInternal

open MvPolynomial TranslatedDepthSeven Published
open FixedLeadingSurfaceCoordinateChoice FixedLeadingSurfaceCoordinateTransport
open FixedLeadingSurfacePrimeReservoir
open FixedLeadingSurfaceLogarithmicActualSurvivorPackets
open FixedLeadingSurfaceSingularCount FixedLeadingSurfaceGeometricPrime
open FixedLeadingSurfaceSurvivorNumerics
open FixedLeadingSurfacePersistentRootDegreeSplit
open FixedLeadingSurfaceSurvivorDegreeSplitCountInternal
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The exact normalized survivor estimate obtained from the original
Salberger root-degree split.  The high-degree callback is left as an
implication because its single uniform constant must be chosen before the
varying equation, height, and point set in the eventual outer theorem. -/
theorem exists_uniform_actual_rootDegreeSplit_bound
    (hConjugate :
      StandardAG.QbarConjugatePreservesProjectiveDimensionDegree)
    (cutoff : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Cpila : ℝ, 0 < Cpila ∧
    ∀ (highConstant : ℝ),
    ∀ {d H Q R : ℕ} (hd : 2 ≤ d) (hH : 1 ≤ H)
      (k g : MvPolynomial (Fin 3) ℤ) (c : ℚ),
      IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) k) → c ≠ 0 →
      g.totalDegree ≤ d →
      map (Int.castRingHom ℚ) (homogeneousComponent d g) =
        C c * map (Int.castRingHom ℚ) k →
      ∀ (a b : ℤ) (eta alpha : ℝ), 0 ≤ eta →
      let F := projectiveEquiv a b (homogenize d g)
      ∀ (P : Finset ℕ) (depth : ℕ), (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, ¬ p ∣ 1) →
      (∀ v : PrimeSubsetPrefix.Vertex P depth, v.1.card = depth →
        (H : ℝ) ^ alpha ≤ (PrimeSubsetPrefix.modulus v : ℝ) ∧
          PrimeSubsetPrefix.modulus v ≤ Q) →
      (∀ p ∈ P, p ≤ R) →
      ∀ (X : Finset (Fin 3 → ℤ)), X.Nonempty →
      (∀ z ∈ X, ∀ i, (z i).natAbs ≤ H) →
      (∀ z ∈ X, eval (progressionHomogeneousPoint 0 1 z) F = 0) →
      let allowed := smoothAllowedPrimes P F
      (∀ z ∈ X, depth ≤ (allowed z).card) →
      ∀ (blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ),
      (∀ v, (blockDegree v : ℝ) ≤ 2 * (H : ℝ) ^ eta *
        (1 + (H : ℝ) ^ alpha /
          (PrimeSubsetPrefix.modulus v : ℝ))) →
      ∀ auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
        (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
          MvPolynomial (Fin 4) ℚ,
      (∀ z ∈ X, ∀ v ∈
        PrimeSubsetPrefix.survivingVertices P (allowed z) depth,
          (auxiliary v (integralResidueVector z)).IsHomogeneous
              (d - 1 + blockDegree v) ∧
            auxiliary v (integralResidueVector z) ∉
              Ideal.span {map (Int.castRingHom ℚ) F} ∧
            eval (fun i ↦ (progressionHomogeneousPoint 0 1 z i : ℚ))
              (auxiliary v (integralResidueVector z)) = 0) →
      d - 1 + blockDegree (PrimeSubsetPrefix.root P depth) ≤
        d - 1 + quantitativePrefixUniformBlockDegree H H eta alpha →
      let sourceEquations : Finset (MvPolynomial (Fin 4) ℚ) :=
        {map (Int.castRingHom ℚ) F}
      let root := PrimeSubsetPrefix.root P depth
      ∃ z₀ ∈ X,
      let G₀ := auxiliary root (integralResidueVector z₀)
      let cell := quantitativePrefixPersistentCell sourceEquations auxiliary
        0 1 X allowed
      let active := activeQbarPersistentRootComponentOptions
        sourceEquations G₀ cell
      ∃ degree : Ideal (MvPolynomial (Fin 4) Qbar) → ℕ,
        (∀ QbarIdeal ∈ finiteEquationMinimalPrimes
            (qbarSurfaceCutEquationFamily sourceEquations G₀),
          QbarIdeal.IsPrime ∧
          QbarIdeal.IsHomogeneous (homogeneousSubmodule (Fin 4) Qbar) ∧
          finiteEquationIdeal
              (qbarSurfaceEquationFamily sourceEquations) ≤ QbarIdeal ∧
          HasProjectiveDimensionDegree QbarIdeal 1 (degree QbarIdeal)) ∧
        (∑ QbarIdeal ∈ finiteEquationMinimalPrimes
            (qbarSurfaceCutEquationFamily sourceEquations G₀),
              degree QbarIdeal) ≤
          d * (d - 1 + blockDegree root) ∧
        active.card ≤
          d * (d - 1 + quantitativePrefixUniformBlockDegree H H eta alpha) ∧
        (Salberger2023Theorem316PersistentRootCallback sourceEquations G₀
          cell degree cutoff highConstant epsilon
            ((2 * (H : ℝ) + 2) ^ (3 : ℕ)) →
          (X.card : ℝ) ≤
            (PrimeSubsetPrefix.directedEdges P depth).card *
              quantitativePrefixModulusSensitiveEdgeMajorant
                (surfaceHypersurfaceFirstChartDehomogenize F).totalDegree
                depth d (d - 1) H H Q R eta alpha +
            ((persistentRootLinePointUnion degree active cell).card : ℝ) +
            ∑ o ∈ active,
              persistentRootUniformDegreeSplitError degree cutoff
                ((cutoff : ℝ) ^ 2 +
                  Cpila * (2 * (H : ℝ) + 2) ^
                    ((1 / 2 : ℝ) + epsilon))
                highConstant epsilon
                  ((2 * (H : ℝ) + 2) ^ (3 : ℕ)) o) := by
  classical
  obtain ⟨Cpila, hCpila, hsplit⟩ :=
    exists_uniform_surfaceCount_rootDegreeSplit_uniformHigh_of_survivor_auxiliaries
      hConjugate cutoff epsilon hepsilon
  refine ⟨Cpila, hCpila, ?_⟩
  intro highConstant d H Q R hd hH k g c hirr hc hdegree htop a b eta alpha
    heta
  dsimp only
  let F := projectiveEquiv a b (homogenize d g)
  intro P depth hP hPm hterminal hprimeCap X hX hbox hzero
  let allowed := smoothAllowedPrimes P F
  intro hroom blockDegree hblock auxiliary hauxiliary hrootCap
  let sourceEquations : Finset (MvPolynomial (Fin 4) ℚ) :=
    {map (Int.castRingHom ℚ) F}
  have hI : finiteEquationIdeal sourceEquations =
      Ideal.span {map (Int.castRingHom ℚ) F} := by
    simp [sourceEquations, finiteEquationIdeal]
  obtain ⟨_hne, hFhom, hprime, hdim⟩ := normalized_surface_certificate
    (by omega : 0 < d) a b g hdegree
      (irreducible_actual_top k g c hirr hc htop)
  have hgeometricPrime :=
    geometrically_prime_normalized_surface k g c hirr hc hdegree htop a b
  have hhom : (Ideal.span {map (Int.castRingHom ℚ) F}).IsHomogeneous
      (homogeneousSubmodule (Fin 4) ℚ) := by
    apply Ideal.homogeneous_span
    intro f hf
    obtain rfl := Set.mem_singleton_iff.mp hf
    exact ⟨d, hFhom.map _⟩
  have hallowed : ∀ z ∈ X, allowed z ⊆ P :=
    fun z _ ↦ smoothAllowedPrimes_subset P F z
  have hauxData : ∀ z ∈ X, ∀ v ∈
      PrimeSubsetPrefix.survivingVertices P (allowed z) depth,
      (auxiliary v (integralResidueVector z)).IsHomogeneous
          (d - 1 + blockDegree v) ∧
        auxiliary v (integralResidueVector z) ∉
          finiteEquationIdeal sourceEquations := by
    intro z hz v hv
    rw [hI]
    exact ⟨(hauxiliary z hz v hv).1, (hauxiliary z hz v hv).2.1⟩
  have hauxZero := fun z hz v hv ↦ (hauxiliary z hz v hv).2.2
  have hsource : ∀ z ∈ X,
      (fun i ↦ (progressionHomogeneousPoint 0 1 z i : ℚ)) ∈
        finiteAffineCommonZeroLocus sourceEquations := by
    intro z hz f hf
    obtain rfl := Finset.mem_singleton.mp hf
    rw [eval_map_intCast, hzero z hz, Int.cast_zero]
  have hboxR : ∀ z ∈ X, ∀ i,
      |(integralAffineMap 0 z 1 i : ℝ) - (0 : Fin 3 → ℝ) i| ≤
        (H : ℝ) := by
    intro z hz i
    simp only [integralAffineMap, Pi.zero_apply, Nat.cast_one, one_mul,
      zero_add, sub_zero]
    have hi : ((z i).natAbs : ℤ) ≤ (H : ℤ) := by
      exact_mod_cast hbox z hz i
    rw [Int.natCast_natAbs] at hi
    exact_mod_cast hi
  obtain ⟨z₀, hz₀⟩ := hX
  obtain ⟨degree, hrootData, hrootMass, hactiveCard, hcount⟩ :=
    hsplit highConstant sourceEquations
      (by simpa only [hI] using hprime)
      (by simpa only [hI] using hgeometricPrime)
      (by simpa only [hI] using hhom)
      (by simpa only [hI] using hdim)
      P depth 0 1 (by decide) X allowed blockDegree auxiliary z₀ hz₀
      hallowed hroom hauxData hrootCap hauxZero hsource 0 H
      (by positivity) hboxR
  have hedge := sum_changedEdges_le_modulusSensitive sourceEquations
    (by simpa only [hI] using hgeometricPrime)
    (by simpa only [hI] using hhom)
    (by simpa only [hI] using hdim) F P depth hP 1 (by decide) hPm 0 X
    allowed blockDegree auxiliary (by exact_mod_cast hH) heta hallowed hroom
    (fun _ _ v _ hv ↦ (hterminal v hv).2) hprimeCap hblock hauxData
    hauxZero hsource hzero
    (by
      intro z _ p hp
      simpa only [Pi.zero_apply, Nat.cast_one, one_mul, zero_add] using
        ((mem_smoothAllowedPrimes P F z p).mp hp).2)
  refine ⟨z₀, hz₀, degree, hrootData, hrootMass, hactiveCard, ?_⟩
  intro hHigh
  simp only [Nat.cast_one, div_one] at hcount
  have hc := hcount hHigh
  simpa only [sourceEquations, F, allowed] using
    hc.trans (add_le_add (add_le_add hedge le_rfl) le_rfl)

end CubicTenVariables.FixedLeadingSurfaceLogarithmicActualRootDegreeSplitInternal
