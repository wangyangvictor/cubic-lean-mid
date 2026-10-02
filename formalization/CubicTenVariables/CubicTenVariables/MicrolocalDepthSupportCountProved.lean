import CubicTenVariables.MicrolocalDepthSupportCount
import CubicTenVariables.FixedEquationFiniteFieldCount

/-! The actual five microlocal support counts without the bounded-degree
point-count premise. Normalize each of the five fixed integral models;
one exceptional integer and one constant then cover every finite field.
The geometric incidence/model data remain explicit hypotheses. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.MicrolocalDepthSupportCountProved
open MvPolynomial HessianTheorem11
open ProjectiveMicrolocalData ProjectiveMicrolocalDepth ProjectiveMicrolocalModels
open BihomogeneousIncidenceFamily TerminalIntegralClosureModels
open MicrolocalDepthSupportCount (profile)
open scoped BigOperators

private theorem exists_level_bound
    {t : ℕ} {F : MvPolynomial (Fin 10) ℤ} {f : Fin t → Polynomial 10 10}
    {N B : ℕ} (h : Geometry F f) (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (hData : TenMicrolocalIncidence.Conclusion F f N B) (j : Fin 5) :
    ∃ E C : ℕ, 1 ≤ E ∧ 1 ≤ C ∧ ∀ p : ℕ, p.Prime → ¬ p ∣ N → ¬ p ∣ E →
      ∀ (K : Type) [Field K] [Fintype K] [CharP K p],
        Nat.card {v : Fin 10 → K // ((j.val+2 : ℕ) : Dimension) ≤
          IntegralGeometricFiberDepth.geometricFiberDimension f K v} ≤
            C * (Fintype.card K)^(profile j) := by
  obtain ⟨u,G,d,hd,hI,hpts,hgood⟩ := hData.depth_models ⟨j.val+1,by omega⟩
  have hI' : IntegralModelDimension.geometricIdeal G =
      vanishingIdeal GeometricField (depth f (j.val+2)) := by simpa using hI
  have hdim : ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸
      FixedEquationNormalization.equationIdeal G ℚ) ≤ (profile j : Dimension) := by
    change ringKrullDim (_ ⧸ IntegralModelDimension.rationalIdeal G) ≤ _
    rw [ExactRationalConeModel.rational_quotient_dimension_eq G _ hI']
    exact MicrolocalDepthSupportCount.depth_dimension_profile h hhom hAn j
  obtain ⟨E,C,hE,hC,hcount⟩ :=
    FixedEquationFiniteFieldCount.exists_good_characteristic_bound G hdim
  refine ⟨E,C,hE,hC,?_⟩
  intro p hp hpN hpE K _ _ _
  have hc := hcount p hp hpE K
  have heq : {v : Fin 10 → K | ∀ i, eval₂ (Int.castRingHom K) v (G i) = 0} =
      {v | ((j.val+2 : ℕ) : Dimension) ≤
        IntegralGeometricFiberDepth.geometricFiberDimension f K v} := by
    ext v
    simpa using (hgood p hp hpN K).1 v
  change Nat.card ({v : Fin 10 → K | ((j.val+2 : ℕ) : Dimension) ≤
    IntegralGeometricFiberDepth.geometricFiberDimension f K v}) ≤ _
  rw [← heq]
  exact hc

/-- One exceptional integer and one constant precede all five depth levels,
all good primes and every finite extension. No point-count literature input
is required for these actual fixed support loci. -/
theorem exists_uniform_bound
    {t : ℕ} {F : MvPolynomial (Fin 10) ℤ} {f : Fin t → Polynomial 10 10}
    {N B : ℕ} (h : Geometry F f) (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (hData : TenMicrolocalIncidence.Conclusion F f N B) (hN : 1 ≤ N) :
    ∃ D C : ℕ, 1 ≤ D ∧ N ∣ D ∧ 1 ≤ C ∧ ∀ j : Fin 5,
      ∀ p : ℕ, p.Prime → ¬ p ∣ D → ∀ (K : Type) [Field K] [Fintype K] [CharP K p],
        Nat.card {v : Fin 10 → K // ((j.val+2 : ℕ) : Dimension) ≤
          IntegralGeometricFiberDepth.geometricFiberDimension f K v} ≤
            C * (Fintype.card K)^(profile j) := by
  classical
  choose E C hE hC hb using fun j : Fin 5 => exists_level_bound h hhom hAn hData j
  have hsum (j : Fin 5) : C j ≤ ∑ i, C i :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (C i)) (Finset.mem_univ j)
  refine ⟨N * ∏ i, E i,∑ i, C i,?_,dvd_mul_right _ _,(hC 0).trans (hsum 0),?_⟩
  · have hp : 1 ≤ ∏ i, E i := Finset.one_le_prod' (fun i _ => hE i)
    nlinarith
  · intro j p hp hpD K _ _ _
    have hpN : ¬ p ∣ N := fun hdiv => hpD (hdiv.trans (dvd_mul_right _ _))
    have hpE : ¬ p ∣ E j := fun hdiv => hpD
      ((hdiv.trans (Finset.dvd_prod_of_mem E (Finset.mem_univ j))).trans (dvd_mul_left _ _))
    exact (hb j p hp hpN hpE K).trans (Nat.mul_le_mul_right _ (hsum j))

end CubicTenVariables.MicrolocalDepthSupportCountProved
