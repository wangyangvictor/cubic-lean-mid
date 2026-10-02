import TranslatedDepthSeven.QuantitativeSurfaceResidueAuxiliaryChoice
import TranslatedDepthSeven.PrimeSubsetPrefixReservoirBridge
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Quantitative auxiliaries on every prime-prefix vertex

One exceptional integer contains the affine scale and the full prime pool.
Consequently every prefix modulus satisfies the packet hypotheses.  Applying
the residue-choice theorem at every finite prefix gives a coherent dependent
family of residue-indexed auxiliaries, with one common degree at each vertex.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

/-- Every prefix of a finite prime pool receives an actual residue-dependent
auxiliary family.  The root modulus is one; deeper degrees retain their
individual sharp inverse-modulus bounds. -/
theorem exists_fixedSurface_quantitative_prefixAuxiliaryChoice
    {d : ℕ} (hd : 0 < d)
    (I : Ideal (MvPolynomial (Fin 4) ℚ))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ ℚ))
    (hX : MvPolynomial.X 0 ∉ I)
    (hdegree : HasProjectiveDimensionDegree I 2 d)
    (F : MvPolynomial (Fin 4) ℤ)
    (K : ℝ) (hK : 1 ≤ K) (Aex : ℕ)
    (η a : ℝ) (hη : 0 < η)
    (ha : Real.sqrt K / Real.sqrt (d : ℝ) < a) :
    ∃ b D A H₀ : ℕ, ∃ C : ℝ,
      1 ≤ D ∧ 2 ≤ A ∧ 2 ≤ H₀ ∧ 0 ≤ C ∧
      ∀ (P : Finset ℕ) (depth H B m Dex : ℕ)
        (u : Fin 3 → ℤ) (X : Finset (Fin 3 → ℤ)),
      (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, ¬ p ∣ m) →
      H₀ ≤ H → 1 ≤ B →
      0 < Dex → Dex ≤ H ^ Aex → m * primeProduct P ∣ Dex →
      m ≠ 0 →
      (∀ p, p.Prime → ¬ p ∣ Dex →
        (Nat.card (SurfaceReductionZeroPoint p
          (surfaceHypersurfaceFirstChartDehomogenize F)) : ℝ) ≤
            K * (p : ℝ) ^ 2) →
      (∀ z ∈ X, ∀ i,
        (progressionHomogeneousPoint u m z i).natAbs ≤ H) →
      (∀ z ∈ X, ∀ i, (z i).natAbs ≤ B) →
      (∀ z ∈ X,
        MvPolynomial.eval (progressionHomogeneousPoint u m z) F = 0) →
      (∀ z ∈ X, ∃ v, MvPolynomial.eval (fun i => u i + (m : ℤ) * z i)
        (MvPolynomial.pderiv v
          (surfaceHypersurfaceFirstChartDehomogenize F)) ≠ 0) →
      (∀ z ∈ X, ∀ p ∈ P, ∃ v,
        (MvPolynomial.eval (fun i => u i + (m : ℤ) * z i)
          (MvPolynomial.pderiv v
            (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0) →
      ∃ blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ,
        ∃ auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
          (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
            MvPolynomial (Fin 4) ℚ,
        ∀ v : PrimeSubsetPrefix.Vertex P depth,
          0 < blockDegree v ∧
          ((blockDegree v : ℕ) : ℝ) ≤ 2 * (H : ℝ) ^ η *
            (1 + (B : ℝ) ^ a /
              (PrimeSubsetPrefix.modulus v : ℝ)) ∧
          (∀ ρ ∈ occupiedIntegralResidues (PrimeSubsetPrefix.modulus v) X,
            (auxiliary v ρ).IsHomogeneous (b + blockDegree v) ∧
              auxiliary v ρ ∉ I) ∧
          ∀ z ∈ X, MvPolynomial.eval
            (fun i => (progressionHomogeneousPoint u m z i : ℚ))
              (auxiliary v (integralResidueVector z)) = 0 := by
  classical
  obtain ⟨b, D, A, H₀, C, hD, hA, hH₀, hC, hchoice⟩ :=
    exists_fixedSurface_quantitative_residueAuxiliaryChoice
      hd I hprime hhom hX hdegree F K hK Aex η a hη ha
  refine ⟨b, D, A, H₀, C, hD, hA, hH₀, hC, ?_⟩
  intro P depth H B m Dex u X hP hPm hH hB hDex hDexHeight hmPDex hm
    hpoints hsource hdisplacement hzero hgrad hsmooth
  have hv : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      ∃ k : ℕ, 0 < k ∧
        (k : ℝ) ≤ 2 * (H : ℝ) ^ η *
          (1 + (B : ℝ) ^ a / (PrimeSubsetPrefix.modulus v : ℝ)) ∧
        ∃ auxiliary : (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
            MvPolynomial (Fin 4) ℚ,
          (∀ ρ ∈ occupiedIntegralResidues (PrimeSubsetPrefix.modulus v) X,
            (auxiliary ρ).IsHomogeneous (b + k) ∧ auxiliary ρ ∉ I) ∧
          ∀ z ∈ X, MvPolynomial.eval
            (fun i => (progressionHomogeneousPoint u m z i : ℚ))
              (auxiliary (integralResidueVector z)) = 0 := by
    intro v
    have hvP : v.1 ⊆ P := (PrimeSubsetPrefix.mem_vertices.mp v.2).1
    have hvPrime : ∀ p ∈ v.1, p.Prime := fun p hp => hP p (hvP hp)
    have hq : 0 < PrimeSubsetPrefix.modulus v :=
      Nat.pos_of_ne_zero (primeProduct_ne_zero hvPrime)
    have hsq : Squarefree (PrimeSubsetPrefix.modulus v) :=
      primeProduct_squarefree hvPrime
    have hqm : Nat.Coprime (PrimeSubsetPrefix.modulus v) m := by
      rw [PrimeSubsetPrefix.modulus, primeProduct,
        Nat.coprime_prod_left_iff]
      intro p hp
      exact (hvPrime p hp).coprime_iff_not_dvd.mpr (hPm p (hvP hp))
    have hqP : PrimeSubsetPrefix.modulus v ∣ primeProduct P := by
      exact Finset.prod_dvd_prod_of_subset v.1 P id hvP
    have hmqDex : m * PrimeSubsetPrefix.modulus v ∣ Dex :=
      (Nat.mul_dvd_mul_left m hqP).trans hmPDex
    have hsmoothv : ∀ z ∈ X, ∀ p, p.Prime →
        p ∣ PrimeSubsetPrefix.modulus v → ∃ w,
          (MvPolynomial.eval (fun i => u i + (m : ℤ) * z i)
            (MvPolynomial.pderiv w
              (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0 := by
      intro z hz p hp hpq
      have hpv : p ∈ v.1 := by
        rw [← primeFactors_primeProduct hvPrime]
        exact Nat.mem_primeFactors.mpr
          ⟨hp, hpq, primeProduct_ne_zero hvPrime⟩
      exact hsmooth z hz p (hvP hpv)
    exact hchoice H B (PrimeSubsetPrefix.modulus v) m Dex u X hH hB
      hDex hDexHeight hmqDex hm hq hsq hqm hpoints hsource
      hdisplacement hzero hgrad hsmoothv
  choose blockDegree hblockPos hblockBound auxiliary hauxiliary hauxZero using hv
  exact ⟨blockDegree, auxiliary, fun v =>
    ⟨hblockPos v, hblockBound v, hauxiliary v, hauxZero v⟩⟩

end
end TranslatedDepthSeven
