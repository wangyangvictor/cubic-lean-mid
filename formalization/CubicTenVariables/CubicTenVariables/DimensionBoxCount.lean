import CubicTenVariables.IntegerProjectionCount
import TranslatedDepthSeven.HomogeneousLinearNormalizationBoxCount

/-! Literal integer-box counts for any homogeneous rational affine ideal.
The Krull-dimension hypothesis is explicit. No Hessian rank or Davenport
goodness is asserted in this module. The linear normalization and its finite
fiber bounds are proved in the imported development. -/

noncomputable section
namespace CubicTenVariables
open MvPolynomial TranslatedDepthSeven
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A rational point of an affine ideal lies on a minimal-prime component. -/
theorem exists_minimalPrime_through_rational_point {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℚ)) (x : Fin n → ℚ)
    (hx : x ∈ affineIdealZeroLocus I) :
    ∃ P ∈ finiteMinimalPrimes I, x ∈ affineIdealZeroLocus P := by
  have hker := (mem_affineIdealZeroLocus_iff_le_ker_aeval I x).mp hx
  obtain ⟨P, hP, hPx⟩ := exists_finiteMinimalPrime_le hker
  exact ⟨P, hP, (mem_affineIdealZeroLocus_iff_le_ker_aeval P x).mpr hPx⟩

/-- Increasing the ideal cannot increase quotient Krull dimension. -/
theorem quotient_dimension_mono {R : Type*} [CommRing R]
    {I J : Ideal R} (hIJ : I ≤ J) :
    ringKrullDim (R ⧸ J) ≤ ringKrullDim (R ⧸ I) := by
  exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hIJ)
    (Ideal.Quotient.factor_surjective hIJ)

/-- A prime homogeneous ideal of dimension at most `r` has at most
`K * B^r` integral points in every radius-`B` box, for some fixed `K`. -/
theorem prime_homogeneous_box_count {n r : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℚ)) (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin n) ℚ))
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℚ ⧸ I) ≤ r) :
    ∃ K : ℕ, ∀ (S : Finset (Fin n → ℤ)) (B : ℕ), 1 ≤ B →
      S ⊆ integerBox n B →
      (∀ x ∈ S, (fun i ↦ (x i : ℚ)) ∈ affineIdealZeroLocus I) →
      S.card ≤ K * B ^ r := by
  letI : I.IsPrime := hprime
  obtain ⟨D⟩ := exists_homogeneousLinearNormalizationData n I hprime hhom
  have hdimlt : ringKrullDim (MvPolynomial (Fin n) ℚ ⧸ I) < (r + 1 : ℕ) :=
    lt_of_le_of_lt hdim (by exact_mod_cast Nat.lt_succ_self r)
  have hparamlt := normalization_parameter_lt_of_ringKrullDim_lt_nat
    D.hom D.hom_injective D.hom_finite.to_isIntegral hdimlt
  have hparam : D.parameterCount ≤ r := by omega
  obtain ⟨K, hK⟩ := exists_card_le_mul_power_of_parameterCount_le D hparam
  refine ⟨K, ?_⟩
  intro S B hB hS hz
  have hbox : ∀ x ∈ S, ∀ i, (x i).natAbs ≤ B := by
    intro x hx i
    have hi := (mem_integerBox.mp (hS hx)) i
    have hi' : ((x i).natAbs : ℤ) ≤ (B : ℤ) := by
      simpa only [Int.natCast_natAbs] using hi
    exact_mod_cast hi'
  apply hK S 0 1 B (by norm_num) hB hbox
  simpa [integralAffineMap] using hz

/-- The component count summed over the actual finite minimal primes.
This includes the empty locus and ideals which are not radical. -/
theorem homogeneous_box_count {n r : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℚ))
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin n) ℚ))
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℚ ⧸ I) ≤ r) :
    ∃ K : ℕ, ∀ (S : Finset (Fin n → ℤ)) (B : ℕ), 1 ≤ B →
      S ⊆ integerBox n B →
      (∀ x ∈ S, (fun i ↦ (x i : ℚ)) ∈ affineIdealZeroLocus I) →
      S.card ≤ K * B ^ r := by
  classical
  let components := finiteMinimalPrimes I
  let Component := {P : Ideal (MvPolynomial (Fin n) ℚ) // P ∈ components}
  have heach : ∀ P : Component, ∃ K : ℕ,
      ∀ (S : Finset (Fin n → ℤ)) (B : ℕ), 1 ≤ B →
      S ⊆ integerBox n B →
      (∀ x ∈ S, (fun i ↦ (x i : ℚ)) ∈ affineIdealZeroLocus P.1) →
      S.card ≤ K * B ^ r := by
    intro P
    have hP := (mem_finiteMinimalPrimes_iff I P.1).mp P.2
    exact prime_homogeneous_box_count P.1
      (isPrime_of_mem_finiteMinimalPrimes P.2)
      (isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous hhom hP)
      ((quotient_dimension_mono hP.1.2).trans hdim)
  choose constant hconstant using heach
  let K : Ideal (MvPolynomial (Fin n) ℚ) → ℕ :=
    fun P ↦ if hP : P ∈ components then constant ⟨P, hP⟩ else 0
  refine ⟨∑ P ∈ components, K P, ?_⟩
  intro S B hB hS hz
  let points : Ideal (MvPolynomial (Fin n) ℚ) → Finset (Fin n → ℤ) :=
    fun P ↦ S.filter fun x ↦ (fun i ↦ (x i : ℚ)) ∈ affineIdealZeroLocus P
  have hcover : S ⊆ components.biUnion points := by
    intro x hx
    obtain ⟨P, hP, hp⟩ := exists_minimalPrime_through_rational_point I _ (hz x hx)
    exact Finset.mem_biUnion.mpr ⟨P, hP, Finset.mem_filter.mpr ⟨hx, hp⟩⟩
  have hbound : ∀ P ∈ components, (points P).card ≤ K P * B ^ r := by
    intro P hP
    have hp := hconstant ⟨P, hP⟩ (points P) B hB
      (fun _ hx ↦ hS (Finset.mem_filter.mp hx).1)
      (fun _ hx ↦ (Finset.mem_filter.mp hx).2)
    simpa [K, hP] using hp
  calc
    S.card ≤ (components.biUnion points).card := Finset.card_le_card hcover
    _ ≤ ∑ P ∈ components, (points P).card := Finset.card_biUnion_le
    _ ≤ ∑ P ∈ components, K P * B ^ r := Finset.sum_le_sum hbound
    _ = (∑ P ∈ components, K P) * B ^ r := (Finset.sum_mul ..).symm

end CubicTenVariables
