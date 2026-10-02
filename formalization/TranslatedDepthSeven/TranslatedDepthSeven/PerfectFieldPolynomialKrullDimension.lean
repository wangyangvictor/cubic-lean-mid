import TranslatedDepthSeven.FieldPolynomialKrullDimension

/-!
# Krull dimension of a polynomial algebra over a perfect field

The characteristic-zero argument in `FieldPolynomialKrullDimension` uses
only that finite residue-field extensions are separable.  This file records
the exact perfect-field generalization.  In particular it applies to every
finite field.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct
open KaehlerDifferential IsLocalRing

universe u

/-- Every maximal ideal of a polynomial algebra over a perfect field has
height at most the number of variables. -/
theorem mvPolynomial_maximal_height_le_of_perfectField
    (k : Type u) [Field k] [PerfectField k] (n : ℕ)
    (m : Ideal (MvPolynomial (Fin n) k)) [m.IsMaximal] :
    m.height ≤ (n : ℕ∞) := by
  let R := MvPolynomial (Fin n) k
  let S := Localization.AtPrime m
  let L := ResidueField S
  letI : Module.Finite k L :=
    mvPolynomial_maximal_residueField_finite k n m
  letI : Algebra.IsIntegral k L := Algebra.IsIntegral.of_finite k L
  letI : Algebra.IsSeparable k L := by infer_instance
  letI : Algebra.FormallyEtale k L :=
    Algebra.FormallyEtale.of_isSeparable k L
  letI : Algebra.FormallySmooth R S :=
    Algebra.FormallySmooth.of_isLocalization m.primeCompl
  letI : Algebra.FormallySmooth k S :=
    Algebra.FormallySmooth.comp k R S
  let bS : Module.Basis (Fin n) S Ω[S⁄k] :=
    mvPolynomialAtPrimeKaehlerBasis k n m
  let bL : Module.Basis (Fin n) L (L ⊗[S] Ω[S⁄k]) := bS.baseChange L
  have hfinrank : Module.finrank L (L ⊗[S] Ω[S⁄k]) = n := by
    rw [Module.finrank_eq_card_basis bL, Fintype.card_fin]
  have hdim : ringKrullDim S ≤ (n : WithBot ℕ∞) := by
    have h := ringKrullDim_le_finrank_residualKaehler (R := S) k
    rw [hfinrank] at h
    exact h
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m S] at hdim
  exact WithBot.coe_le_coe.mp hdim

/-- A polynomial algebra in `n` variables over a perfect field has Krull
dimension exactly `n`. -/
theorem ringKrullDim_mvPolynomial_fin_eq_of_perfectField
    (k : Type u) [Field k] [PerfectField k] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) k) = (n : WithBot ℕ∞) := by
  apply le_antisymm
  · rw [ringKrullDim_le_iff_isMaximal_height_le]
    intro m hm
    letI : m.IsMaximal := hm
    exact_mod_cast mvPolynomial_maximal_height_le_of_perfectField k n m
  · have h := ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial
        (R := k) (Fin n)
    simpa only [ringKrullDim_eq_zero_of_field, zero_add, Nat.card_fin] using h

end

end TranslatedDepthSeven
