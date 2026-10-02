import TranslatedDepthSeven.FixedQuotientFivefoldResidueModel

/-!
# Occupied residue classes on the isolated-vertex quotient

This file applies the fixed affine-fivefold model to the literal occupied
residues of a finite set in twelve variables.  The affine homothety is
injective at primes avoiding its scale, and CRT is used coordinatewise.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

set_option maxHeartbeats 800000

/-- Integer reduction in twelve coordinates commutes with the square-free
Chinese-remainder equivalence. -/
theorem quotientCrtVectorEquiv_intCast
    {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime)
    (z : Fin 12 → ℤ) (p : P) :
    crtVectorEquiv (fun p : P ↦ (p : ℕ))
        (primeSubtype_pairwise_coprime hprime) 12
        (fun i ↦ (z i : ZMod (∏ p : P, (p : ℕ)))) p =
      (fun i ↦ (z i : ZMod (p : ℕ))) := by
  funext i
  change ZMod.prodEquivPi (fun p : P ↦ (p : ℕ))
      (primeSubtype_pairwise_coprime hprime)
      (z i : ZMod (∏ p : P, (p : ℕ))) p =
    (z i : ZMod (p : ℕ))
  exact congrFun (map_intCast
    (ZMod.prodEquivPi (fun p : P ↦ (p : ℕ))
      (primeSubtype_pairwise_coprime hprime)).toRingHom (z i)) p

/-- The twelve-coordinate affine homothety commutes with each CRT
component. -/
theorem quotientCrtVectorEquiv_zmodIntegralAffineMap
    {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime)
    (m : ℕ) (x₀ : Fin 12 → ℤ)
    (z : Fin 12 → ZMod (∏ p : P, (p : ℕ))) (p : P) :
    crtVectorEquiv (fun p : P ↦ (p : ℕ))
        (primeSubtype_pairwise_coprime hprime) 12
        (zmodIntegralAffineMap (∏ p : P, (p : ℕ)) m x₀ z) p =
      zmodIntegralAffineMap (p : ℕ) m x₀
        (crtVectorEquiv (fun p : P ↦ (p : ℕ))
          (primeSubtype_pairwise_coprime hprime) 12 z p) := by
  funext i
  change ZMod.prodEquivPi (fun p : P ↦ (p : ℕ))
      (primeSubtype_pairwise_coprime hprime)
      ((x₀ i : ZMod (∏ p : P, (p : ℕ))) +
        (m : ZMod (∏ p : P, (p : ℕ))) * z i) p =
    (x₀ i : ZMod (p : ℕ)) + (m : ZMod (p : ℕ)) *
      ZMod.prodEquivPi (fun p : P ↦ (p : ℕ))
        (primeSubtype_pairwise_coprime hprime) (z i) p
  let φ := (ZMod.prodEquivPi (fun p : P ↦ (p : ℕ))
    (primeSubtype_pairwise_coprime hprime)).toRingHom
  have h := congrFun (map_add φ
    (x₀ i : ZMod (∏ p : P, (p : ℕ)))
    ((m : ZMod (∏ p : P, (p : ℕ))) * z i)) p
  simpa only [map_intCast, map_natCast, map_mul] using h

/-- The affine homothety is injective modulo a square-free prime product
when every selected prime avoids the scale. -/
theorem quotient_zmodIntegralAffineMap_squarefree_injective
    {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime)
    {m : ℕ} (hpm : ∀ p ∈ P, ¬ p ∣ m)
    (x₀ : Fin 12 → ℤ) :
    Function.Injective
      (zmodIntegralAffineMap (∏ p : P, (p : ℕ)) m x₀) := by
  intro z w hzw
  apply (crtVectorEquiv (fun p : P ↦ (p : ℕ))
    (primeSubtype_pairwise_coprime hprime) 12).injective
  funext p
  apply zmodIntegralAffineMap_injective
    (hprime p p.property) (hpm p p.property) x₀
  rw [← quotientCrtVectorEquiv_zmodIntegralAffineMap hprime m x₀ z p,
    ← quotientCrtVectorEquiv_zmodIntegralAffineMap hprime m x₀ w p, hzw]

/-- Reduction of the integral affine point is its reduced affine image. -/
theorem quotient_intCast_integralAffineMap_eq_zmodIntegralAffineMap
    {p m : ℕ} (x₀ z : Fin 12 → ℤ) :
    (fun i ↦ (integralAffineMap x₀ z m i : ZMod p)) =
      zmodIntegralAffineMap p m x₀ (fun i ↦ (z i : ZMod p)) := by
  funext i
  simp [integralAffineMap, zmodIntegralAffineMap]

/-- Affine images of all occupied quotient residues lie in the literal CRT
product of the fixed model's local zero sets. -/
theorem image_quotientOccupiedResidues_subset_fixedModel_crt
    (equations : Finset (MvPolynomial (Fin 12) ℤ))
    (M : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (Z : Finset (Fin 12 → ℤ)) (x₀ : Fin 12 → ℤ) (m : ℕ)
    (hzero : ∀ z ∈ Z, ∀ g ∈ equations,
      MvPolynomial.eval (integralAffineMap x₀ z m) g = 0)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hgoodden : ∀ p ∈ P, ¬ p ∣ M.denominator.natAbs) :
    (occupiedIntegralResidues (∏ p : P, (p : ℕ)) Z).image
        (zmodIntegralAffineMap (∏ p : P, (p : ℕ)) m x₀) ⊆
      crtGlobalResidues (fun p : P ↦ (p : ℕ))
        (primeSubtype_pairwise_coprime hprime)
        (primeSubtype_ne_zero hprime) 12
        (fun p ↦ principalOpenIdealZeroFinset 12 M.denominator (p : ℕ)
          (hprime p p.property) (hgoodden p p.property)
          (finiteNormalizationModelIdeal
            M.equations M.parameters M.relations)) := by
  classical
  intro y hy
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
  rw [mem_crtGlobalResidues_iff]
  intro p
  rw [quotientCrtVectorEquiv_zmodIntegralAffineMap hprime m x₀ u p]
  obtain ⟨z, hz, hzu⟩ := mem_occupiedIntegralResidues_iff.mp hu
  have hcomponent :
      crtVectorEquiv (fun p : P ↦ (p : ℕ))
          (primeSubtype_pairwise_coprime hprime) 12 u p =
        (fun i ↦ (z i : ZMod (p : ℕ))) := by
    rw [← hzu]
    exact quotientCrtVectorEquiv_intCast hprime z p
  rw [hcomponent]
  rw [← quotient_intCast_integralAffineMap_eq_zmodIntegralAffineMap x₀ z]
  exact quotientIntCast_mem_principalOpenModel_of_mem_integralEquationFinset
    equations M (integralAffineMap x₀ z m) (hzero z hz)
      (p : ℕ) (hprime p p.property) (hgoodden p p.property)

/-- Exact occupied-class bound for a prime product in twelve coordinates. -/
theorem card_quotientOccupiedResidues_le_fixedModel_crt
    (equations : Finset (MvPolynomial (Fin 12) ℤ))
    (M : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (Z : Finset (Fin 12 → ℤ)) (x₀ : Fin 12 → ℤ) (m : ℕ)
    (hzero : ∀ z ∈ Z, ∀ g ∈ equations,
      MvPolynomial.eval (integralAffineMap x₀ z m) g = 0)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hgoodm : ∀ p ∈ P, ¬ p ∣ m)
    (hgoodden : ∀ p ∈ P, ¬ p ∣ M.denominator.natAbs) :
    (occupiedIntegralResidues (∏ p : P, (p : ℕ)) Z).card ≤
      M.localConstant ^ P.card * (primeProduct P) ^ 5 := by
  classical
  let q := ∏ p : P, (p : ℕ)
  let Y := occupiedIntegralResidues q Z
  let φ := zmodIntegralAffineMap q m x₀
  let R : ∀ p : P, Finset (Fin 12 → ZMod (p : ℕ)) :=
    fun p ↦ principalOpenIdealZeroFinset 12 M.denominator (p : ℕ)
      (hprime p p.property) (hgoodden p p.property)
      (finiteNormalizationModelIdeal M.equations M.parameters M.relations)
  let G := crtGlobalResidues (fun p : P ↦ (p : ℕ))
    (primeSubtype_pairwise_coprime hprime)
    (primeSubtype_ne_zero hprime) 12 R
  have hφ : Function.Injective φ :=
    quotient_zmodIntegralAffineMap_squarefree_injective hprime hgoodm x₀
  have hsubset : Y.image φ ⊆ G := by
    simpa only [Y, φ, G, R, q] using
      image_quotientOccupiedResidues_subset_fixedModel_crt
        equations M Z x₀ m hzero P hprime hgoodden
  have hYG : Y.card ≤ G.card := by
    calc
      Y.card = (Y.image φ).card :=
        (Finset.card_image_iff.mpr hφ.injOn).symm
      _ ≤ G.card := Finset.card_le_card hsubset
  have hG : G.card ≤
      M.localConstant ^ P.card * (primeProduct P) ^ 5 := by
    simpa only [G, R] using
      card_squarefreePrime_crtGlobalResidues_le
        P hprime 12 5 M.localConstant
          (fun p ↦ principalOpenIdealZeroFinset 12 M.denominator (p : ℕ)
            (hprime p p.property) (hgoodden p p.property)
            (finiteNormalizationModelIdeal
              M.equations M.parameters M.relations))
          (fun p ↦ M.local_bound (p : ℕ) (hprime p p.property)
            (hgoodden p p.property))
  exact hYG.trans hG

/-- Reservoir form: the fixed local factor is absorbed into `H^ε`, leaving
the dimension-five power of the modulus. -/
theorem card_quotientOccupiedResidues_cast_le_rpow_mul
    {M₀ ε H : ℝ} (hM₀ : 0 ≤ M₀) (hε : 0 < ε)
    (equations : Finset (MvPolynomial (Fin 12) ℤ))
    (M : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (Z : Finset (Fin 12 → ℤ)) (x₀ : Fin 12 → ℤ) (m : ℕ)
    (hzero : ∀ z ∈ Z, ∀ g ∈ equations,
      MvPolynomial.eval (integralAffineMap x₀ z m) g = 0)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hgoodm : ∀ p ∈ P, ¬ p ∣ m)
    (hgoodden : ∀ p ∈ P, ¬ p ∣ M.denominator.natAbs)
    (hPcard : P.card ≤ reservoirDepth M₀ H)
    (hH : reservoirSubpowerThreshold M₀ (M.localConstant : ℝ) ε ≤ H) :
    ((occupiedIntegralResidues (∏ p : P, (p : ℕ)) Z).card : ℝ) ≤
      H ^ ε * (primeProduct P : ℝ) ^ 5 := by
  have hfinite := card_quotientOccupiedResidues_le_fixedModel_crt
    equations M Z x₀ m hzero P hprime hgoodm hgoodden
  have hfiniteCast :
      ((occupiedIntegralResidues (∏ p : P, (p : ℕ)) Z).card : ℝ) ≤
        (M.localConstant : ℝ) ^ P.card *
          (primeProduct P : ℝ) ^ 5 := by
    exact_mod_cast hfinite
  have hCpowNat : M.localConstant ^ P.card ≤
      M.localConstant ^ reservoirDepth M₀ H :=
    Nat.pow_le_pow_right M.one_le_localConstant hPcard
  have hCpow : (M.localConstant : ℝ) ^ P.card ≤
      (M.localConstant : ℝ) ^ reservoirDepth M₀ H := by
    exact_mod_cast hCpowNat
  have hsub : (M.localConstant : ℝ) ^ reservoirDepth M₀ H ≤ H ^ ε :=
    reservoirBase_pow_depth_le_rpow hM₀
      (by exact_mod_cast M.one_le_localConstant) hε hH
  exact hfiniteCast.trans
    (mul_le_mul_of_nonneg_right (hCpow.trans hsub) (by positivity))

end

end TranslatedDepthSeven
