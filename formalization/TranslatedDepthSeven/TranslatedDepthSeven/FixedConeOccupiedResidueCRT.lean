import TranslatedDepthSeven.FixedConeResidueBridge
import TranslatedDepthSeven.AffineIntegralPointTransport

/-!
# Occupied square-free residue classes on the fixed cone

This file applies the fixed principal-open model to the residue classes
actually occupied by a finite set of normalized integral vectors.  The
affine substitution `x = x₀ + m z` is injective at every selected prime
which does not divide `m`.  Coordinatewise Chinese remaindering therefore
embeds the occupied normalized residue classes into the product of the
fixed model's local zero sets.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

set_option maxHeartbeats 800000

/-- The literal set of residue vectors modulo `q` occupied by a finite set
of integral vectors. -/
def occupiedIntegralResidues {N : ℕ} (q : ℕ)
    (Z : Finset (Fin N → ℤ)) : Finset (Fin N → ZMod q) :=
  Z.image fun z i ↦ (z i : ZMod q)

@[simp]
theorem mem_occupiedIntegralResidues_iff {N q : ℕ}
    {Z : Finset (Fin N → ℤ)} {y : Fin N → ZMod q} :
    y ∈ occupiedIntegralResidues q Z ↔
      ∃ z ∈ Z, (fun i ↦ (z i : ZMod q)) = y := by
  classical
  simp [occupiedIntegralResidues]

/-- Cardinalities of occupied residue sets transport across an equality of
moduli, without exposing dependent casts between the two `ZMod` types. -/
theorem card_occupiedIntegralResidues_congr_modulus
    {N q r : ℕ} (hqr : q = r) (Z : Finset (Fin N → ℤ)) :
    (occupiedIntegralResidues q Z).card =
      (occupiedIntegralResidues r Z).card := by
  subst r
  rfl

/-- Integer reduction commutes with every coordinate of the square-free
Chinese-remainder equivalence. -/
theorem crtVectorEquiv_intCast
    {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime)
    (z : Fin 13 → ℤ) (p : P) :
    crtVectorEquiv (fun p : P ↦ (p : ℕ))
        (primeSubtype_pairwise_coprime hprime) 13
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

/-- The affine substitution modulo the product commutes with every CRT
component. -/
theorem crtVectorEquiv_zmodIntegralAffineMap
    {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime)
    (m : ℕ) (x₀ : Fin 13 → ℤ)
    (z : Fin 13 → ZMod (∏ p : P, (p : ℕ))) (p : P) :
    crtVectorEquiv (fun p : P ↦ (p : ℕ))
        (primeSubtype_pairwise_coprime hprime) 13
        (zmodIntegralAffineMap (∏ p : P, (p : ℕ)) m x₀ z) p =
      zmodIntegralAffineMap (p : ℕ) m x₀
        (crtVectorEquiv (fun p : P ↦ (p : ℕ))
          (primeSubtype_pairwise_coprime hprime) 13 z p) := by
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

/-- If every selected prime avoids `m`, the affine substitution is
injective modulo their square-free product. -/
theorem zmodIntegralAffineMap_squarefree_injective
    {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime)
    {m : ℕ} (hpm : ∀ p ∈ P, ¬ p ∣ m)
    (x₀ : Fin 13 → ℤ) :
    Function.Injective
      (zmodIntegralAffineMap (∏ p : P, (p : ℕ)) m x₀) := by
  intro z w hzw
  apply (crtVectorEquiv (fun p : P ↦ (p : ℕ))
    (primeSubtype_pairwise_coprime hprime) 13).injective
  funext p
  apply zmodIntegralAffineMap_injective
    (hprime p p.property) (hpm p p.property) x₀
  rw [← crtVectorEquiv_zmodIntegralAffineMap hprime m x₀ z p,
    ← crtVectorEquiv_zmodIntegralAffineMap hprime m x₀ w p, hzw]

/-- Reduction of the integral affine point is the corresponding affine map
of the reduced normalized vector. -/
theorem intCast_integralAffineMap_eq_zmodIntegralAffineMap
    {p m : ℕ} (x₀ z : Fin 13 → ℤ) :
    (fun i ↦ (integralAffineMap x₀ z m i : ZMod p)) =
      zmodIntegralAffineMap p m x₀ (fun i ↦ (z i : ZMod p)) := by
  funext i
  simp [integralAffineMap, zmodIntegralAffineMap]

/-- The affine images of all occupied normalized residue classes lie in the
literal CRT product of the fixed model's local zero sets. -/
theorem image_occupiedIntegralResidues_subset_fixedModel_crt
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (M : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (Z : Finset (Fin 13 → ℤ)) (x₀ : Fin 13 → ℤ) (m : ℕ)
    (hzero : ∀ z ∈ Z, ∀ g ∈ equations,
      MvPolynomial.eval (integralAffineMap x₀ z m) g = 0)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hgoodden : ∀ p ∈ P, ¬ p ∣ M.denominator.natAbs) :
    (occupiedIntegralResidues (∏ p : P, (p : ℕ)) Z).image
        (zmodIntegralAffineMap (∏ p : P, (p : ℕ)) m x₀) ⊆
      crtGlobalResidues (fun p : P ↦ (p : ℕ))
        (primeSubtype_pairwise_coprime hprime)
        (primeSubtype_ne_zero hprime) 13
        (fun p ↦ principalOpenIdealZeroFinset 13 M.denominator (p : ℕ)
          (hprime p p.property) (hgoodden p p.property)
          (finiteNormalizationModelIdeal
            M.equations M.parameters M.relations)) := by
  classical
  intro y hy
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
  rw [mem_crtGlobalResidues_iff]
  intro p
  rw [crtVectorEquiv_zmodIntegralAffineMap hprime m x₀ u p]
  obtain ⟨z, hz, hzu⟩ := mem_occupiedIntegralResidues_iff.mp hu
  have hcomponent :
      crtVectorEquiv (fun p : P ↦ (p : ℕ))
          (primeSubtype_pairwise_coprime hprime) 13 u p =
        (fun i ↦ (z i : ZMod (p : ℕ))) := by
    rw [← hzu]
    exact crtVectorEquiv_intCast hprime z p
  rw [hcomponent]
  rw [← intCast_integralAffineMap_eq_zmodIntegralAffineMap x₀ z]
  exact intCast_mem_principalOpenModel_of_mem_integralEquationFinset
    equations M (integralAffineMap x₀ z m) (hzero z hz)
      (p : ℕ) (hprime p p.property) (hgoodden p p.property)

/-- Exact occupied-class bound.  No special-fibre closure is counted: only
reductions of the displayed integral affine images enter the argument. -/
theorem card_occupiedIntegralResidues_le_fixedModel_crt
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (M : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (Z : Finset (Fin 13 → ℤ)) (x₀ : Fin 13 → ℤ) (m : ℕ)
    (hzero : ∀ z ∈ Z, ∀ g ∈ equations,
      MvPolynomial.eval (integralAffineMap x₀ z m) g = 0)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hgoodm : ∀ p ∈ P, ¬ p ∣ m)
    (hgoodden : ∀ p ∈ P, ¬ p ∣ M.denominator.natAbs) :
    (occupiedIntegralResidues (∏ p : P, (p : ℕ)) Z).card ≤
      M.localConstant ^ P.card * (primeProduct P) ^ 6 := by
  classical
  let q := ∏ p : P, (p : ℕ)
  let Y := occupiedIntegralResidues q Z
  let φ := zmodIntegralAffineMap q m x₀
  let R : ∀ p : P, Finset (Fin 13 → ZMod (p : ℕ)) :=
    fun p ↦ principalOpenIdealZeroFinset 13 M.denominator (p : ℕ)
      (hprime p p.property) (hgoodden p p.property)
      (finiteNormalizationModelIdeal M.equations M.parameters M.relations)
  let G := crtGlobalResidues (fun p : P ↦ (p : ℕ))
    (primeSubtype_pairwise_coprime hprime)
    (primeSubtype_ne_zero hprime) 13 R
  have hφ : Function.Injective φ :=
    zmodIntegralAffineMap_squarefree_injective hprime hgoodm x₀
  have hsubset : Y.image φ ⊆ G := by
    simpa only [Y, φ, G, R, q] using
      image_occupiedIntegralResidues_subset_fixedModel_crt
        equations M Z x₀ m hzero P hprime hgoodden
  have hYG : Y.card ≤ G.card := by
    calc
      Y.card = (Y.image φ).card :=
        (Finset.card_image_iff.mpr hφ.injOn).symm
      _ ≤ G.card := Finset.card_le_card hsubset
  have hG : G.card ≤
      M.localConstant ^ P.card * (primeProduct P) ^ 6 := by
    simpa only [G, R] using
      card_fixedPrincipalOpenModel_crt_le
        M.equations M.parameters M.relations M.localConstant
        P hprime hgoodden (fun p ↦
          M.local_bound (p : ℕ) (hprime p p.property)
            (hgoodden p p.property))
  exact hYG.trans hG

/-- The exact occupied-class estimate on the manuscript's literal modulus
`primeProduct P`. -/
theorem card_occupiedIntegralResidues_primeProduct_le_fixedModel_crt
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (M : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (Z : Finset (Fin 13 → ℤ)) (x₀ : Fin 13 → ℤ) (m : ℕ)
    (hzero : ∀ z ∈ Z, ∀ g ∈ equations,
      MvPolynomial.eval (integralAffineMap x₀ z m) g = 0)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hgoodm : ∀ p ∈ P, ¬ p ∣ m)
    (hgoodden : ∀ p ∈ P, ¬ p ∣ M.denominator.natAbs) :
    (occupiedIntegralResidues (primeProduct P) Z).card ≤
      M.localConstant ^ P.card * (primeProduct P) ^ 6 := by
  calc
    (occupiedIntegralResidues (primeProduct P) Z).card =
        (occupiedIntegralResidues (∏ p : P, (p : ℕ)) Z).card :=
      card_occupiedIntegralResidues_congr_modulus
        (primeSubtype_prod_eq_primeProduct P).symm Z
    _ ≤ M.localConstant ^ P.card * (primeProduct P) ^ 6 :=
      card_occupiedIntegralResidues_le_fixedModel_crt
        equations M Z x₀ m hzero P hprime hgoodm hgoodden

/-- Reservoir form of the occupied-class estimate, with the fixed local
normalization constant absorbed into `H^ε`. -/
theorem card_occupiedIntegralResidues_cast_le_rpow_mul
    {M₀ ε H : ℝ} (hM₀ : 0 ≤ M₀) (hε : 0 < ε)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (M : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (Z : Finset (Fin 13 → ℤ)) (x₀ : Fin 13 → ℤ) (m : ℕ)
    (hzero : ∀ z ∈ Z, ∀ g ∈ equations,
      MvPolynomial.eval (integralAffineMap x₀ z m) g = 0)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hgoodm : ∀ p ∈ P, ¬ p ∣ m)
    (hgoodden : ∀ p ∈ P, ¬ p ∣ M.denominator.natAbs)
    (hPcard : P.card ≤ reservoirDepth M₀ H)
    (hH : reservoirSubpowerThreshold M₀ (M.localConstant : ℝ) ε ≤ H) :
    ((occupiedIntegralResidues (∏ p : P, (p : ℕ)) Z).card : ℝ) ≤
      H ^ ε * (primeProduct P : ℝ) ^ 6 := by
  have hfinite := card_occupiedIntegralResidues_le_fixedModel_crt
    equations M Z x₀ m hzero P hprime hgoodm hgoodden
  have hfiniteCast :
      ((occupiedIntegralResidues (∏ p : P, (p : ℕ)) Z).card : ℝ) ≤
        (M.localConstant : ℝ) ^ P.card *
          (primeProduct P : ℝ) ^ 6 := by
    exact_mod_cast hfinite
  have hCpowNat :
      M.localConstant ^ P.card ≤
        M.localConstant ^ reservoirDepth M₀ H :=
    Nat.pow_le_pow_right M.one_le_localConstant hPcard
  have hCpow :
      (M.localConstant : ℝ) ^ P.card ≤
        (M.localConstant : ℝ) ^ reservoirDepth M₀ H := by
    exact_mod_cast hCpowNat
  have hsub :
      (M.localConstant : ℝ) ^ reservoirDepth M₀ H ≤ H ^ ε :=
    reservoirBase_pow_depth_le_rpow hM₀
      (by exact_mod_cast M.one_le_localConstant) hε hH
  exact hfiniteCast.trans
    (mul_le_mul_of_nonneg_right (hCpow.trans hsub) (by positivity))

/-- Reservoir form on the literal square-free modulus `primeProduct P`. -/
theorem card_occupiedIntegralResidues_primeProduct_cast_le_rpow_mul
    {M₀ ε H : ℝ} (hM₀ : 0 ≤ M₀) (hε : 0 < ε)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (M : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (Z : Finset (Fin 13 → ℤ)) (x₀ : Fin 13 → ℤ) (m : ℕ)
    (hzero : ∀ z ∈ Z, ∀ g ∈ equations,
      MvPolynomial.eval (integralAffineMap x₀ z m) g = 0)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hgoodm : ∀ p ∈ P, ¬ p ∣ m)
    (hgoodden : ∀ p ∈ P, ¬ p ∣ M.denominator.natAbs)
    (hPcard : P.card ≤ reservoirDepth M₀ H)
    (hH : reservoirSubpowerThreshold M₀ (M.localConstant : ℝ) ε ≤ H) :
    ((occupiedIntegralResidues (primeProduct P) Z).card : ℝ) ≤
      H ^ ε * (primeProduct P : ℝ) ^ 6 := by
  rw [card_occupiedIntegralResidues_congr_modulus
    (primeSubtype_prod_eq_primeProduct P).symm Z]
  exact card_occupiedIntegralResidues_cast_le_rpow_mul
    hM₀ hε equations M Z x₀ m hzero P hprime hgoodm hgoodden
      hPcard hH

end

end TranslatedDepthSeven
