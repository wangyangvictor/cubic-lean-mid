import TranslatedDepthSeven.FixedConeOccupiedResidueCRT

/-!
# A fixed residue model for the isolated-vertex quotient

The isolated-vertex quotient has twelve affine coordinates and affine
dimension five.  This file is the twelve-coordinate analogue of the fixed
cone model: a homogeneous linear normalization over one principal open gives
`O(p^5)` points at every remaining prime, and exact Chinese remaindering gives
`O(q^5)` occupied residue classes.

Only finite-field residue classes are counted here.  No component count and
no rational or integral point-count theorem enters.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct
open MvPolynomial Polynomial

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

/-- A homogeneous prime ideal in twelve variables whose projectivization has
dimension four admits a homogeneous linear normalization with at most five
parameters. -/
theorem exists_homogeneousLinearNormalizationData_parameterCount_le_five
    (I : Ideal (MvPolynomial (Fin 12) ℚ)) (degree : ℕ)
    (hI : Published.IsIntegralProjectiveVariety (N := 11) I 4 degree) :
    ∃ D : HomogeneousLinearNormalizationData I,
      D.parameterCount ≤ 5 := by
  rcases hI with ⟨hhom, _hsaturated, hprime, hdimdegree⟩
  obtain ⟨D⟩ := exists_homogeneousLinearNormalizationData 12 I hprime hhom
  refine ⟨D, ?_⟩
  have hdim : ringKrullDim (MvPolynomial (Fin 12) ℚ ⧸ I) = 5 := by
    simpa using hdimdegree.1
  exact normalization_parameter_le_of_ringKrullDim_eq
    D.hom D.hom_injective D.hom_finite.to_isIntegral hdim

/-- The twelve coordinate classes satisfy monic equations over a finite
homogeneous linear normalization. -/
theorem exists_monic_relations_for_quotientNormalizationData
    (I : Ideal (MvPolynomial (Fin 12) ℚ))
    (D : HomogeneousLinearNormalizationData I) :
    ∃ p : Fin 12 → (MvPolynomial (Fin D.parameterCount) ℚ)[X],
      (∀ i, (p i).Monic) ∧
      ∀ i, normalizationCoordinateRelation D.forms p i ∈ I := by
  let B := MvPolynomial (Fin D.parameterCount) ℚ
  let A := MvPolynomial (Fin 12) ℚ ⧸ I
  let g : B →ₐ[ℚ] A := D.hom
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : Module.Finite B A := D.hom_finite
  letI : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  have hcoordinate : ∀ i : Fin 12,
      IsIntegral B (Ideal.Quotient.mk I (MvPolynomial.X i)) := by
    intro i
    exact Algebra.IsIntegral.isIntegral
      (Ideal.Quotient.mk I (MvPolynomial.X i))
  choose p hpmonic hpzero using hcoordinate
  refine ⟨p, hpmonic, ?_⟩
  intro i
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hmap :
      Ideal.Quotient.mk I (normalizationCoordinateRelation D.forms p i) =
        (p i).eval₂ g.toRingHom
          (Ideal.Quotient.mk I (MvPolynomial.X i)) := by
    simpa only [normalizationCoordinateRelation,
      HomogeneousLinearNormalizationData.hom, g,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_comp, RingHom.coe_comp,
      Function.comp_apply] using
      (Polynomial.hom_eval₂ (p i) (MvPolynomial.aeval D.forms).toRingHom
        (Ideal.Quotient.mkₐ ℚ I).toRingHom (MvPolynomial.X i))
  rw [hmap]
  exact hpzero i

/-- Fixed principal-open normalization data for an affine fivefold in
twelve-space.  The local exponent is five. -/
structure FixedQuotientFivefoldResidueModel
    {r : ℕ} (f : Fin r → MvPolynomial (Fin 12) ℚ) where
  parameterCount : ℕ
  parameterCount_le_five : parameterCount ≤ 5
  denominator : ℤ
  denominator_ne_zero : denominator ≠ 0
  equations : Fin r →
    MvPolynomial (Fin 12) (Localization.Away denominator)
  parameters : Fin parameterCount →
    MvPolynomial (Fin 12) (Localization.Away denominator)
  relations : Fin 12 →
    (MvPolynomial (Fin parameterCount)
      (Localization.Away denominator))[X]
  equations_map : ∀ i, MvPolynomial.map
    (awayToFractionRing (R := ℤ) (K := ℚ)
      denominator denominator_ne_zero) (equations i) = f i
  relations_monic : ∀ i, (relations i).Monic
  generic_model : Ideal.map
      (MvPolynomial.map
        (awayToFractionRing (R := ℤ) (K := ℚ)
          denominator denominator_ne_zero))
      (finiteNormalizationModelIdeal equations parameters relations) =
    Ideal.span (Set.range f)
  normalization_finite :
    (finiteNormalizationModelAlgHom equations parameters relations).Finite
  localConstant : ℕ
  one_le_localConstant : 1 ≤ localConstant
  local_bound : ∀ (p : ℕ) (hp : p.Prime)
      (hpden : ¬ p ∣ denominator.natAbs),
    (principalOpenIdealZeroFinset 12 denominator p hp hpden
      (finiteNormalizationModelIdeal equations parameters relations)).card ≤
        localConstant * p ^ 5

/-- Construction of the fixed quotient residue model from a geometrically
integral projective fourfold. -/
theorem nonempty_fixedQuotientFivefoldResidueModel
    {r degree : ℕ} (f : Fin r → MvPolynomial (Fin 12) ℚ)
    (hI : Published.IsIntegralProjectiveVariety (N := 11)
      (Ideal.span (Set.range f)) 4 degree) :
    Nonempty (FixedQuotientFivefoldResidueModel f) := by
  obtain ⟨D, hs⟩ :=
    exists_homogeneousLinearNormalizationData_parameterCount_le_five
      (Ideal.span (Set.range f)) degree hI
  obtain ⟨p, hpmonic, hprelation⟩ :=
    exists_monic_relations_for_quotientNormalizationData
      (Ideal.span (Set.range f)) D
  obtain ⟨Δ, hΔ, f₀, q₀, p₀, hf₀, _hq₀, hp₀monic, _hp₀map,
      hmodel, hfinite⟩ :=
    exists_vertical_finite_normalization_model
      (R := ℤ) (K := ℚ) f D.forms p hpmonic
      (Ideal.span (Set.range f)) rfl hprelation
  let S := Localization.Away Δ
  let A := MvPolynomial (Fin 12) S ⧸
    finiteNormalizationModelIdeal f₀ q₀ p₀
  let g : MvPolynomial (Fin D.parameterCount) S →ₐ[S] A :=
    finiteNormalizationModelAlgHom f₀ q₀ p₀
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_natCard_algHom_le_mul_pow_of_finite_normalization_over_base
      S A D.parameterCount g hfinite
  refine ⟨
    { parameterCount := D.parameterCount
      parameterCount_le_five := hs
      denominator := Δ
      denominator_ne_zero := hΔ
      equations := f₀
      parameters := q₀
      relations := p₀
      equations_map := hf₀
      relations_monic := hp₀monic
      generic_model := hmodel
      normalization_finite := hfinite
      localConstant := C
      one_le_localConstant := hC
      local_bound := ?_ }⟩
  intro ℘ h℘ h℘Δ
  letI : NeZero ℘ := ⟨h℘.ne_zero⟩
  letI : Fact ℘.Prime := ⟨h℘⟩
  letI : Algebra S (ZMod ℘) :=
    (awayIntToZMod Δ ℘ h℘ h℘Δ).toAlgebra
  have hcount : Nat.card (A →ₐ[S] ZMod ℘) ≤
      C * Nat.card (ZMod ℘) ^ D.parameterCount :=
    hbound (ZMod ℘)
  calc
    (principalOpenIdealZeroFinset 12 Δ ℘ h℘ h℘Δ
        (finiteNormalizationModelIdeal f₀ q₀ p₀)).card =
        Nat.card (A →ₐ[S] ZMod ℘) := by
      simpa only [principalOpenIdealZeroFinset, S, A] using
        card_affineIdealZeroFinsetOver_eq_natCard_quotientAlgHom
          (K := ZMod ℘) (finiteNormalizationModelIdeal f₀ q₀ p₀)
    _ ≤ C * Nat.card (ZMod ℘) ^ D.parameterCount := hcount
    _ = C * ℘ ^ D.parameterCount := by simp
    _ ≤ C * ℘ ^ 5 := by
      exact Nat.mul_le_mul_left C (Nat.pow_le_pow_right h℘.one_le hs)

/-- Finite-equation form of the quotient model constructor. -/
theorem nonempty_fixedQuotientFivefoldResidueModel_finiteEquationIdeal
    (equations : Finset (MvPolynomial (Fin 12) ℚ)) (degree : ℕ)
    (hI : Published.IsIntegralProjectiveVariety (N := 11)
      (finiteEquationIdeal equations) 4 degree) :
    Nonempty (FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily equations)) := by
  apply nonempty_fixedQuotientFivefoldResidueModel
    (degree := degree) (indexedFinsetFamily equations)
  rw [span_range_indexedFinsetFamily_eq_finiteEquationIdeal]
  exact hI

/-- An integral common zero of the displayed quotient equations reduces to
the fixed principal-open model at every prime away from its denominator. -/
theorem quotientIntCast_mem_principalOpenModel_of_mem_integralEquationFinset
    (equations : Finset (MvPolynomial (Fin 12) ℤ))
    (M : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (x : Fin 12 → ℤ)
    (hx : ∀ g ∈ equations, MvPolynomial.eval x g = 0)
    (p : ℕ) (hp : p.Prime)
    (hpden : ¬ p ∣ M.denominator.natAbs) :
    (fun i ↦ (x i : ZMod p)) ∈
      principalOpenIdealZeroFinset 12 M.denominator p hp hpden
        (finiteNormalizationModelIdeal
          M.equations M.parameters M.relations) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  let S := Localization.Away M.denominator
  let φQ : S →+* ℚ :=
    awayToFractionRing M.denominator M.denominator_ne_zero
  let φp : S →+* ZMod p :=
    awayIntToZMod M.denominator p hp hpden
  letI : Algebra S (ZMod p) := φp.toAlgebra
  change (fun i ↦ (x i : ZMod p)) ∈
    affineIdealZeroFinsetOver
      (finiteNormalizationModelIdeal M.equations M.parameters M.relations)
  rw [mem_affineIdealZeroFinsetOver_iff]
  intro g₀ hg₀
  have hQg₀ : MvPolynomial.map φQ g₀ ∈
      Ideal.span (Set.range
        (indexedFinsetFamily (rationalizedEquationFinset equations))) := by
    rw [← M.generic_model]
    exact Ideal.mem_map_of_mem _ hg₀
  rw [span_range_indexedFinsetFamily_eq_finiteEquationIdeal] at hQg₀
  have hcommon : (fun i ↦ (x i : ℚ)) ∈
      finiteAffineCommonZeroLocus
        (rationalizedEquationFinset equations) := by
    intro q hq
    rw [rationalizedEquationFinset, Finset.mem_image] at hq
    obtain ⟨g, hg, rfl⟩ := hq
    rw [eval_map_intCast, hx g hg, Int.cast_zero]
  rw [← affineIdealZeroLocus_finiteEquationIdeal] at hcommon
  have hQzero :
      MvPolynomial.eval (fun i ↦ (x i : ℚ))
        (MvPolynomial.map φQ g₀) = 0 := hcommon _ hQg₀
  let xS : Fin 12 → S := fun i ↦ algebraMap ℤ S (x i)
  have hxQcoord : φQ ∘ xS = fun i ↦ (x i : ℚ) := by
    funext i
    simpa only [xS, φQ, Function.comp_apply, S] using
      awayToFractionRing_algebraMap
        M.denominator M.denominator_ne_zero (x i)
  have hmapQ :
      φQ (MvPolynomial.eval xS g₀) =
        MvPolynomial.eval (fun i ↦ (x i : ℚ))
          (MvPolynomial.map φQ g₀) := by
    have heval := MvPolynomial.map_eval φQ xS g₀
    rw [hxQcoord] at heval
    exact heval
  have hSzero : MvPolynomial.eval xS g₀ = 0 := by
    apply (awayToFractionRing_injective (R := ℤ) (K := ℚ)
      M.denominator M.denominator_ne_zero)
    rw [hmapQ, hQzero, map_zero]
  change MvPolynomial.eval₂ φp (fun i ↦ (x i : ZMod p)) g₀ = 0
  have hspecialize := (MvPolynomial.eval₂_comp φp xS g₀).symm
  have hxpcoord : φp ∘ xS = fun i ↦ (x i : ZMod p) := by
    funext i
    simpa only [xS, φp, Function.comp_apply, S] using
      awayIntToZMod_algebraMap M.denominator p hp hpden (x i)
  rw [hxpcoord, hSzero, map_zero] at hspecialize
  exact hspecialize

end

end TranslatedDepthSeven
