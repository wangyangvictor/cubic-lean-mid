import HessianTheorem11.UnconditionalValuationRelative
import HessianTheorem11.UnconditionalOrbitCharacterScaling

/-! A literal integral diagonal degeneration into an invariant residue target
produces an actual nonzero special-linear integral one-parameter weight. -/
noncomputable section
namespace HessianTheorem11.UnconditionalValuationRelative
open MvPolynomial PolynomialRestriction ReducedRelative UnconditionalOrbitIdeal
  UnconditionalValuationWeights
variable {K : Type*} [Field K] (V : ValuationSubring K)
  [Infinite (IsLocalRing.ResidueField V)] {n d : ℕ}

/-- Strict positivity for an actual active equation follows from an exact
character eigenvector identity, after a support-preserving residue lift. -/
theorem active_character_positive_of_integral_diagonal (hn : 0 < n)
    (C H : MvPolynomial (Fin n) V) (δ : Fin n → Kˣ) (hδ : ∏ i, δ i = 1)
    (hCH : map V.subtype H =
      restrict (Matrix.diagonal (fun i => (δ i : K))) (map V.subtype C))
    (S : Set (MvPolynomial (Fin n) (IsLocalRing.ResidueField V)))
    (hS : slInvariant S) (hhom : ∀ G ∈ S, G.IsHomogeneous d)
    (hH : residuePolynomial V H ∈ S) (N : ℕ) (a : Fin n → ℤ)
    (ha : a ∈ activeCharacters (d := d) (residuePolynomial V C) S N) :
    0 < UnconditionalOrderedWeights.value a (fun i => weight V (δ i)) := by
  classical
  obtain ⟨p,hpure,hc,hz⟩ := exists_active_equation_lift V hn C H S hS hhom hH N a ha
  have hpossible := activeCharacters_subset (residuePolynomial V C) S N ha
  change a ∈ (equationMonomials n d N).image equationCharacter at hpossible
  obtain ⟨e,he,hea⟩ := Finset.mem_image.mp hpossible
  have hpureK : ∀ f ∈ (map V.subtype p).support, equationCharacter f = equationCharacter e := by
    intro f hf
    exact (hpure f (support_map_subset V.subtype p hf)).trans hea.symm
  have hcoef : coefficientVector (d := d) (map V.subtype H) =
      fun m => (coefficientDiagonal δ m : K) * coefficientVector (map V.subtype C) m := by
    funext m
    change coeff m.val (map V.subtype H) = _
    rw [hCH,coeff_restrict_diagonal]
    simp only [coefficientDiagonal,Units.coe_prod,Units.val_pow_eq_pow_val,coefficientVector]
    ring
  have hs := eval_characterPolynomial_coefficientDiagonal_pow hn δ hδ
    (coefficientVector (map V.subtype C)) (map V.subtype p) e hpureK
  rw [←hcoef,←map_integralEquationValue V V.subtype H p,
    ←map_integralEquationValue V V.subtype C p,hea] at hs
  apply character_positive_of_power_relation V hn δ a
    (integralEquationValue V C p) (integralEquationValue V H p) hc hz
  simpa only [Units.coe_prod,Units.val_zpow_eq_zpow_val] using hs

/-- A valuation-ring diagonal degeneration into a closed SL-invariant residue
target yields a nonzero integral SL weight whose literal relative ideal order
is positive. Neither an instability theorem nor an optimality theorem is used. -/
theorem integral_diagonal_relative_weight (hn : 0 < n)
    (C H : MvPolynomial (Fin n) V) (hC : C.IsHomogeneous d)
    (δ : Fin n → K) (hδ : ∀ i, δ i ≠ 0) (hprod : ∏ i, δ i = 1)
    (hCH : map V.subtype H = restrict (Matrix.diagonal δ) (map V.subtype C))
    (S : Set (MvPolynomial (Fin n) (IsLocalRing.ResidueField V)))
    (hclosed : coefficientClosed S) (hS : slInvariant S)
    (hhom : ∀ G ∈ S, G.IsHomogeneous d)
    (hH : residuePolynomial V H ∈ S) (hnot : residuePolynomial V C ∉ S) :
    ∃ w : Fin n → ℤ, w ≠ 0 ∧ ∃ hw : ∑ i, w i = 0,
      HasNonnegativeWeights (residuePolynomial V C) w ∧
      1 ≤ relativeOrder d (residuePolynomial V C) S (identityWeightFrame w hw) := by
  classical
  let x : Fin n → Kˣ := fun i => Units.mk0 (δ i) (hδ i)
  have hx : ∏ i, x i = 1 := by
    apply Units.ext
    simpa [x] using hprod
  have hmodel : map V.subtype H =
      restrict (Matrix.diagonal (fun i => (x i : K))) (map V.subtype C) := hCH
  obtain ⟨N,hgen⟩ := exists_boundedIdeal_generates (finiteTarget (d := d) S)
  obtain ⟨w,hwne,_,hW,hw,horder⟩ := relative_weight_of_ordered_support hn
    (residuePolynomial V C) (hC.map (IsLocalRing.residue V))
    S hclosed hS hhom hnot N hgen (fun i => weight V (x i)) (sum_weight_eq_zero V x hx)
    (by
      intro e he
      exact residue_support_nonnegative V C H x hmodel.symm e (mem_support_iff.mp he))
    (by
      intro a ha
      exact active_character_positive_of_integral_diagonal V hn C H x hx hmodel
        S hS hhom hH N a ha)
  exact ⟨w,hwne,hw,hW,horder⟩

end HessianTheorem11.UnconditionalValuationRelative
