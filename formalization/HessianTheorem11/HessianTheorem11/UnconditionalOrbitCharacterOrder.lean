import HessianTheorem11.UnconditionalOrbitCharacters
import HessianTheorem11.UnconditionalOrbitRelativeOrder

/-! The literal target-ideal order is governed by full torus characters
with nonzero evaluation, independently of the chosen one-parameter subgroup. -/
noncomputable section
namespace HessianTheorem11.UnconditionalOrbitIdeal
open MvPolynomial PolynomialRestriction ReducedRelative UnconditionalOrbitWeights
variable {K : Type*} [Field K] [Infinite K] {n d : ℕ}

theorem finiteCurveTest_characterPart_nonnegative (hn : 0 < n)
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (w : Fin n → ℤ) (hw : ∑ i, w i = 0) (hW : HasNonnegativeWeights F w)
    (P : MvPolynomial (DegreeIndex n d) K) (e : DegreeIndex n d →₀ ℕ)
    (ha : 0 ≤ exponentWeight (coefficientWeights w) e) :
    finiteCurveTest F w (characterPart P (equationCharacter e)) =
      Polynomial.monomial (exponentWeight (coefficientWeights w) e).toNat
        (eval (coefficientVector F) (characterPart P (equationCharacter e))) := by
  have h := finiteCurveTest_weightPart_of_nonnegative F hF w hW
    (characterPart P (equationCharacter e)) (exponentWeight (coefficientWeights w) e) ha
  rw [characterPart_pure_weight hn P w hw e] at h
  exact h

theorem finiteCurveTest_characterPart_negative (hn : 0 < n)
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (w : Fin n → ℤ) (hw : ∑ i, w i = 0) (hW : HasNonnegativeWeights F w)
    (P : MvPolynomial (DegreeIndex n d) K) (e : DegreeIndex n d →₀ ℕ)
    (ha : exponentWeight (coefficientWeights w) e < 0) :
    eval (coefficientVector F) (characterPart P (equationCharacter e)) = 0 ∧
      finiteCurveTest F w (characterPart P (equationCharacter e)) = 0 := by
  have h := finiteCurveTest_weightPart_of_negative F hF w hW
    (characterPart P (equationCharacter e)) (exponentWeight (coefficientWeights w) e) ha
  rw [characterPart_pure_weight hn P w hw e] at h
  exact h

theorem dvd_characterPart_iff (hn : 0 < n)
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (w : Fin n → ℤ) (hw : ∑ i, w i = 0) (hW : HasNonnegativeWeights F w)
    (P : MvPolynomial (DegreeIndex n d) K) (e : DegreeIndex n d →₀ ℕ) (m : ℕ) :
    Polynomial.X ^ m ∣ finiteCurveTest F w (characterPart P (equationCharacter e)) ↔
      (eval (coefficientVector F) (characterPart P (equationCharacter e)) ≠ 0 →
        (m : ℤ) ≤ exponentWeight (coefficientWeights w) e) := by
  by_cases ha : exponentWeight (coefficientWeights w) e < 0
  · obtain ⟨hc,hp⟩ := finiteCurveTest_characterPart_negative hn F hF w hw hW P e ha
    simp [hc,hp]
  · have ha0 : 0 ≤ exponentWeight (coefficientWeights w) e := by omega
    rw [finiteCurveTest_characterPart_nonnegative hn F hF w hw hW P e ha0]
    constructor
    · intro h hc
      by_contra hm
      have hlt : (exponentWeight (coefficientWeights w) e).toNat < m := by omega
      have hz := Polynomial.X_pow_dvd_iff.mp h _ hlt
      exact hc (by simpa using hz)
    · intro h
      apply Polynomial.X_pow_dvd_iff.mpr
      intro k hk
      by_cases hc : eval (coefficientVector F) (characterPart P (equationCharacter e)) = 0
      · simp [hc]
      · have hge := h hc
        have hne : (exponentWeight (coefficientWeights w) e).toNat ≠ k := by omega
        simp [Polynomial.coeff_monomial,hne]

/-- The bounded ideal order is the minimum of the weights of its actual
nonvanishing character evaluations. This statement allows cancellation
between monomials within one character, exactly as ideal order requires. -/
theorem bounded_dvd_iff_character_weights (hn : 0 < n)
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (S : Set (MvPolynomial (Fin n) K)) (hS : slInvariant S)
    (hhom : ∀ G ∈ S, G.IsHomogeneous d)
    (w : Fin n → ℤ) (hw : ∑ i, w i = 0) (hW : HasNonnegativeWeights F w) (N m : ℕ) :
    (∀ P : boundedIdeal (finiteTarget (d := d) S) N,
      Polynomial.X ^ m ∣ finiteCurveTest F w P.val) ↔
    (∀ P : boundedIdeal (finiteTarget (d := d) S) N, ∀ e ∈ P.val.support,
      eval (coefficientVector F) (characterPart P.val (equationCharacter e)) ≠ 0 →
        (m : ℤ) ≤ exponentWeight (coefficientWeights w) e) := by
  classical
  constructor
  · intro h P e he
    apply (dvd_characterPart_iff hn F hF w hw hW P.val e m).mp
    exact h ⟨_,target_characterPart_mem hn S hS hhom N P _⟩
  · intro h P
    have he : finiteCurveTest F w P.val =
        ∑ c ∈ P.val.support.image equationCharacter, finiteCurveTest F w (characterPart P.val c) := by
      have heq := congrArg (finiteCurveHom F w) (sum_characterParts P.val)
      simpa only [map_sum,finiteCurveHom_apply] using heq.symm
    rw [he]
    apply Finset.dvd_sum
    intro c hc
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hc
    exact (dvd_characterPart_iff hn F hF w hw hW P.val e m).mpr (h P e he)

theorem le_relativeOrder_iff_character_weights (hn : 0 < n)
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (S : Set (MvPolynomial (Fin n) K)) (hclosed : coefficientClosed S)
    (hS : slInvariant S) (hhom : ∀ G ∈ S, G.IsHomogeneous d) (hnot : F ∉ S)
    (w : Fin n → ℤ) (hw : ∑ i, w i = 0) (hW : HasNonnegativeWeights F w) (N m : ℕ)
    (hgen : Ideal.span (boundedIdeal (finiteTarget (d := d) S) N :
      Set (MvPolynomial (DegreeIndex n d) K)) = vanishingIdeal K (finiteTarget (d := d) S)) :
    m ≤ relativeOrder d F S (identityWeightFrame w hw) ↔
    (∀ P : boundedIdeal (finiteTarget (d := d) S) N, ∀ e ∈ P.val.support,
      eval (coefficientVector F) (characterPart P.val (equationCharacter e)) ≠ 0 →
        (m : ℤ) ≤ exponentWeight (coefficientWeights w) e) := by
  rw [le_relativeOrder_iff_all_dvd F hF S hclosed hnot,
    all_original_dvd_iff_finite F hF S hhom w hw m,
    all_ideal_pullbacks_dvd_iff_bounded F w S N m hgen,
    bounded_dvd_iff_character_weights hn F hF S hS hhom w hw hW N m]

end HessianTheorem11.UnconditionalOrbitIdeal
