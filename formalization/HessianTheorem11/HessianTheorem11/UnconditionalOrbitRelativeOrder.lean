import HessianTheorem11.UnconditionalOrbitOrder
import HessianTheorem11.ReducedRelativeOrder

/-! The already defined relative ideal order equals the concrete finite
coefficient/weight test. No new notion of relative order or new input. -/
noncomputable section
namespace HessianTheorem11.UnconditionalOrbitIdeal
open MvPolynomial PolynomialRestriction PolynomialWeightTransport ReducedRelative
open ReducedWeightCurve RationalDescent UnconditionalOrbitWeights
variable {K : Type*} [Field K] {n d : ℕ}

def identityWeightFrame (w : Fin n → ℤ) (hw : ∑ i, w i=0) : WeightFrame K n where
  matrix := 1
  injective := by intro x y h; simpa only [Matrix.one_mulVec] using h
  weight := w
  sum_zero := hw

theorem originalCurve_identity (F : MvPolynomial (Fin n) K)
    (w : Fin n → ℤ) (hw : ∑ i, w i=0) (t : K) :
    originalCurve F (identityWeightFrame w hw) t = curve F w t := by
  simp [originalCurve,identityWeightFrame,restrict_one]

theorem originalTest_identity_finiteEquation [Infinite K]
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (w : Fin n → ℤ) (hw : ∑ i, w i=0)
    (P : MvPolynomial (Fin n →₀ ℕ) K) :
    originalTest d F (identityWeightFrame w hw) P = finiteCurveTest F w (finiteEquation (d := d) P) := by
  apply Polynomial.funext
  intro t
  rw [originalTest_eval F hF,originalCurve_identity,eval_finiteCurveTest,
    eval_finiteEquation _ (curve_homogeneous F hF w t)]

theorem originalTest_identity_rename [Infinite K]
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (w : Fin n → ℤ) (hw : ∑ i, w i=0)
    (P : MvPolynomial (DegreeIndex n d) K) :
    originalTest d F (identityWeightFrame w hw) (rename Subtype.val P) = finiteCurveTest F w P := by
  apply Polynomial.funext
  intro t
  rw [originalTest_eval F hF,originalCurve_identity,eval_finiteCurveTest,eval_rename]
  rfl

theorem le_relativeOrder_iff_all_dvd
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (S : Set (MvPolynomial (Fin n) K)) (hS : coefficientClosed S) (hnot : F ∉ S)
    (f : WeightFrame K n) (m : ℕ) :
    m ≤ relativeOrder d F S f ↔
      ∀ P, coefficientVanishing S P → Polynomial.X ^ m ∣ originalTest d F f P := by
  constructor
  · intro hm P hP
    apply Polynomial.X_pow_dvd_iff.mpr
    intro k hk
    exact Polynomial.X_pow_dvd_iff.mp (relativeOrder_dvd F S f P hP) k (hk.trans_le hm)
  · intro h
    by_contra hm
    obtain ⟨P,hP,hc⟩ := relativeOrder_attained F hF S hS hnot f
    exact hc (Polynomial.X_pow_dvd_iff.mp (h P hP) _ (by omega))

theorem all_original_dvd_iff_finite [Infinite K]
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (S : Set (MvPolynomial (Fin n) K)) (hhom : ∀ G ∈ S, G.IsHomogeneous d)
    (w : Fin n → ℤ) (hw : ∑ i, w i=0) (m : ℕ) :
    (∀ P, coefficientVanishing S P →
      Polynomial.X ^ m ∣ originalTest d F (identityWeightFrame w hw) P) ↔
    (∀ P ∈ vanishingIdeal K (finiteTarget (d := d) S),
      Polynomial.X ^ m ∣ finiteCurveTest F w P) := by
  constructor
  · intro h P hP
    rw [← originalTest_identity_rename F hF w hw P]
    apply h
    intro G hG
    rw [eval_rename]
    exact hP _ ⟨G,hG,rfl⟩
  · intro h P hP
    rw [originalTest_identity_finiteEquation F hF w hw P]
    apply h
    rintro _ ⟨G,hG,rfl⟩
    change eval (coefficientVector (d := d) G) (finiteEquation (d := d) P) = 0
    rw [eval_finiteEquation G (hhom G hG)]
    exact hP G hG

/-- Exact bridge to the pre-existing literal ideal-order definition, using
the actual finite target equations and their actual polynomial weights. -/
theorem le_relativeOrder_iff_weight_components [Infinite K]
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (S : Set (MvPolynomial (Fin n) K)) (hS : coefficientClosed S)
    (hhom : ∀ G ∈ S, G.IsHomogeneous d) (hnot : F ∉ S)
    (w : Fin n → ℤ) (hw : ∑ i, w i=0) (hW : HasNonnegativeWeights F w)
    (N m : ℕ)
    (hgen : Ideal.span (boundedIdeal (finiteTarget (d := d) S) N :
      Set (MvPolynomial (DegreeIndex n d) K)) = vanishingIdeal K (finiteTarget (d := d) S)) :
    m ≤ relativeOrder d F S (identityWeightFrame w hw) ↔
    (∀ P : boundedIdeal (finiteTarget (d := d) S) N, ∀ k : ℕ, k < m →
      eval (coefficientVector F) (weightPart P.val (coefficientWeights w) (k : ℤ)) = 0) := by
  rw [le_relativeOrder_iff_all_dvd F hF S hS hnot,
    all_original_dvd_iff_finite F hF S hhom w hw m,
    all_ideal_pullbacks_dvd_iff_weight_components F hF w hW S N m hgen]

end HessianTheorem11.UnconditionalOrbitIdeal
