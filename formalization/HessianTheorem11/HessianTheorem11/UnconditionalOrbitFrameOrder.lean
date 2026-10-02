import HessianTheorem11.UnconditionalOrbitFiniteCharacters

/-! Relative ideal order in an actual special-linear frame equals its
identity-frame expression in the transformed polynomial. The invariant
target and its finite generating degree cutoff remain literally fixed. -/
noncomputable section
namespace HessianTheorem11.UnconditionalOrbitIdeal
open MvPolynomial PolynomialRestriction PolynomialWeightTransport ReducedOrbitCoordinates ReducedRelative
open ReducedWeightCurve RationalDescent
variable {K : Type*} [Field K] [Infinite K] {n d : ℕ}

theorem eval_coefficientPullback (B : Matrix (Fin n) (Fin n) K)
    (G : MvPolynomial (Fin n) K) (hG : G.IsHomogeneous d)
    (P : MvPolynomial (Fin n →₀ ℕ) K) :
    eval (fun e => coeff e G) (aeval (coefficientRestriction B d) P) =
      eval (fun e => coeff e (restrict B G)) P := by
  change aeval (fun e => coeff e G) (aeval (coefficientRestriction B d) P) = _
  rw [MvPolynomial.comp_aeval_apply]
  have h : (fun e => aeval (fun m => coeff m G) (coefficientRestriction B d e)) =
      (fun e => coeff e (restrict B G)) := funext (eval_coefficientRestriction B G hG)
  rw [h]
  rfl

theorem coefficientVanishing_pullback (S : Set (MvPolynomial (Fin n) K))
    (hS : slInvariant S) (hhom : ∀ G ∈ S, G.IsHomogeneous d)
    (B : Matrix (Fin n) (Fin n) K) (hB : B.det = 1)
    (P : MvPolynomial (Fin n →₀ ℕ) K) (hP : coefficientVanishing S P) :
    coefficientVanishing S (aeval (coefficientRestriction B d) P) := by
  intro G hG
  rw [eval_coefficientPullback B G (hhom G hG) P]
  exact hP _ (hS B hB G hG)

theorem originalTest_identity_eq_curveTest
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (w : Fin n → ℤ) (hw : ∑ i, w i = 0) (P : MvPolynomial (Fin n →₀ ℕ) K) :
    originalTest d F (identityWeightFrame w hw) P = curveTest F w P := by
  apply Polynomial.funext
  intro t
  rw [originalTest_eval F hF,originalCurve_identity,eval_curveTest]

theorem originalTest_pullback_frame
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (f : WeightFrame K n) (P : MvPolynomial (Fin n →₀ ℕ) K) :
    originalTest d F f (aeval (coefficientRestriction f.matrix d) P) =
      curveTest (restrict f.matrix F) f.weight P := by
  apply Polynomial.funext
  intro t
  rw [originalTest_eval F hF]
  unfold originalCurve
  rw [eval_coefficientPullback f.matrix
    (restrict f.matrix⁻¹ (curve (restrict f.matrix F) f.weight t))
    (homogeneous_restrict f.matrix⁻¹ _
      (curve_homogeneous _ (homogeneous_restrict f.matrix F hF) f.weight t)),eval_curveTest]
  rw [restrict_restrict,Matrix.nonsing_inv_mul f.matrix
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp f.injective)),restrict_one]

theorem all_original_dvd_iff_coordinate [Infinite K]
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (S : Set (MvPolynomial (Fin n) K)) (hS : slInvariant S)
    (hhom : ∀ G ∈ S, G.IsHomogeneous d) (f : WeightFrame K n) (hdet : f.matrix.det = 1) (m : ℕ) :
    (∀ P, coefficientVanishing S P → Polynomial.X ^ m ∣ originalTest d F f P) ↔
    (∀ P, coefficientVanishing S P → Polynomial.X ^ m ∣
      originalTest d (restrict f.matrix F) (identityWeightFrame f.weight f.sum_zero) P) := by
  constructor
  · intro h P hP
    rw [originalTest_identity_eq_curveTest _ (homogeneous_restrict _ F hF),← originalTest_pullback_frame F hF f P]
    exact h _ (coefficientVanishing_pullback S hS hhom f.matrix hdet P hP)
  · intro h P hP
    unfold originalTest
    have hi : f.matrix⁻¹.det = 1 := by rw [Matrix.det_nonsing_inv,hdet,Ring.inverse_one]
    have hh := h _ (coefficientVanishing_pullback S hS hhom f.matrix⁻¹ hi P hP)
    rwa [originalTest_identity_eq_curveTest _ (homogeneous_restrict _ F hF)] at hh

theorem relativeOrder_coordinate
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (S : Set (MvPolynomial (Fin n) K)) (hclosed : coefficientClosed S)
    (hS : slInvariant S) (hhom : ∀ G ∈ S, G.IsHomogeneous d) (hnot : F ∉ S)
    (f : WeightFrame K n) (hdet : f.matrix.det = 1) :
    relativeOrder d F S f = relativeOrder d (restrict f.matrix F) S
      (identityWeightFrame f.weight f.sum_zero) := by
  have hnot' : restrict f.matrix F ∉ S := by
    intro h
    apply hnot
    have hi : f.matrix⁻¹.det = 1 := by rw [Matrix.det_nonsing_inv,hdet,Ring.inverse_one]
    have h' := hS f.matrix⁻¹ hi _ h
    rw [restrict_restrict,Matrix.mul_nonsing_inv f.matrix (hdet ▸ isUnit_one),restrict_one] at h'
    exact h'
  apply Nat.le_antisymm
  · apply (le_relativeOrder_iff_all_dvd _ (homogeneous_restrict _ F hF) S hclosed hnot' _ _).mpr
    apply (all_original_dvd_iff_coordinate F hF S hS hhom f hdet _).mp
    exact (le_relativeOrder_iff_all_dvd F hF S hclosed hnot f _).mp le_rfl
  · apply (le_relativeOrder_iff_all_dvd F hF S hclosed hnot f _).mpr
    apply (all_original_dvd_iff_coordinate F hF S hS hhom f hdet _).mpr
    exact (le_relativeOrder_iff_all_dvd _ (homogeneous_restrict _ F hF) S hclosed hnot' _ _).mp le_rfl

end HessianTheorem11.UnconditionalOrbitIdeal
