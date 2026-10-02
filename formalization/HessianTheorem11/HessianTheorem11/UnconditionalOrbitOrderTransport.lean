import HessianTheorem11.UnconditionalOrbitWeightUpper
import HessianTheorem11.UnconditionalOrbitFrameOrder

/-! Quantitative relative ideal order is preserved by a weighted flag.
The proof uses actual bounded ideal equations and triangular substitutions
on coefficient polynomials, without a geometric group-action input. -/
noncomputable section
namespace HessianTheorem11.UnconditionalOrbitIdeal
open MvPolynomial PolynomialRestriction PolynomialWeightTransport ReducedRelative
open ReducedWeightCurve RationalDescent UnconditionalOrbitWeights
variable {K : Type*} [Field K] [Infinite K] {n d : ℕ}

theorem bounded_eval_zero_of_upper
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (S : Set (MvPolynomial (Fin n) K)) (N m : ℕ)
    (v : Fin n → ℤ) (hV : HasNonnegativeWeights F v)
    (hvan : ∀ P : boundedIdeal (finiteTarget (d := d) S) N, ∀ k : ℕ, k < m →
      eval (coefficientVector F) (weightPart P.val (coefficientWeights v) (k : ℤ)) = 0)
    (P : boundedIdeal (finiteTarget (d := d) S) N) (a : ℤ) (ha : a < m)
    (hP : UpperBound P.val (coefficientWeights v) a) : eval (coefficientVector F) P.val = 0 := by
  classical
  have he : eval (coefficientVector F) P.val =
      ∑ r ∈ P.val.support.image (exponentWeight (coefficientWeights v)),
        eval (coefficientVector F) (weightPart P.val (coefficientWeights v) r) := by
    have h := congrArg (eval (coefficientVector F)) (sum_weightParts_one P.val (coefficientWeights v))
    simpa only [map_sum] using h.symm
  rw [he]
  apply Finset.sum_eq_zero
  intro r hr
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hr
  have hle := hP e he
  by_cases hp : 0 ≤ exponentWeight (coefficientWeights v) e
  · have hk : (exponentWeight (coefficientWeights v) e).toNat < m := by omega
    have h := hvan P _ hk
    simpa only [Int.toNat_of_nonneg hp] using h
  · exact (finiteCurveTest_weightPart_of_negative F hF v hV P.val _ (by omega)).1

/-- A triangular special-linear coordinate change cannot lower the
relative order when its new weights give the same flag filtration. -/
theorem identity_order_le_of_weight_triangular
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (S : Set (MvPolynomial (Fin n) K)) (hclosed : coefficientClosed S)
    (hS : slInvariant S) (hhom : ∀ G ∈ S, G.IsHomogeneous d) (hnot : F ∉ S)
    (A : Matrix (Fin n) (Fin n) K) (hA : A.det = 1)
    (v w : Fin n → ℤ) (hv : ∑ i, v i = 0) (hw : ∑ i, w i = 0)
    (hentry : ∀ i j, A i j ≠ 0 → v i ≤ w j)
    (hV : HasNonnegativeWeights F v) (hW : HasNonnegativeWeights (restrict A F) w) :
    relativeOrder d F S (identityWeightFrame v hv) ≤
      relativeOrder d (restrict A F) S (identityWeightFrame w hw) := by
  classical
  have hnot' : restrict A F ∉ S := by
    intro h
    apply hnot
    have hi : A⁻¹.det = 1 := by rw [Matrix.det_nonsing_inv,hA,Ring.inverse_one]
    have h' := hS A⁻¹ hi _ h
    rwa [restrict_restrict,Matrix.mul_nonsing_inv A (hA ▸ isUnit_one),restrict_one] at h'
  obtain ⟨N,hgen⟩ := exists_boundedIdeal_generates (finiteTarget (d := d) S)
  let m := relativeOrder d F S (identityWeightFrame v hv)
  have hvan := (le_relativeOrder_iff_weight_components F hF S hclosed hhom hnot v hv hV N m hgen).mp le_rfl
  apply (le_relativeOrder_iff_weight_components (restrict A F) (homogeneous_restrict A F hF)
    S hclosed hhom hnot' w hw hW N m hgen).mpr
  intro P k hk
  let Q := weightPart P.val (coefficientWeights w) (k : ℤ)
  have hQ : Q ∈ boundedIdeal (finiteTarget (d := d) S) N := target_weightPart_mem S hS hhom N w hw P _
  have hR : restrict (finiteCoefficientMatrix A) Q ∈ boundedIdeal (finiteTarget (d := d) S) N :=
    restrict_mem_boundedIdeal (finiteCoefficientMatrix A) (finiteTarget S) N
      (finiteTarget_invariant S hS hhom A hA) hQ
  have hupper : UpperBound (restrict (finiteCoefficientMatrix A) Q) (coefficientWeights v) (k : ℤ) :=
    coefficientPullback_upper A v w hentry Q k (weightPart_upper P.val (coefficientWeights w) k)
  have hz := bounded_eval_zero_of_upper F hF S N m v hV hvan ⟨_,hR⟩ k (by exact_mod_cast hk) hupper
  rw [coefficientVector_restrict A F hF,← eval_restrict]
  exact hz

end HessianTheorem11.UnconditionalOrbitIdeal
