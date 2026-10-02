import TranslatedDepthSeven.RationalProjectiveCurveFirstChartBezoutInternal
import TranslatedDepthSeven.ProgressionNormalizationBlockEvaluation
import TranslatedDepthSeven.AffineIntegralPointTransport

/-! An elementary coefficient-uniform count on rational prime curves.
Two distinct points select a nonconstant coordinate. Each of its fibers is
a proper linear section, so the proved curve Bézout bound gives at most D
points per fiber. No Pila or determinant-method estimate is assumed. -/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 2500000

theorem rationalIntegralAffineChartPoint_progression {N : ℕ}
    (u z : Fin N → ℤ) (m : ℕ) :
    rationalIntegralAffineChartPoint (integralAffineMap u z m) =
      fun i => (progressionHomogeneousPoint u m z i : ℚ) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [progressionHomogeneousPoint, integralAffineMap]

/-- Proper homogeneous cuts of a prime curve contain at most the product
of the degrees many actual progression points. Injectivity of the positive
progression scale is proved, rather than a point multiplicity being assumed. -/
theorem card_primeCurve_progression_properCut_le
    {N D e m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hdegree : HasProjectiveDimensionDegree I 1 D)
    (G : MvPolynomial (Fin (N + 1)) ℚ) (hGhom : G.IsHomogeneous e) (hGnot : G ∉ I)
    (u : Fin N → ℤ) (S : Finset (Fin N → ℤ))
    (hsource : ∀ z ∈ S,
      (fun i => (progressionHomogeneousPoint u m z i : ℚ)) ∈ affineIdealZeroLocus I)
    (hcut : ∀ z ∈ S,
      eval (fun i => (progressionHomogeneousPoint u m z i : ℚ)) G = 0) :
    S.card ≤ D * e := by
  classical
  have h := card_integralAffinePoints_on_projectiveCurve_auxiliary_le
    rationalProjectiveCurveAuxiliaryFirstChartBezout_internal I G hprime hhom hdegree
    hGhom hGnot (S.image (fun z => integralAffineMap u z m))
    (by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      rw [rationalIntegralAffineChartPoint_progression]
      exact hsource z hz)
    (by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      rw [rationalIntegralAffineChartPoint_progression]
      exact hcut z hz)
  rwa [Finset.card_image_of_injective S (integralAffineMap_injective hm u)] at h

/-- The exact bound D(2B+1) is uniform in the prime curve, its coefficients,
the integral center and the positive progression scale. It applies to all
prime curves, including lines and curves not geometrically integral. -/
theorem card_primeCurve_progression_box_le
    {N D B m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hdegree : HasProjectiveDimensionDegree I 1 D)
    (u : Fin N → ℤ) (S : Finset (Fin N → ℤ))
    (hsource : ∀ z ∈ S,
      (fun i => (progressionHomogeneousPoint u m z i : ℚ)) ∈ affineIdealZeroLocus I)
    (hbox : ∀ z ∈ S, ∀ i, (z i).natAbs ≤ B) :
    S.card ≤ D * (2 * B + 1) := by
  classical
  by_cases hsmall : S.card ≤ 1
  · exact hsmall.trans ((hdegree.2.1).trans_le
      (Nat.le_mul_of_pos_right D (by omega)))
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
    by_contra! h
    exact hxy (funext h)
  let G : ℤ → MvPolynomial (Fin (N + 1)) ℚ := fun t =>
    X j.succ - C ((u j + (m : ℤ) * t : ℤ) : ℚ) * X 0
  have hGhom (t : ℤ) : (G t).IsHomogeneous 1 :=
    (isHomogeneous_X ℚ j.succ).sub
      ((isHomogeneous_C _ _).mul (isHomogeneous_X ℚ 0))
  have hGnot (t : ℤ) : G t ∉ I := by
    intro hGI
    have heval (z : Fin N → ℤ) (hz : z ∈ S) :
        u j + (m : ℤ) * z j = u j + (m : ℤ) * t := by
      have hh := hsource z hz (G t) hGI
      simp only [G, map_sub, map_mul, eval_X, eval_C,
        progressionHomogeneousPoint, Fin.cases_succ, Fin.cases_zero,
        Int.cast_one, mul_one] at hh
      exact_mod_cast sub_eq_zero.mp hh
    have hmul : (m : ℤ) * x j = (m : ℤ) * y j :=
      add_left_cancel ((heval x hx).trans (heval y hy).symm)
    exact hj (mul_left_cancel₀ (by exact_mod_cast hm.ne' : (m : ℤ) ≠ 0) hmul)
  have hcount := finiteSet_card_le_fibre_mul_integerBox
    (d := 1) S (fun z _ => z j) B D
    (fun z hz _ => hbox z hz j)
    (by
      intro t
      have hh := card_primeCurve_progression_properCut_le hm I hprime hhom hdegree
        (G (t 0)) (hGhom (t 0)) (hGnot (t 0)) u
        (S.filter fun z => (fun _ : Fin 1 => z j) = t)
        (fun z hz => hsource z (Finset.mem_filter.mp hz).1)
        (by
          intro z hz
          have he : z j = t 0 := congrFun (Finset.mem_filter.mp hz).2 0
          simp [G, progressionHomogeneousPoint, he])
      simpa using hh)
  simpa [Nat.mul_comm] using hcount

end
end TranslatedDepthSeven
