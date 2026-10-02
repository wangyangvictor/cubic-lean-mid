import CubicTenVariables.RealPlace
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! An anisotropic rational binary cubic has a simple projective zero over
every algebraically closed extension of the rationals. We exhibit the
affine representative `(t, 1)`, using the actual univariate restriction and
its derivative. No geometric smooth-point theorem is assumed here. -/

noncomputable section

namespace CubicTenVariables.BinaryInfinitySmoothPoint

open MvPolynomial HessianTheorem11

/-- The chart with second coordinate one contains a zero with nonzero
first partial derivative. The hypotheses concern the rational cubic itself. -/
theorem exists_simple_affine_root {K : Type*} [Field K] [Algebra ℚ K] [IsAlgClosed K]
    (H : MvPolynomial (Fin 2) ℚ) (hH : H.IsHomogeneous 3) (hA : Anisotropic H) :
    ∃ t : K, eval ![t, 1] (map (algebraMap ℚ K) H) = 0 ∧
      eval ![t, 1] (pderiv 0 (map (algebraMap ℚ K) H)) ≠ 0 := by
  classical
  let u : Fin 2 → ℚ := Pi.single 0 1
  let v : Fin 2 → ℚ := Pi.single 1 1
  have hu : u ≠ 0 := by
    intro h
    have he := congrFun h 0
    simp [u] at he
  have hlead := anisotropic_eval_ne_zero hA hu
  let P := RealPlace.linePolynomial H u v
  have hd : P.natDegree = 3 := RealPlace.linePolynomial_natDegree H hH u v hlead
  have hnoroot : ∀ t : ℚ, ¬ P.IsRoot t := by
    intro t ht
    have hvect : (fun i => v i + t * u i) ≠ 0 := by
      intro h
      have he := congrFun h 1
      simp [u, v] at he
    apply hvect
    apply hA
    have he := RealPlace.linePolynomial_eval₂ H u v (RingHom.id ℚ) t
    simpa only [Polynomial.eval₂_id, RingHom.id_apply, MvPolynomial.eval₂_id]
      using he.symm.trans ht
  have hi : Irreducible P := Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    (by simp [hd]) hnoroot
  have hdegree : P.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hi.ne_zero, hd]
    norm_num
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_eval₂_eq_zero (algebraMap ℚ K) P hdegree
  have hderiv := hi.separable.eval₂_derivative_ne_zero (algebraMap ℚ K) ht
  have hvec : (fun i => algebraMap ℚ K (v i) + t * algebraMap ℚ K (u i)) =
      ![t, 1] := by
    funext i
    fin_cases i <;> simp [u, v]
  refine ⟨t, ?_, ?_⟩
  · rw [← MvPolynomial.eval₂_eq_eval_map, ← hvec]
    exact (RealPlace.linePolynomial_eval₂ H u v (algebraMap ℚ K) t).symm.trans ht
  · rw [pderiv_map, ← MvPolynomial.eval₂_eq_eval_map]
    rw [show P = RealPlace.linePolynomial H u v from rfl,
      RealPlace.linePolynomial_derivative_eval₂, hvec] at hderiv
    simpa [Fin.sum_univ_two, u] using hderiv

/-- An explicit nonzero binary vector at which the cubic vanishes and at
least one formal partial derivative is nonzero. -/
theorem exists_simple_binary_zero {K : Type*} [Field K] [Algebra ℚ K] [IsAlgClosed K]
    (H : MvPolynomial (Fin 2) ℚ) (hH : H.IsHomogeneous 3) (hA : Anisotropic H) :
    ∃ x : Fin 2 → K, x ≠ 0 ∧ eval x (map (algebraMap ℚ K) H) = 0 ∧
      ∃ i : Fin 2, eval x (pderiv i (map (algebraMap ℚ K) H)) ≠ 0 := by
  obtain ⟨t, ht, hd⟩ := exists_simple_affine_root (K := K) H hH hA
  refine ⟨![t, 1], ?_, ht, 0, hd⟩
  intro h
  have he := congrFun h 1
  simp at he

end CubicTenVariables.BinaryInfinitySmoothPoint
