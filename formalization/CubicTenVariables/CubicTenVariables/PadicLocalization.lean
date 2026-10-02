import CubicTenVariables.HighRankLocalPoint
import CubicTenVariables.PadicPrimitive
import CubicTenVariables.PadicPolynomialNeighborhood
import CubicTenVariables.PadicCongruenceNeighborhood

/-!
# A literal primitive p-adic congruence class with a fixed nonzero Hessian minor

The center is an actual integral smooth zero. On a literal congruence coset
around it, one coordinate stays a unit, the chosen first partial and Hessian
minor retain their exact nonzero norms, and the Hessian rank stays at least
eight. The row and column selections are separate: no principal-minor claim
is made. Only the center is asserted to be a zero of the cubic; the entire
coset need not consist of zeros.

The neighborhood and normalization steps are proved. The final existence
theorem retains precisely the explicit Pleasants local-solubility argument.
-/

noncomputable section

namespace CubicTenVariables.PadicLocalization

open MvPolynomial HessianTheorem11 RationalHessianMinor

/-- Coercing the literal integral congruence-class point gives exactly the
field-valued point used by the proved neighborhood theorem. -/
theorem coe_integral_coset (p : ℕ) [Fact p.Prime] {n : ℕ}
    (ξ z : Fin n → ℤ_[p]) (M : ℕ) :
    (fun i => ((ξ + (p : ℤ_[p]) ^ M • z) i : ℚ_[p])) =
      (fun i => (ξ i : ℚ_[p])) + (p : ℚ_[p]) ^ M • (fun i => (z i : ℚ_[p])) := by
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, PadicInt.coe_add,
    PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast]

/-- A supplied integral point with a nonzero partial and a nonzero actual
Hessian minor admits a literal congruence class retaining both norms. This
lemma assumes neither local solubility nor homogeneity. -/
theorem exists_constant_norm_coset (p : ℕ) [Fact p.Prime] {n r : ℕ}
    (F : MvPolynomial (Fin n) ℚ) (ξ : Fin n → ℤ_[p]) (i j : Fin n)
    (hj : ξ j = 1)
    (hi : eval₂ (algebraMap ℚ ℚ_[p]) (fun k => (ξ k : ℚ_[p])) (pderiv i F) ≠ 0)
    (rows cols : Fin r → Fin n)
    (hD : eval₂ (algebraMap ℚ ℚ_[p]) (fun k => (ξ k : ℚ_[p]))
      (hessianMinor F rows cols) ≠ 0) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ z : Fin n → ℤ_[p],
      let η := ξ + (p : ℤ_[p]) ^ M • z
      IsUnit (η j) ∧
      ‖eval₂ (algebraMap ℚ ℚ_[p]) (fun k => (η k : ℚ_[p])) (pderiv i F)‖ =
        ‖eval₂ (algebraMap ℚ ℚ_[p]) (fun k => (ξ k : ℚ_[p])) (pderiv i F)‖ ∧
      ‖eval₂ (algebraMap ℚ ℚ_[p]) (fun k => (η k : ℚ_[p])) (hessianMinor F rows cols)‖ =
        ‖eval₂ (algebraMap ℚ ℚ_[p]) (fun k => (ξ k : ℚ_[p])) (hessianMinor F rows cols)‖ ∧
      eval₂ (algebraMap ℚ ℚ_[p]) (fun k => (η k : ℚ_[p])) (pderiv i F) ≠ 0 ∧
      eval₂ (algebraMap ℚ ℚ_[p]) (fun k => (η k : ℚ_[p])) (hessianMinor F rows cols) ≠ 0 ∧
      r ≤ (hessian (map (algebraMap ℚ ℚ_[p]) F) (fun k => (η k : ℚ_[p]))).rank := by
  let x : Fin n → ℚ_[p] := fun k => (ξ k : ℚ_[p])
  let P := map (algebraMap ℚ ℚ_[p]) (pderiv i F)
  let D := map (algebraMap ℚ ℚ_[p]) (hessianMinor F rows cols)
  have hP : eval x P ≠ 0 := by simpa only [P, eval_map] using hi
  have hDx : eval x D ≠ 0 := by simpa only [D, eval_map] using hD
  have hx : ∀ k, ‖x k‖ ≤ 1 := fun k => (ξ k).property
  have hxj : ‖x j‖ = 1 := by
    change ‖(ξ j : ℚ_[p])‖ = 1
    rw [hj, PadicInt.coe_one, norm_one]
  obtain ⟨U, hU, hxU, hnorms⟩ :=
    PadicPolynomialNeighborhood.exists_open_integral_constant_norm_neighborhood
      P D x hP hDx hx j hxj
  obtain ⟨M, hM, hcoset⟩ :=
    PadicCongruenceNeighborhood.exists_power_coset_subset p x U hU hxU
  refine ⟨M, hM, ?_⟩
  intro z
  let η := ξ + (p : ℤ_[p]) ^ M • z
  have hηU : (fun k => (η k : ℚ_[p])) ∈ U := by
    rw [show (fun k => (η k : ℚ_[p])) =
      x + (p : ℚ_[p]) ^ M • (fun k => (z k : ℚ_[p])) from coe_integral_coset p ξ z M]
    exact hcoset z
  have hη := hnorms _ hηU
  have hunit : IsUnit (η j) := by
    apply PadicInt.isUnit_iff.mpr
    exact hη.2.1
  have hpnorm :
      ‖eval₂ (algebraMap ℚ ℚ_[p]) (fun k => (η k : ℚ_[p])) (pderiv i F)‖ =
        ‖eval₂ (algebraMap ℚ ℚ_[p]) x (pderiv i F)‖ := by
    simpa only [P, eval_map] using hη.2.2.1
  have hdnorm :
      ‖eval₂ (algebraMap ℚ ℚ_[p]) (fun k => (η k : ℚ_[p])) (hessianMinor F rows cols)‖ =
        ‖eval₂ (algebraMap ℚ ℚ_[p]) x (hessianMinor F rows cols)‖ := by
    simpa only [D, eval_map] using hη.2.2.2
  have hpη : eval₂ (algebraMap ℚ ℚ_[p]) (fun k => (η k : ℚ_[p])) (pderiv i F) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hpnorm]
    exact norm_ne_zero_iff.mpr hi
  have hdη : eval₂ (algebraMap ℚ ℚ_[p]) (fun k => (η k : ℚ_[p]))
      (hessianMinor F rows cols) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hdnorm]
    exact norm_ne_zero_iff.mpr hD
  exact ⟨hunit, hpnorm, hdnorm, hpη, hdη,
    size_le_rank_of_eval₂_ne_zero F rows cols _ hdη⟩

set_option maxHeartbeats 800000 in
/-- Conditional only on the displayed Pleasants theorem, a rational
anisotropic cubic in ten variables has a primitive smooth integral zero
and a literal integral congruence class retaining a rank-sized nonzero
Hessian minor of size at least eight. -/
theorem exists_primitive_high_rank_localization
    (pleasants : Literature.Pleasants1971Theorem2Qp)
    (F : AnisotropicCubic 10) (p : ℕ) [Fact p.Prime] :
    ∃ (ξ : Fin 10 → ℤ_[p]) (i j : Fin 10) (r : ℕ)
      (rows cols : Fin r → Fin 10) (M : ℕ),
      ξ j = 1 ∧
      eval₂ (algebraMap ℚ ℚ_[p]) (fun k => (ξ k : ℚ_[p])) F.polynomial = 0 ∧
      eval₂ (algebraMap ℚ ℚ_[p]) (fun k => (ξ k : ℚ_[p])) (pderiv i F.polynomial) ≠ 0 ∧
      8 ≤ r ∧
      r = (hessian (map (algebraMap ℚ ℚ_[p]) F.polynomial) (fun k => (ξ k : ℚ_[p]))).rank ∧
      1 ≤ M ∧
      eval₂ (algebraMap ℚ ℚ_[p]) (fun k => (ξ k : ℚ_[p]))
        (hessianMinor F.polynomial rows cols) ≠ 0 ∧
      ∀ z : Fin 10 → ℤ_[p],
        let η := ξ + (p : ℤ_[p]) ^ M • z
        IsUnit (η j) ∧
        ‖eval₂ (algebraMap ℚ ℚ_[p]) (fun k => (η k : ℚ_[p])) (pderiv i F.polynomial)‖ =
          ‖eval₂ (algebraMap ℚ ℚ_[p]) (fun k => (ξ k : ℚ_[p])) (pderiv i F.polynomial)‖ ∧
        ‖eval₂ (algebraMap ℚ ℚ_[p]) (fun k => (η k : ℚ_[p]))
          (hessianMinor F.polynomial rows cols)‖ =
          ‖eval₂ (algebraMap ℚ ℚ_[p]) (fun k => (ξ k : ℚ_[p]))
            (hessianMinor F.polynomial rows cols)‖ ∧
        eval₂ (algebraMap ℚ ℚ_[p]) (fun k => (η k : ℚ_[p])) (pderiv i F.polynomial) ≠ 0 ∧
        eval₂ (algebraMap ℚ ℚ_[p]) (fun k => (η k : ℚ_[p]))
          (hessianMinor F.polynomial rows cols) ≠ 0 ∧
        8 ≤ (hessian (map (algebraMap ℚ ℚ_[p]) F.polynomial) (fun k => (η k : ℚ_[p]))).rank := by
  obtain ⟨x, hx, hFx, hsmooth, hrank⟩ := HighRankLocalPoint.padic_high_rank_zero pleasants F p
  obtain ⟨c, hc, ξ, hscale, ⟨j, hj⟩, hFξ, ⟨i, hi⟩, hξrank⟩ :=
    PadicPrimitive.exists_integral_smooth_zero_preserving_hessian_rank
      p F.polynomial F.homogeneous x hx hFx hsmooth
  let H := hessian (map (algebraMap ℚ ℚ_[p]) F.polynomial) (fun k => (ξ k : ℚ_[p]))
  have hr : 8 ≤ H.rank := hξrank ▸ hrank
  obtain ⟨rows, cols, hminor⟩ := MatrixRankMinors.exists_rank_minor H
  have hD : eval₂ (algebraMap ℚ ℚ_[p]) (fun k => (ξ k : ℚ_[p]))
      (hessianMinor F.polynomial rows cols) ≠ 0 := by
    rw [eval₂_hessianMinor]
    exact hminor
  obtain ⟨M, hM, hcoset⟩ := exists_constant_norm_coset p F.polynomial ξ i j hj hi rows cols hD
  refine ⟨ξ, i, j, H.rank, rows, cols, M, hj, hFξ, hi, hr, rfl, hM, hD, ?_⟩
  intro z
  obtain ⟨hunit, hp, hd, hpne, hdne, hrη⟩ := hcoset z
  exact ⟨hunit, hp, hd, hpne, hdne, hr.trans hrη⟩

end CubicTenVariables.PadicLocalization
