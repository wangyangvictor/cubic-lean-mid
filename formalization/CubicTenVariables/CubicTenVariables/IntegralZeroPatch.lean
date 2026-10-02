import CubicTenVariables.ZeroPatch
import CubicTenVariables.PadicUnitOrbit
import CubicTenVariables.PadicResidueNorm
import CubicTenVariables.PadicCongruenceNeighborhood

/-!
# Exact integral zero patches inside a prescribed p-adic coset

An actual integral smooth zero supplies a fixed congruence coset of the
remaining coordinates, every point of which lifts to an actual integral
zero in the original prescribed coset. The selected derivative need only
be nonzero in Q_p, not a unit. No homogeneity, Hensel-lifting, or local-density
input is introduced. All primes and zero-dimensional parameter spaces are
included.
-/

noncomputable section
namespace CubicTenVariables.IntegralZeroPatch

open MvPolynomial

variable (p : ℕ) [Fact p.Prime]

/-- Literal integral polynomial evaluation commutes with its field coercion. -/
theorem coe_eval₂_int {ι : Type*} (F : MvPolynomial ι ℤ) (z : ι → ℤ_[p]) :
    ((eval₂ (Int.castRingHom ℤ_[p]) z F : ℤ_[p]) : ℚ_[p]) =
      eval₂ (Int.castRingHom ℚ_[p]) (fun j => (z j : ℚ_[p])) F := by
  have hcomp : (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]).comp
      (Int.castRingHom ℤ_[p]) = Int.castRingHom ℚ_[p] := by
    ext a
    simp
  change PadicInt.Coe.ringHom (eval₂ (Int.castRingHom ℤ_[p]) z F) = _
  rw [eval₂_comp_left, hcomp]
  rfl

/-- A sufficiently close field point is an actual integral point of the
prescribed literal congruence coset. The ordinary open ball suffices. -/
theorem exists_integral_coset_lift_of_mem_ball {n : ℕ}
    (ξ : Fin n → ℤ_[p]) (M : ℕ) (z : Fin n → ℚ_[p])
    (hz : z ∈ Metric.ball (fun j => (ξ j : ℚ_[p])) (((p : ℝ) ^ M)⁻¹)) :
    ∃ zI : Fin n → ℤ_[p],
      (fun j => (zI j : ℚ_[p])) = z ∧ zI ∈ PadicUnitOrbit.coset p ξ M := by
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  have hρ : ((p : ℝ) ^ M)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hp)
  have hdist : ‖z - (fun j => (ξ j : ℚ_[p]))‖ < ((p : ℝ) ^ M)⁻¹ := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hzbound : ∀ j, ‖z j‖ ≤ 1 := by
    intro j
    have hdiff : ‖z j - (ξ j : ℚ_[p])‖ ≤ 1 :=
      (norm_le_pi_norm (z - (fun k => (ξ k : ℚ_[p]))) j).trans
        ((le_of_lt hdist).trans hρ)
    calc
      ‖z j‖ = ‖(z j - (ξ j : ℚ_[p])) + (ξ j : ℚ_[p])‖ := by rw [sub_add_cancel]
      _ ≤ max ‖z j - (ξ j : ℚ_[p])‖ ‖(ξ j : ℚ_[p])‖ := Padic.nonarchimedean _ _
      _ ≤ 1 := max_le hdiff (ξ j).property
  let zI : Fin n → ℤ_[p] := fun j => ⟨z j, hzbound j⟩
  refine ⟨zI, rfl, ?_⟩
  apply (PadicUnitOrbit.mem_coset_iff p ξ zI M).mpr
  apply (PadicResidueNorm.pi_toZModPow_eq_iff_norm_coe_sub_le M zI ξ).mpr
  exact le_of_lt hdist

/-- Every parameter in one fixed integral congruence coset lifts to an
exact integral polynomial zero in the original prescribed coset. The
exponent is chosen before any parameter or future residue modulus. -/
theorem exists_integral_zero_patch {m : ℕ}
    (F : MvPolynomial (Fin (m + 1)) ℤ) (i : Fin (m + 1))
    (ξ : Fin (m + 1) → ℤ_[p])
    (hzero : eval₂ (Int.castRingHom ℚ_[p]) (fun j => (ξ j : ℚ_[p])) F = 0)
    (hpartial : eval₂ (Int.castRingHom ℚ_[p]) (fun j => (ξ j : ℚ_[p])) (pderiv i F) ≠ 0)
    (M : ℕ) :
    ∃ K : ℕ, max M 1 ≤ K ∧
      ∀ y ∈ PadicUnitOrbit.coset p (i.removeNth ξ) K,
        ∃ z ∈ PadicUnitOrbit.coset p ξ M,
          eval₂ (Int.castRingHom ℤ_[p]) z F = 0 ∧ i.removeNth z = y := by
  let Fq := map (Int.castRingHom ℚ_[p]) F
  let x : Fin (m + 1) → ℚ_[p] := fun j => (ξ j : ℚ_[p])
  let U := Metric.ball x (((p : ℝ) ^ M)⁻¹)
  have hFx : eval x Fq = 0 := by simpa only [Fq, eval_map] using hzero
  have hi : eval x (pderiv i Fq) ≠ 0 := by
    simpa only [Fq, pderiv_map, eval_map] using hpartial
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hρpos : 0 < ((p : ℝ) ^ M)⁻¹ := by positivity
  have hxU : x ∈ U := Metric.mem_ball_self hρpos
  obtain ⟨V, hV, hxV, _, hpatch⟩ :=
    ZeroPatch.exists_open_zero_patch Fq i x hFx hi U Metric.isOpen_ball hxU
  obtain ⟨K₀, hK₀, hparam⟩ := PadicCongruenceNeighborhood.exists_power_coset_subset
    p (i.removeNth x) V hV hxV
  let K := max M K₀
  refine ⟨K, max_le (le_max_left _ _) (hK₀.trans (le_max_right _ _)), ?_⟩
  intro y hy
  have hy₀ : y ∈ PadicUnitOrbit.coset p (i.removeNth ξ) K₀ :=
    PadicUnitOrbit.coset_mono p (i.removeNth ξ) (le_max_right M K₀) hy
  obtain ⟨t, ht⟩ := hy₀
  have hcasty : (fun j => (y j : ℚ_[p])) =
      i.removeNth x + (p : ℚ_[p]) ^ K₀ • (fun j => (t j : ℚ_[p])) := by
    rw [← ht]
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, PadicInt.coe_add,
      PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast]
    rfl
  have hyV : (fun j => (y j : ℚ_[p])) ∈ V := by
    rw [hcasty]
    exact hparam t
  obtain ⟨z, hzU, hFz, _, hremove⟩ := hpatch _ hyV
  obtain ⟨zI, hcastz, hzI⟩ := exists_integral_coset_lift_of_mem_ball p ξ M z hzU
  refine ⟨zI, hzI, ?_, ?_⟩
  · apply PadicInt.coe_eq_zero.mp
    rw [coe_eval₂_int, hcastz]
    simpa only [Fq, eval_map] using hFz
  · funext j
    apply PadicInt.ext
    have hzj := congrFun hcastz (i.succAbove j)
    have hyj := congrFun hremove j
    exact hzj.trans hyj

end CubicTenVariables.IntegralZeroPatch
