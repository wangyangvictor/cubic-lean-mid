import CubicTenVariables.ModularMinorKernelGcdBound
import CubicTenVariables.PrimeLocalizationResidues
import CubicTenVariables.HessianKernelCRT

/-! A uniform actual modular Hessian-kernel bound on the chosen local
unit orbit. Fixed nonzero minor norm supplies a uniform determinant-gcd
bound, and at least eight selected columns leave at most two free ones. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables
open MvPolynomial HessianTheorem11 RationalHessianMinor PadicUnitOrbit
open scoped BigOperators
namespace PrimeLocalizationData
variable {p : ℕ} [Fact p.Prime] {F : MvPolynomial (Fin 10) ℤ}

/-- One positive prime-power level detects the nonzero selected Hessian minor
at every point of the whole unit orbit. It is fixed before future moduli. -/
theorem exists_uniform_minor_reduction_ne_zero (D : PrimeLocalizationData p F) :
    ∃ t : ℕ, 1 ≤ t ∧ ∀ z ∈ unitOrbit p D.center D.modulusExponent,
      PadicInt.toZModPow t (eval₂ (Int.castRingHom ℤ_[p]) z (hessianMinor F D.rows D.cols)) ≠ 0 := by
  let d : ℤ_[p] := eval₂ (Int.castRingHom ℤ_[p]) D.center (hessianMinor F D.rows D.cols)
  have hd : d ≠ 0 := by
    intro hd
    apply D.minor_ne_zero
    rw [← IntegralZeroPatch.coe_eval₂_int]
    change (d:ℚ_[p]) = 0
    rw [hd,PadicInt.coe_zero]
  have hex : ∃ t : ℕ, PadicInt.toZModPow t d ≠ 0 := by
    by_contra h
    push_neg at h
    apply hd
    apply PadicInt.ext_of_toZModPow.mp
    intro t
    rw [h t,map_zero]
  obtain ⟨t,ht⟩ := hex
  have htpos : 1 ≤ t := by
    by_contra hh
    have ht0 : t = 0 := by omega
    subst t
    haveI : Subsingleton (ZMod (p^0)) := by
      simpa using (inferInstance : Subsingleton (ZMod 1))
    exact ht (Subsingleton.elim _ _)
  refine ⟨t,htpos,?_⟩
  intro z hz hzero
  have hnorm := (D.orbit_geometry z hz).2.2.1
  have hzle : ‖((eval₂ (Int.castRingHom ℤ_[p]) z (hessianMinor F D.rows D.cols):ℤ_[p]):ℚ_[p])‖ ≤
      ((p:ℝ)^t)⁻¹ := by
    simpa only [map_zero,PadicInt.coe_zero,sub_zero] using
      (PadicResidueNorm.toZModPow_eq_iff_norm_coe_sub_le t
        (eval₂ (Int.castRingHom ℤ_[p]) z (hessianMinor F D.rows D.cols)) 0).mp
          (by simpa only [map_zero] using hzero)
  rw [IntegralZeroPatch.coe_eval₂_int,hnorm] at hzle
  have hdle : ‖(d:ℚ_[p]) - (0:ℚ_[p])‖ ≤ ((p:ℝ)^t)⁻¹ := by
    simpa only [d,IntegralZeroPatch.coe_eval₂_int,sub_zero] using hzle
  have heq := (PadicResidueNorm.toZModPow_eq_iff_norm_coe_sub_le t d 0).mpr hdle
  exact ht (by simpa only [map_zero] using heq)

/-- Literal integer representatives in the allowed residue set inherit
the same fixed nondivisibility bound. -/
theorem exists_uniform_minor_not_dvd (D : PrimeLocalizationData p F) :
    ∃ t : ℕ, 1 ≤ t ∧ ∀ z : Fin 10 → ℤ,
      integerResidue (p^D.modulusExponent) z ∈ D.residueSet →
      ¬ ((p^t:ℕ):ℤ) ∣ eval z (hessianMinor F D.rows D.cols) := by
  obtain ⟨t,ht,hminor⟩ := D.exists_uniform_minor_reduction_ne_zero
  refine ⟨t,ht,?_⟩
  intro z hz hdvd
  apply hminor (fun i => (z i:ℤ_[p])) ((D.integerResidue_mem_iff z).mp hz)
  rw [PolynomialResidueEvaluation.toZModPow_eval₂_int]
  simp only [map_intCast]
  rw [← SmoothResidueLifting.cast_eval_int]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd


/-- A fixed failure of prime-power divisibility bounds all subsequent
gcds with powers of the same prime. -/
theorem gcd_primePower_le_of_not_dvd (T t : ℕ) (a : ℤ)
    (ha : ¬ ((p^T : ℕ):ℤ) ∣ a) :
    Nat.gcd a.natAbs (p^t) ≤ p^T := by
  obtain ⟨k,hkt,hg⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp
    (Nat.gcd_dvd_right a.natAbs (p^t))
  have hk : k < T := by
    by_contra hh
    apply ha
    apply Int.natCast_dvd.mpr
    apply (pow_dvd_pow p (le_of_not_gt hh)).trans
    rw [←hg]
    exact Nat.gcd_dvd_left _ _
  rw [hg]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).one_le hk.le

/-- A uniform natural constant controls the actual reduced integer
Hessian kernel throughout the selected congruence restriction. -/
theorem exists_uniform_integer_kernel_bound (D : PrimeLocalizationData p F) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ y : Fin 10 → ℤ,
      integerResidue (p^D.modulusExponent) y ∈ D.residueSet → ∀ t : ℕ,
        Nat.card {h : Fin 10 → ZMod (p^t) //
          ((hessian F y).map (Int.castRingHom (ZMod (p^t)))).mulVec h = 0} ≤
          C*p^(2*t) := by
  obtain ⟨T,hT,hminor⟩ := D.exists_uniform_minor_not_dvd
  let C := (p^T)^D.minorSize
  have hrows : Function.Injective D.rows := by
    apply SelectedGradientCoordinates.rows_injective_of_submatrix_det_ne_zero
      (hessian (map (Int.castRingHom ℚ_[p]) F) (fun i => (D.center i:ℚ_[p]))) D.rows D.cols
    rw [←eval₂_hessianMinor]
    exact D.minor_ne_zero
  let rows : Fin D.minorSize ↪ Fin 10 := ⟨D.rows,hrows⟩
  let cols : Fin D.minorSize ↪ Fin 10 := ⟨D.cols,D.cols_injective⟩
  refine ⟨C,one_le_pow₀ (one_le_pow₀ (Fact.out : p.Prime).one_le),?_⟩
  intro y hy t
  have heval : eval y (hessianMinor F D.rows D.cols) =
      ((hessian F y).submatrix D.rows D.cols).det := by
    change eval₂ (RingHom.id ℤ) y _ = _
    rw [eval₂_hessianMinor,map_id]
  have hdet : ¬ ((p^T:ℕ):ℤ) ∣ ((hessian F y).submatrix D.rows D.cols).det := by
    rw [←heval]
    exact hminor y hy
  have hg := gcd_primePower_le_of_not_dvd T t _ hdet
  have hker := ModularMinorKernelGcdBound.natCard_kernel_le_minor_gcd
    (hessian F y) rows cols (p^t)
  have hsize : 10-D.minorSize ≤ 2 := by have := D.minorSize_ge_eight; omega
  calc
    _ ≤ (p^t)^(10-D.minorSize) *
        (Nat.gcd ((hessian F y).submatrix D.rows D.cols).det.natAbs (p^t))^D.minorSize := hker
    _ ≤ (p^t)^2 * C := Nat.mul_le_mul
      (Nat.pow_le_pow_right (one_le_pow₀ (Fact.out : p.Prime).one_le) hsize)
      (Nat.pow_le_pow_left hg _)
    _ = C*p^(2*t) := by rw [←pow_mul,mul_comm t 2,mul_comm]

/-- The same estimate in the exact residue-Hessian form used by the
quadratic terminal bound, with one real constant before all points/levels. -/
theorem exists_uniform_residue_kernel_bound (D : PrimeLocalizationData p F) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ y : Fin 10 → ℤ,
      integerResidue (p^D.modulusExponent) y ∈ D.residueSet → ∀ t : ℕ,
        (Nat.card {h : Fin 10 → ZMod (p^t) //
          (hessian (map (Int.castRingHom (ZMod (p^t))) F)
            (fun i => (y i:ZMod (p^t)))).mulVec h = 0} : ℝ) ≤
          C*(p:ℝ)^(2*t) := by
  obtain ⟨C,hC,hker⟩ := D.exists_uniform_integer_kernel_bound
  refine ⟨C,by exact_mod_cast hC,?_⟩
  intro y hy t
  have h := hker y hy t
  rw [HessianKernelCRT.hessian_map_eval] at h
  exact_mod_cast h

end PrimeLocalizationData
end CubicTenVariables
