import CubicTenVariables.PrimeLocalizationData
import CubicTenVariables.IntegralZeroPatch
import CubicTenVariables.PolynomialResidueEvaluation
import CubicTenVariables.WeightedCounting
import CubicTenVariables.SmoothResidueLifting

/-! The actual finite residue restriction selected by prime-local data.
It is exactly the reduction of the chosen unit orbit, and a fixed derivative
remains nonzero modulo one fixed prime power throughout that restriction. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables
open MvPolynomial PadicUnitOrbit

namespace PadicUnitOrbit
variable (p : ℕ) [Fact p.Prime] {n : ℕ}

/-- The unit orbit is a union of full congruence classes at its defining
level, so membership depends only on reduction at that level. -/
theorem mem_unitOrbit_of_reduction_eq (ξ : Fin n → ℤ_[p]) (M : ℕ)
    (x y : Fin n → ℤ_[p]) (hx : x ∈ unitOrbit p ξ M)
    (hxy : ∀ j, PadicInt.toZModPow M (y j) = PadicInt.toZModPow M (x j)) :
    y ∈ unitOrbit p ξ M := by
  obtain ⟨u,z,hz,huz⟩ := hx
  have hxcos : x ∈ coset p ((u:ℤ_[p]) • ξ) M := by
    rw [← unit_smul_coset]
    exact ⟨z,hz,huz⟩
  have hycos : y ∈ coset p ((u:ℤ_[p]) • ξ) M :=
    (mem_coset_iff p _ y M).mpr fun j =>
      (hxy j).trans ((mem_coset_iff p _ x M).mp hxcos j)
  rw [← unit_smul_coset] at hycos
  obtain ⟨z',hz',huz'⟩ := hycos
  exact ⟨u,z',hz',huz'⟩

end PadicUnitOrbit

namespace PrimeLocalizationData
variable {p : ℕ} [Fact p.Prime] {F : MvPolynomial (Fin 10) ℤ}

def residueSet (D : PrimeLocalizationData p F) : Set (Fin 10 → ZMod (p^D.modulusExponent)) :=
  (fun z : Fin 10 → ℤ_[p] => fun i => PadicInt.toZModPow D.modulusExponent (z i)) ''
    unitOrbit p D.center D.modulusExponent

theorem reduction_mem_residueSet_iff (D : PrimeLocalizationData p F)
    (z : Fin 10 → ℤ_[p]) :
    (fun i => PadicInt.toZModPow D.modulusExponent (z i)) ∈ D.residueSet ↔
      z ∈ unitOrbit p D.center D.modulusExponent := by
  constructor
  · rintro ⟨y,hy,heq⟩
    exact mem_unitOrbit_of_reduction_eq p D.center D.modulusExponent y z hy
      (fun j => (congrFun heq j).symm)
  · intro hz
    exact ⟨z,hz,rfl⟩

theorem integerResidue_mem_iff (D : PrimeLocalizationData p F) (z : Fin 10 → ℤ) :
    integerResidue (p^D.modulusExponent) z ∈ D.residueSet ↔
      (fun i => (z i:ℤ_[p])) ∈ unitOrbit p D.center D.modulusExponent := by
  simpa only [integerResidue,map_intCast] using
    D.reduction_mem_residueSet_iff (fun i => (z i:ℤ_[p]))

/-- One positive prime-power level detects the nonzero selected derivative
at every point of the whole unit orbit. It is fixed before future moduli. -/
theorem exists_uniform_partial_reduction_ne_zero (D : PrimeLocalizationData p F) :
    ∃ t : ℕ, 1 ≤ t ∧ ∀ z ∈ unitOrbit p D.center D.modulusExponent,
      PadicInt.toZModPow t (eval₂ (Int.castRingHom ℤ_[p]) z (pderiv D.partialIndex F)) ≠ 0 := by
  let d : ℤ_[p] := eval₂ (Int.castRingHom ℤ_[p]) D.center (pderiv D.partialIndex F)
  have hd : d ≠ 0 := by
    intro hd
    apply D.partial_ne_zero
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
  have hnorm := (D.orbit_geometry z hz).2.1
  have hzle : ‖((eval₂ (Int.castRingHom ℤ_[p]) z (pderiv D.partialIndex F):ℤ_[p]):ℚ_[p])‖ ≤
      ((p:ℝ)^t)⁻¹ := by
    simpa only [map_zero,PadicInt.coe_zero,sub_zero] using
      (PadicResidueNorm.toZModPow_eq_iff_norm_coe_sub_le t
        (eval₂ (Int.castRingHom ℤ_[p]) z (pderiv D.partialIndex F)) 0).mp
          (by simpa only [map_zero] using hzero)
  rw [IntegralZeroPatch.coe_eval₂_int,hnorm] at hzle
  have hdle : ‖(d:ℚ_[p]) - (0:ℚ_[p])‖ ≤ ((p:ℝ)^t)⁻¹ := by
    simpa only [d,IntegralZeroPatch.coe_eval₂_int,sub_zero] using hzle
  have heq := (PadicResidueNorm.toZModPow_eq_iff_norm_coe_sub_le t d 0).mpr hdle
  exact ht (by simpa only [map_zero] using heq)

/-- Literal integer representatives in the allowed residue set inherit
the same fixed nondivisibility bound. -/
theorem exists_uniform_partial_not_dvd (D : PrimeLocalizationData p F) :
    ∃ t : ℕ, 1 ≤ t ∧ ∀ z : Fin 10 → ℤ,
      integerResidue (p^D.modulusExponent) z ∈ D.residueSet →
      ¬ ((p^t:ℕ):ℤ) ∣ eval z (pderiv D.partialIndex F) := by
  obtain ⟨t,ht,hpartial⟩ := D.exists_uniform_partial_reduction_ne_zero
  refine ⟨t,ht,?_⟩
  intro z hz hdvd
  apply hpartial (fun i => (z i:ℤ_[p])) ((D.integerResidue_mem_iff z).mp hz)
  rw [PolynomialResidueEvaluation.toZModPow_eval₂_int]
  simp only [map_intCast]
  rw [← SmoothResidueLifting.cast_eval_int]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd

end PrimeLocalizationData
end CubicTenVariables
