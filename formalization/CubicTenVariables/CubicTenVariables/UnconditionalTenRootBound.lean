import CubicTenVariables.TenCubicPointwiseBound
import CubicTenVariables.PrimePowerRootBoundOfPointwise

/-! The actual unrestricted ten-variable prime-power root bound, now proved
by finite differencing and the finite root-density identity. Neither Bernert
nor global singular-series convergence is an input. The constant precedes
all primes and all levels, including level zero and primes two and three. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.UnconditionalTenRootBound
open MvPolynomial

/-- The no-integer-zero branch of the actual uniform root estimate. -/
theorem of_no_integer_zero (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hzero : ¬ HasIntegerZero F) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      ∀ s : ℕ,
        (Finset.univ.filter fun z : Fin 10 → ZMod (p^s) =>
          eval₂ (Int.castRingHom (ZMod (p^s))) z F = 0).card ≤ C*p^(9*s) := by
  obtain ⟨C, _, hbound⟩ := TenCubicPointwiseBound.exists_complete_bound F hF hzero
  exact PrimePowerRootBoundOfPointwise.exists_uniform_root_bound F hbound

/-- The exact anisotropy formulation consumed by the residue and Smith
estimates. No estimate is supplied by the caller. -/
theorem of_anisotropic (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : HessianTheorem11.Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      ∀ s : ℕ,
        (Finset.univ.filter fun z : Fin 10 → ZMod (p^s) =>
          eval₂ (Int.castRingHom (ZMod (p^s))) z F = 0).card ≤ C*p^(9*s) := by
  apply of_no_integer_zero F hF
  intro hz
  obtain ⟨x, hx, hFx⟩ := hasRationalZero_of_hasIntegerZero hz
  exact hx (hA x hFx)

/-- Absolute convergence of the actual higher-prime-power subseries.
The prime-modulus contribution and positivity are not asserted here. -/
theorem summable_higher_prime_powers (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hzero : ¬ HasIntegerZero F) :
    Summable (fun pk : Nat.Primes × ℕ =>
      ‖singularSeriesTerm F (pk.1.val ^ (pk.2+2))‖) := by
  obtain ⟨C, _, hbound⟩ := TenCubicPointwiseBound.exists_complete_bound F hF hzero
  apply PrimePowerSeriesConvergence.cubic_higher_prime_powers F (by omega)
    (C := C) (ε := 0) (by norm_num)
  intro p hp k _hk
  convert hbound (p^k) (pow_pos hp.pos k) using 1 <;> norm_num

end CubicTenVariables.UnconditionalTenRootBound
