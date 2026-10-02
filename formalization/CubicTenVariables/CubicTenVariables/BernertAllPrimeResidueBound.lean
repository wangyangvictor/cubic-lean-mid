import CubicTenVariables.UnconditionalTenRootBound
import CubicTenVariables.CubicAllPrimeResidueBound

/-! The complete prime-power residue-class bound, with the unrestricted
estimate supplied by finite differencing and the finite root-density identity and the finite exceptional primes are handled inside
one constant. Composite-modulus assembly is a separate obligation. -/

noncomputable section
namespace CubicTenVariables.BernertAllPrimeResidueBound
open MvPolynomial

/-- One fixed exceptional integer and one constant control all prime-power
residue classes. No root-count, rank, or exceptional-prime estimate is left
as a separate input. No unproved literature premise remains. -/
theorem exists_all_prime_residue_bound
    
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : HessianTheorem11.Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ B : ℕ, 1 ≤ B ∧
      ∀ (p : ℕ) (hp : p.Prime),
        letI : Fact p.Prime := ⟨hp⟩
        ∀ (k : Fin 10 → ℤ), (p : ℤ) ∣ eval k F →
          ∀ (r : ℕ) (hr : 2 ≤ r),
            (Finset.univ.filter fun z : Fin 10 → ZMod (p^r) =>
              (∀ i, SmoothResidueIteration.toPrime p r (by omega) (z i) = (k i : ZMod p)) ∧
              eval₂ (Int.castRingHom (ZMod (p^r))) z F = 0).card ≤
                B*(r-1)*p^(9*(r-1) +
                  if (p : ℤ) ∣ D then 0 else
                  if (∀ i, (p : ℤ) ∣ k i) then 2
                  else if (∀ i, (p : ℤ) ∣ eval k (pderiv i F)) then 1 else 0) := by
  obtain ⟨D,hD,hall⟩ := CubicAllPrimeResidueBound.exists_all_prime_residue_bound F hF hA
  obtain ⟨C,hC,hU⟩ := UnconditionalTenRootBound.of_anisotropic  F hF hA
  obtain ⟨B,hB,hbound⟩ := hall C hC hU
  exact ⟨D,hD,B,hB,hbound⟩

end CubicTenVariables.BernertAllPrimeResidueBound
