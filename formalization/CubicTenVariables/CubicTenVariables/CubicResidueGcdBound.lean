import CubicTenVariables.BernertAllPrimeResidueBound
import CubicTenVariables.SquarefreeResidueFactors

/-!
# Local cubic residue bounds with the manuscript's gcd factors

The exceptional-prime defect is weakened to the two ordinary coordinate
gcd factors. No prime is removed from the manuscript's squarefree modulus.
-/

noncomputable section
namespace CubicTenVariables.CubicResidueGcdBound
open MvPolynomial
open SquarefreeResidueFactors

/-- Divisibility of the coordinates forces divisibility of every first
partial of a homogeneous cubic, including at primes two and three. -/
theorem dvd_gradient_of_dvd_coordinates {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (p : ℕ) (k : Fin n → ℤ) (hk : ∀ i, (p : ℤ) ∣ k i) :
    ∀ i, (p : ℤ) ∣ eval k (pderiv i F) := by
  intro i
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [SmoothResidueLifting.cast_eval_int, eval₂_eq_eval_map]
  have hz : (fun j => (k j : ZMod p)) = 0 := by
    funext j
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hk j)
  rw [hz]
  exact HessianTheorem11.eval_origin_of_positive_homogeneous
    (hF.pderiv.map (Int.castRingHom (ZMod p))) (by norm_num)

/-- The two ordinary gcd factors dominate the local defect, even at an
exceptional prime. The exceptional integer does not alter either gcd. -/
theorem prime_defect_le_vectorGcd {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (p : ℕ) (hp : p.Prime) (D : ℤ) (k : Fin n → ℤ) :
    p^(if (p : ℤ) ∣ D then 0 else
      if (∀ i, (p : ℤ) ∣ k i) then 2
      else if (∀ i, (p : ℤ) ∣ eval k (pderiv i F)) then 1 else 0) ≤
      vectorGcd p (fun i => eval k (pderiv i F)) * vectorGcd p k := by
  by_cases hpD : (p : ℤ) ∣ D
  · simp only [if_pos hpD, pow_zero]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
      (vectorGcd_pos p hp.pos _).ne' (vectorGcd_pos p hp.pos _).ne')
  · simp only [if_neg hpD]
    by_cases hk : ∀ i, (p : ℤ) ∣ k i
    · have hg := dvd_gradient_of_dvd_coordinates F hF p k hk
      simp [vectorGcd_prime p hp, hk, hg, pow_two]
    · by_cases hg : ∀ i, (p : ℤ) ∣ eval k (pderiv i F)
      · simp [vectorGcd_prime p hp, hk, hg]
      · simp [vectorGcd_prime p hp, hk, hg]

/-- One common constant supplies unrestricted and prescribed-prime-class
bounds with the literal vector gcds, without an unproved literature
premise. Constants precede all primes, levels and centers. -/
theorem exists_uniform_local_gcd_bound
    
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : HessianTheorem11.Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ K : ℕ, 1 ≤ K ∧
      (∀ (p : ℕ) (hp : p.Prime),
        letI : Fact p.Prime := ⟨hp⟩
        ∀ s : ℕ,
          (Finset.univ.filter fun z : Fin 10 → ZMod (p^s) =>
            eval₂ (Int.castRingHom (ZMod (p^s))) z F = 0).card ≤ K*p^(9*s)) ∧
      (∀ (p : ℕ) (hp : p.Prime),
        letI : Fact p.Prime := ⟨hp⟩
        ∀ (k : Fin 10 → ℤ), (p : ℤ) ∣ eval k F →
          ∀ (r : ℕ) (hr : 2 ≤ r),
            (Finset.univ.filter fun z : Fin 10 → ZMod (p^r) =>
              (∀ i, SmoothResidueIteration.toPrime p r (by omega) (z i) = (k i : ZMod p)) ∧
              eval₂ (Int.castRingHom (ZMod (p^r))) z F = 0).card ≤
                K*(r-1)*p^(9*(r-1)) *
                  vectorGcd p (fun i => eval k (pderiv i F)) * vectorGcd p k) := by
  obtain ⟨C,hC,hU⟩ := UnconditionalTenRootBound.of_anisotropic  F hF hA
  obtain ⟨D,_,B,hB,hR⟩ := BernertAllPrimeResidueBound.exists_all_prime_residue_bound  F hF hA
  refine ⟨max C B, hC.trans (le_max_left _ _), ?_, ?_⟩
  · intro p hp
    letI : Fact p.Prime := ⟨hp⟩
    intro s
    exact (hU p hp s).trans (Nat.mul_le_mul_right _ (le_max_left _ _))
  · intro p hp
    letI : Fact p.Prime := ⟨hp⟩
    intro k hk r hr
    have hpow := prime_defect_le_vectorGcd F hF p hp D k
    have hlocal := hR p hp k hk r hr
    rw [pow_add, ← mul_assoc] at hlocal
    calc
      _ ≤ B*(r-1)*p^(9*(r-1)) *
          p^(if (p : ℤ) ∣ D then 0 else
            if (∀ i, (p : ℤ) ∣ k i) then 2
            else if (∀ i, (p : ℤ) ∣ eval k (pderiv i F)) then 1 else 0) := hlocal
      _ ≤ (max C B)*(r-1)*p^(9*(r-1)) *
          (vectorGcd p (fun i => eval k (pderiv i F)) * vectorGcd p k) :=
        Nat.mul_le_mul
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (le_max_right _ _))) hpow
      _ = _ := by ring

end CubicTenVariables.CubicResidueGcdBound
