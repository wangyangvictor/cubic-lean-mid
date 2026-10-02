import CubicTenVariables.CubicPrimeSingularMass

/-! The full ten-variable j=2 frog estimate, including all four choices
of the source gcd factors. All point-count dependencies are proved. -/

noncomputable section
namespace CubicTenVariables.CubicPrimeFrogTwoBound
open MvPolynomial HessianTheorem11 HessianKernelCRT PrimeFrogZeroMass
open SquarefreeResidueFactors PrimeFrogTwoMass
open scoped BigOperators

/-- The actual kernel-weighted root mass at every prime. Only integral
cubic homogeneity and rational anisotropy are hypotheses. -/
theorem exists_uniform_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) (hp : p.Prime),
      letI : NeZero p := ⟨hp.ne_zero⟩
      (∑ x ∈ Finset.univ.filter (fun x : Fin 10 → ZMod p =>
        eval₂ (Int.castRingHom (ZMod p)) x F = 0),
        hessianKernelCard F p x * rootWeight F p x) ≤ C*p^12 := by
  classical
  obtain ⟨I, _hI, hi⟩ := CubicFiniteFieldMass.exists_uniform_hessian_kernel_mass_bound F hF hA
  obtain ⟨S, _hS, hs⟩ := CubicPrimeSingularMass.exists_uniform_bound F hF hA
  refine ⟨I+S+1, by omega, ?_⟩
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  calc
    _ ≤ (∑ x : Fin 10 → ZMod p, hessianKernelCard F p x) +
        p * (∑ x ∈ singularRootPoints F p, hessianKernelCard F p x) + p^(10+2) :=
      sum_kernel_mul_rootWeight_le F hF p hp
    _ ≤ I*p^12 + p*(S*p^11) + p^12 :=
      Nat.add_le_add_right (Nat.add_le_add (hi p) (Nat.mul_le_mul_left p (hs p))) _
    _ = (I+S+1)*p^12 := by ring

/-- One constant precedes both the prime and the independent choices
of whether to retain each gcd factor. The summand is fully displayed. -/
theorem exists_uniform_bound_with_optional_gcds
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) (hp : p.Prime),
      letI : NeZero p := ⟨hp.ne_zero⟩
      ∀ (includeGradient includeCoordinates : Bool),
        (∑ x ∈ Finset.univ.filter (fun x : Fin 10 → ZMod p =>
          eval₂ (Int.castRingHom (ZMod p)) x F = 0),
          (if includeGradient then
            vectorGcd p (fun i => eval (integerLift p x) (pderiv i F)) else 1) *
          (if includeCoordinates then vectorGcd p (integerLift p x) else 1) *
          hessianKernelCard F p x) ≤ C*p^12 := by
  classical
  obtain ⟨C, hC, hc⟩ := exists_uniform_bound F hF hA
  refine ⟨C, hC, ?_⟩
  intro p hp
  letI : NeZero p := ⟨hp.ne_zero⟩
  intro includeGradient includeCoordinates
  apply le_trans (Finset.sum_le_sum (fun x _ => ?_)) (hc p hp)
  rw [Nat.mul_comm (hessianKernelCard F p x)]
  apply Nat.mul_le_mul_right
  unfold rootWeight
  have hg : 1 ≤ vectorGcd p (fun i => eval (integerLift p x) (pderiv i F)) :=
    vectorGcd_pos p hp.pos _
  have hx : 1 ≤ vectorGcd p (integerLift p x) := vectorGcd_pos p hp.pos _
  apply Nat.mul_le_mul <;> split_ifs <;> omega

end CubicTenVariables.CubicPrimeFrogTwoBound
