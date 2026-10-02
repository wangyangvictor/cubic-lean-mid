import CubicTenVariables.PrimeFrogOneMass
import CubicTenVariables.CubicPrimeFrogZeroBound
import CubicTenVariables.CubicPrimeFrogTwoBound

/-!
# The ten-variable prime frog bound at j=1

Weighted Cauchy--Schwarz combines the proved j=0 and j=2 estimates.
The final real exponent is exactly 21/2. One constant precedes every
prime and both independent gcd-omission switches; no counting or
literature premise is supplied.
-/

noncomputable section
namespace CubicTenVariables.CubicPrimeFrogOneBound
open MvPolynomial HessianTheorem11 PrimeFrogZeroMass PrimeFrogOneMass
  SquarefreeResidueFactors HessianKernelCRT
open scoped BigOperators

/-- Squared j=1 estimate, simultaneously for all four literal gcd weights. -/
theorem exists_uniform_squared_bound
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) (hp : p.Prime),
      letI : NeZero p := ⟨hp.ne_zero⟩
      ∀ (includeGradient includeCoordinates : Bool),
        (oneMass F p includeGradient includeCoordinates)^2 ≤ (C : ℝ)*(p : ℝ)^21 := by
  classical
  obtain ⟨C₀, hC₀, hzero⟩ := CubicPrimeFrogZeroBound.exists_uniform_bound_with_optional_gcds F hF hA
  obtain ⟨C₂, hC₂, htwo⟩ := CubicPrimeFrogTwoBound.exists_uniform_bound_with_optional_gcds F hF hA
  refine ⟨C₀*C₂, by nlinarith, ?_⟩
  intro p hp
  letI : NeZero p := ⟨hp.ne_zero⟩
  intro includeGradient includeCoordinates
  have h₀ := hzero p hp includeGradient includeCoordinates
  have h₂ := htwo p hp includeGradient includeCoordinates
  change (∑ x ∈ Finset.univ.filter (fun x : Fin 10 → ZMod p =>
      eval₂ (Int.castRingHom (ZMod p)) x F = 0),
      optionalRootWeight F p x includeGradient includeCoordinates) ≤ C₀*p^9 at h₀
  change (∑ x ∈ Finset.univ.filter (fun x : Fin 10 → ZMod p =>
      eval₂ (Int.castRingHom (ZMod p)) x F = 0),
      optionalRootWeight F p x includeGradient includeCoordinates *
        hessianKernelCard F p x) ≤ C₂*p^12 at h₂
  calc
    _ ≤ ((∑ x ∈ Finset.univ.filter (fun x : Fin 10 → ZMod p =>
          eval₂ (Int.castRingHom (ZMod p)) x F = 0),
          optionalRootWeight F p x includeGradient includeCoordinates : ℕ) : ℝ) *
        ((∑ x ∈ Finset.univ.filter (fun x : Fin 10 → ZMod p =>
          eval₂ (Int.castRingHom (ZMod p)) x F = 0),
          optionalRootWeight F p x includeGradient includeCoordinates *
            hessianKernelCard F p x : ℕ) : ℝ) :=
      oneMass_sq_le F p includeGradient includeCoordinates
    _ ≤ ((C₀*p^9 : ℕ) : ℝ)*((C₂*p^12 : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul h₀ h₂
    _ = _ := by push_cast; ring

/-- Square-root form of the source estimate, with no supplied mass bound. -/
theorem exists_uniform_sqrt_bound
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (p : ℕ) (hp : p.Prime),
      letI : NeZero p := ⟨hp.ne_zero⟩
      ∀ (includeGradient includeCoordinates : Bool),
        oneMass F p includeGradient includeCoordinates ≤ A*(p : ℝ)^((21 : ℝ)/2) := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_squared_bound F hF hA
  refine ⟨C, by exact_mod_cast hC, ?_⟩
  intro p hp
  letI : NeZero p := ⟨hp.ne_zero⟩
  intro includeGradient includeCoordinates
  exact le_mul_rpow_of_sq_le (by exact_mod_cast hC) (Nat.cast_nonneg p)
    (hbound p hp includeGradient includeCoordinates)

/-- The literal source real-power bound at j=1, including omission of either
or both gcd factors, with one constant chosen before every prime and switch. -/
theorem exists_uniform_bound
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (p : ℕ) (hp : p.Prime),
      letI : NeZero p := ⟨hp.ne_zero⟩
      ∀ (includeGradient includeCoordinates : Bool),
        (∑ x ∈ Finset.univ.filter (fun x : Fin 10 → ZMod p =>
          eval₂ (Int.castRingHom (ZMod p)) x F = 0),
          (hessianKernelCard F p x : ℝ)^((1 : ℝ)/2) *
          (((if includeGradient then
            vectorGcd p (fun i => eval (integerLift p x) (pderiv i F)) else 1) *
          (if includeCoordinates then vectorGcd p (integerLift p x) else 1) : ℕ) : ℝ)) ≤
            A*(p : ℝ)^((21 : ℝ)/2) := by
  classical
  obtain ⟨A,hA',hbound⟩ := exists_uniform_sqrt_bound F hF hA
  refine ⟨A,hA',?_⟩
  intro p hp
  letI : NeZero p := ⟨hp.ne_zero⟩
  intro includeGradient includeCoordinates
  simpa only [oneMass_eq_rpow, optionalRootWeight] using
    hbound p hp includeGradient includeCoordinates

end CubicTenVariables.CubicPrimeFrogOneBound
