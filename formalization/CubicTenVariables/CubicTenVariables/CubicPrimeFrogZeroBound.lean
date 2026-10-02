import CubicTenVariables.PrimeFrogZeroMass
import CubicTenVariables.UniformPrimePolynomialZeros
import CubicTenVariables.CubicFiniteFieldMass

/-!
# The ten-variable prime frog bound at j=0

The actual two coordinate gcds are retained. Uniform polynomial-root and
gradient-zero counts are proved dependencies, not additional premises.
One constant precedes every prime, including the exceptional small primes.
-/

noncomputable section
namespace CubicTenVariables.CubicPrimeFrogZeroBound
open MvPolynomial HessianTheorem11 PrimeFrogZeroMass SquarefreeResidueFactors
open scoped BigOperators

/-- The source's j=0 weighted-prime mass, for the actual ten-variable
anisotropic integral cubic, with no literature or counting premise. -/
theorem exists_uniform_bound
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) (hp : p.Prime),
      letI : NeZero p := ⟨hp.ne_zero⟩
      (∑ x ∈ Finset.univ.filter (fun x : Fin 10 → ZMod p =>
        eval₂ (Int.castRingHom (ZMod p)) x F = 0), rootWeight F p x) ≤ C*p^9 := by
  classical
  have hne : F ≠ 0 := by
    intro hz
    have he := hA (fun _ => 1) (by simp [hz])
    have hi := congrFun he (0 : Fin 10)
    norm_num at hi
  obtain ⟨R, hR, hroot⟩ := UniformPrimePolynomialZeros.exists_uniform_prime_zero_bound F hne
  obtain ⟨G, hG, hgrad⟩ := CubicFiniteFieldMass.exists_uniform_gradient_zero_bound F hF hA
  refine ⟨R+G+1, by omega, ?_⟩
  intro p hp
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hr : (Finset.univ.filter (fun x : Fin 10 → ZMod p =>
      eval₂ (Int.castRingHom (ZMod p)) x F = 0)).card ≤ R*p^9 := by
    simpa only [UniformPrimePolynomialZeros.primeZeros,
      TranslatedDepthSeven.mvPolynomialZeroSet, eval_map, Nat.reduceSub] using hroot p hp
  have hg : (Finset.univ.filter (fun x : Fin 10 → ZMod p =>
      ∀ i, eval₂ (Int.castRingHom (ZMod p)) x (pderiv i F) = 0)).card ≤ G*p^5 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, HessianTheorem11.gradient,
      _root_.funext_iff,
      Pi.zero_apply, pderiv_map, eval_map] using hgrad p hp
  have h69 : p^6 ≤ p^9 := Nat.pow_le_pow_right hp.one_le (by decide)
  have h29 : p^2 ≤ p^9 := Nat.pow_le_pow_right hp.one_le (by decide)
  calc
    _ ≤ (Finset.univ.filter (fun x : Fin 10 → ZMod p =>
          eval₂ (Int.castRingHom (ZMod p)) x F = 0)).card +
        p * (Finset.univ.filter (fun x : Fin 10 → ZMod p =>
          ∀ i, eval₂ (Int.castRingHom (ZMod p)) x (pderiv i F) = 0)).card + p^2 :=
      sum_rootWeight_le F p hp
    _ ≤ R*p^9 + p*(G*p^5) + p^2 :=
      Nat.add_le_add_right (Nat.add_le_add hr (Nat.mul_le_mul_left p hg)) _
    _ = R*p^9 + G*p^6 + p^2 := by ring
    _ ≤ R*p^9 + G*p^9 + p^9 :=
      Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left G h69) _) h29
    _ = (R+G+1)*p^9 := by ring

/-- The same one constant also covers omission of either or both gcd
factors, exactly as in the source's j=0 qualifier. -/
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
          (if includeCoordinates then vectorGcd p (integerLift p x) else 1)) ≤ C*p^9 := by
  classical
  obtain ⟨C,hC,hbound⟩ := exists_uniform_bound F hF hA
  refine ⟨C,hC,?_⟩
  intro p hp
  letI : NeZero p := ⟨hp.ne_zero⟩
  intro includeGradient includeCoordinates
  apply le_trans (Finset.sum_le_sum (fun x _ => ?_)) (hbound p hp)
  unfold rootWeight
  have hg : 1 ≤ vectorGcd p (fun i => eval (integerLift p x) (pderiv i F)) :=
    vectorGcd_pos p hp.pos _
  have hx : 1 ≤ vectorGcd p (integerLift p x) := vectorGcd_pos p hp.pos _
  apply Nat.mul_le_mul <;> split_ifs <;> omega

end CubicTenVariables.CubicPrimeFrogZeroBound
