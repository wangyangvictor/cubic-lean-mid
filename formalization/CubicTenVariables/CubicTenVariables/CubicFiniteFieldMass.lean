import CubicTenVariables.CubicMassEquations
import CubicTenVariables.FixedEquationPrimeCount
import CubicTenVariables.HessianKernelCRT

/-! Actual finite residue masses attached to the integral incidence and
first-partial equations. -/

noncomputable section
namespace CubicTenVariables.CubicFiniteFieldMass
open MvPolynomial CubicMassEquations IntegralEquationCounts HessianKernelCRT

/-- The common zeros of the twenty-coordinate incidence equations are
exactly a base point together with a vector in its actual Hessian kernel. -/
def incidenceZeroEquiv {n : ℕ} (F : MvPolynomial (Fin n) ℤ) (q : ℕ) :
    {z : (Fin n ⊕ Fin n) → ZMod q //
      ∀ i, eval₂ (Int.castRingHom (ZMod q)) z (incidenceEquation F i) = 0} ≃
    (x : Fin n → ZMod q) ×
      {y : Fin n → ZMod q //
        (HessianTheorem11.hessian (map (Int.castRingHom (ZMod q)) F) x).mulVec y = 0} where
  toFun z := ⟨z.val ∘ Sum.inl, ⟨z.val ∘ Sum.inr,
    (incidence_equations_zero_iff _ F z.val).mp z.property⟩⟩
  invFun xy := ⟨Sum.elim xy.1 xy.2.val,
    (incidence_equations_zero_iff _ F _).mpr xy.2.property⟩
  left_inv z := by
    apply Subtype.ext
    funext i
    cases i <;> rfl
  right_inv xy := by
    rcases xy with ⟨x, y, hy⟩
    rfl

/-- Summing over all base points retains the full incidence, including
points with F(x) nonzero. -/
theorem incidence_zeroCount_eq_sum {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (q : ℕ) [NeZero q] :
    zeroCount (incidenceEquation F) q =
      ∑ x : Fin n → ZMod q, hessianKernelCard F q x := by
  exact (Nat.card_congr (incidenceZeroEquiv F q)).trans Nat.card_sigma

/-- Gradient zeros are actual common zeros of the reduced first partials. -/
theorem gradient_zeroCount_eq {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (q : ℕ) :
    zeroCount (gradientEquation F) q =
      Nat.card {x : Fin n → ZMod q //
        HessianTheorem11.gradient (map (Int.castRingHom (ZMod q)) F) x = 0} := by
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun x => gradient_equations_zero_iff _ F x

/-- One constant controls the actual singular residue count for every
prime, including primes of bad reduction. -/
theorem exists_uniform_gradient_zero_bound
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : HessianTheorem11.Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ p : ℕ, p.Prime →
      Nat.card {x : Fin 10 → ZMod p //
        HessianTheorem11.gradient (map (Int.castRingHom (ZMod p)) F) x = 0} ≤
        C*p^5 := by
  obtain ⟨C, hC, hc⟩ := FixedEquationPrimeCount.exists_uniform_bound
    (gradientEquation F) (rationalGradientIdeal_ne_top F hF)
    (gradient_quotient_dimension_le_five F hF hA)
  refine ⟨C, hC, ?_⟩
  intro p hp
  rw [← gradient_zeroCount_eq]
  exact hc p hp

/-- The full Hessian kernel mass counts actual incidence pairs over each
prime field. The constant is uniform in the prime and needs no mass input. -/
theorem exists_uniform_hessian_kernel_mass_bound
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : HessianTheorem11.Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) [Fact p.Prime],
      (∑ x : Fin 10 → ZMod p, hessianKernelCard F p x) ≤ C*p^12 := by
  obtain ⟨C, hC, hc⟩ := FixedEquationPrimeCount.exists_uniform_bound
    (incidenceEquation F) (rationalIncidenceIdeal_ne_top F)
    (incidence_quotient_dimension_le_twelve F hF hA)
  refine ⟨C, hC, ?_⟩
  intro p hp
  rw [← incidence_zeroCount_eq_sum]
  exact hc p hp.out

end CubicTenVariables.CubicFiniteFieldMass
