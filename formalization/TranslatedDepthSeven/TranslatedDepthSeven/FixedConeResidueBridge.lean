import TranslatedDepthSeven.FixedConeResidueCount

/-!
# Integral points in the fixed cone model

The finite normalization model contains extra monic relations, so the local
point count is useful only after proving that every integral point of the
original rational cone satisfies those relations after good reduction.  The
generic-model equality supplies exactly this fact.  Injectivity of
`Z[1/Delta] -> Q` first brings the rational vanishing back to the principal
open; reduction then carries it to `ZMod p`.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

set_option maxHeartbeats 600000

/-- Every integral common zero of the original rational equations reduces,
at a prime away from the fixed denominator, to a point of the literal finite
normalization model. -/
theorem integralZero_mem_fixedFivefoldResidueModel
    {r : ℕ} {f : Fin r → MvPolynomial (Fin 13) ℚ}
    (M : FixedFivefoldResidueModel f)
    (x : IntVector 13)
    (hx : ∀ i, MvPolynomial.eval (fun j ↦ (x j : ℚ)) (f i) = 0)
    (p : ℕ) (hp : p.Prime)
    (hpden : ¬ p ∣ M.denominator.natAbs) :
    (fun j ↦ (x j : ZMod p)) ∈
      principalOpenIdealZeroFinset 13 M.denominator p hp hpden
        (finiteNormalizationModelIdeal
          M.equations M.parameters M.relations) := by
  apply intCast_mem_principalOpenModel_of_mem_rationalIdeal
    M x ?_ p hp hpden
  let xQ : Fin 13 → ℚ := fun i ↦ (x i : ℚ)
  let evQ : MvPolynomial (Fin 13) ℚ →+* ℚ :=
    MvPolynomial.eval₂Hom (RingHom.id ℚ) xQ
  have hspanZero : Ideal.span (Set.range f) ≤ RingHom.ker evQ := by
    rw [Ideal.span_le]
    rintro g ⟨i, rfl⟩
    change evQ (f i) = 0
    simpa [evQ, xQ] using hx i
  intro g hg
  exact RingHom.mem_ker.mp (hspanZero hg)

end

end TranslatedDepthSeven
