import TranslatedDepthSeven.IntegralLocalEquationMultiplicitySpecialization
import TranslatedDepthSeven.StrictRootTheorem

/-!
# From a rational stalk equality to one integral specialization certificate

Let a rational projective surface component be given together with an
integral affine point and `N - 2` integral equations.  Suppose that the
equations lie in the contracted integral affine-chart ideal and generate
the rational component ideal in the local ring of the displayed point.
If one selected Jacobian determinant is nonzero at the point, then there is
one nonzero integer outside whose prime divisors every reduction has local
dimension two and Hilbert--Samuel multiplicity one.

The proof does not assume a packaged spreading-out statement.  Equality in
the rational stalk first yields one rational polynomial which clears the
larger ideal into the displayed equation ideal.  Its finitely many rational
coefficients are then cleared literally.  The remaining constant
denominators are cleared by Noetherian finite generation in
`exists_integralCertificate_projectiveSurface_multiplicityOne`.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

noncomputable local instance integralPolynomialToRationalAlgebra''
    {N : ℕ} :
    Algebra (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) ℚ) :=
  (MvPolynomial.map (Int.castRingHom ℚ)).toAlgebra

/-- A rational local equality for integral local equations gives one
integer certificate which makes every avoided reduction a smooth surface
point in the literal Hilbert--Samuel sense used by the published Salberger
input. -/
theorem exists_integralCertificate_projectiveSurface_multiplicityOne_of_local_eq
    {N : ℕ} (hN : 2 ≤ N)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (z : Fin N → ℤ)
    (equations : Fin (N - 2) → MvPolynomial (Fin N) ℤ)
    (selectedVar : Fin (N - 2) → Fin N)
    (hselected : Function.Injective selectedVar)
    (hpoint : ∀ f ∈ Ideal.map rationalDehomogenizeAtZeroHom I,
      MvPolynomial.eval (fun i ↦ (z i : ℚ)) f = 0)
    (hIJ : Ideal.span (Set.range equations) ≤
      Ideal.map integralDehomogenizeAtZeroHom
        (projectiveIntegralClosureIdeal I))
    (hatPoint :
      Ideal.map
          (algebraMap (MvPolynomial (Fin N) ℚ)
            (Localization.AtPrime
              (RingHom.ker
                (MvPolynomial.eval (fun i ↦ (z i : ℚ))))))
          (Ideal.map (MvPolynomial.map (Int.castRingHom ℚ))
            (Ideal.span (Set.range equations))) =
        Ideal.map
          (algebraMap (MvPolynomial (Fin N) ℚ)
            (Localization.AtPrime
              (RingHom.ker
                (MvPolynomial.eval (fun i ↦ (z i : ℚ))))))
          (Ideal.map rationalDehomogenizeAtZeroHom I))
    (hminor : MvPolynomial.eval z
      (selectedJacobianDeterminant equations selectedVar) ≠ 0) :
    ∃ U : MvPolynomial (Fin N) ℤ,
      MvPolynomial.eval z U ≠ 0 ∧
      (∀ f ∈ Ideal.map integralDehomogenizeAtZeroHom
          (projectiveIntegralClosureIdeal I),
        U * f ∈ Ideal.span (Set.range equations)) ∧
      let Δ : ℤ := integralSelectedJacobianChartCertificate
        equations selectedVar U z
      Δ ≠ 0 ∧
        ∀ (p : ℕ) (hp : p.Prime), ¬p ∣ Δ.natAbs →
          HasHilbertSamuelMultiplicityAt hp
            (projectiveSpecialFiberIdeal I)
            (fun i ↦ (integralAffineProjectivePoint z i : ZMod p)) 2 1 := by
  let RZ := MvPolynomial (Fin N) ℤ
  let RQ := MvPolynomial (Fin N) ℚ
  let equationIdealZ : Ideal RZ := Ideal.span (Set.range equations)
  let equationIdealQ : Ideal RQ :=
    Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) equationIdealZ
  let componentIdealQ : Ideal RQ :=
    Ideal.map rationalDehomogenizeAtZeroHom I
  let zQ : Fin N → ℚ := fun i ↦ (z i : ℚ)
  have hIJQ : equationIdealQ ≤ componentIdealQ := by
    change Ideal.map (MvPolynomial.map (Int.castRingHom ℚ))
        (Ideal.span (Set.range equations)) ≤
      Ideal.map rationalDehomogenizeAtZeroHom I
    rw [← map_integralAffineChart_projectiveIntegralClosureIdeal I]
    exact Ideal.map_mono hIJ
  obtain ⟨uQ, huQ, hclearQ, _haway⟩ :=
    exists_nonzeroEvaluation_mul_mem_and_map_away_eq_of_map_atPoint_eq
      zQ equationIdealQ componentIdealQ hIJQ
        (IsNoetherian.noetherian componentIdealQ) (by
          simpa only [zQ, equationIdealQ, componentIdealQ, RQ] using hatPoint)
  let uZ : RZ := clearRationalMvPolynomial uQ
  let d : ℕ := mvPolynomialRationalCommonDenominator uQ
  have hdQ : (d : ℚ) ≠ 0 := by
    exact_mod_cast (mvPolynomialRationalCommonDenominator_pos uQ).ne'
  have huZQ : MvPolynomial.eval zQ
      (MvPolynomial.map (Int.castRingHom ℚ) uZ) ≠ 0 := by
    rw [show MvPolynomial.map (Int.castRingHom ℚ) uZ =
      MvPolynomial.C (d : ℚ) * uQ by
        simpa only [uZ, d] using map_clearRationalMvPolynomial uQ,
      map_mul, eval_C]
    exact mul_ne_zero hdQ huQ
  have huZ : MvPolynomial.eval z uZ ≠ 0 := by
    intro hzero
    apply huZQ
    rw [eval_map_intCast, hzero, Int.cast_zero]
  have hclearRational : ∀ f ∈ componentIdealQ,
      MvPolynomial.map (Int.castRingHom ℚ) uZ * f ∈ equationIdealQ := by
    intro f hf
    rw [show MvPolynomial.map (Int.castRingHom ℚ) uZ =
      MvPolynomial.C (d : ℚ) * uQ by
        simpa only [uZ, d] using map_clearRationalMvPolynomial uQ]
    rw [mul_assoc]
    exact equationIdealQ.mul_mem_left (MvPolynomial.C (d : ℚ))
      (hclearQ f hf)
  exact exists_integralCertificate_projectiveSurface_multiplicityOne
    hN I z equations selectedVar hselected uZ hpoint hIJ
      (by simpa only [componentIdealQ, equationIdealQ] using hclearRational)
      huZ hminor

end

end TranslatedDepthSeven
