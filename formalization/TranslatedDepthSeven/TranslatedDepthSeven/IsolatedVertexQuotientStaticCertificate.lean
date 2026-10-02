import TranslatedDepthSeven.IsolatedVertexQuotientReservoirSelection

/-!
# A fixed certificate at every regular quotient point

The Jacobian certificate used to delete bad reservoir primes must be chosen
before the modulus.  This file makes that choice literal.  A certificate
retains its actual equation rows, coordinate columns, nonzero determinant,
and the fixed polynomial height bound.  The resulting integer-valued
function is defined on the whole quotient box (with the harmless value `1`
off the regular locus), so it can be passed directly to the static
certificate-deleted reservoir cover.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

local instance isolatedVertexQuotientStaticCertificatePropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-- The regular part of the literal isolated-vertex quotient point set. -/
def isolatedVertexRegularQuotientPointFinset
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (x₀ : IntVector 13)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ)) :
    Finset (IntVector 12) :=
  (isolatedVertexQuotientPointFinset U p x₀ sourceEquations CF).filter
    (IsQuotientJacobianRegularAt
      (isolatedVertexQuotientAffineEquationFinset
        U p x₀ lowerEquations))

@[simp]
theorem mem_isolatedVertexRegularQuotientPointFinset_iff
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (x₀ : IntVector 13)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (w : IntVector 12) :
    w ∈ isolatedVertexRegularQuotientPointFinset
        U p x₀ sourceEquations CF lowerEquations ↔
      w ∈ isolatedVertexQuotientPointFinset
          U p x₀ sourceEquations CF ∧
      IsQuotientJacobianRegularAt
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations) w := by
  classical
  simp [isolatedVertexRegularQuotientPointFinset]

/-- The actual bounded `7 × 7` Jacobian certificate selected at one
regular quotient point. -/
structure IsolatedVertexQuotientJacobianCertificate
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (x₀ : IntVector 13)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (w : IntVector 12) where
  rows : Fin 7 → Fin
    (isolatedVertexQuotientAffineEquationFinset
      U p x₀ lowerEquations).card
  cols : Fin 7 → Fin 12
  rows_injective : Function.Injective rows
  cols_injective : Function.Injective cols
  determinant_ne_zero :
    integralJacobianMinor
      (indexedFinsetFamily
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations)) w rows cols ≠ 0
  determinant_height :
    ((integralJacobianMinor
      (indexedFinsetFamily
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations)) w rows cols).natAbs : ℝ) ≤
      p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations

namespace IsolatedVertexQuotientJacobianCertificate

/-- The literal integer determinant carried by the certificate. -/
def value
    {U : IntegralUnimodularChange 13} {p : Parameters}
    {x₀ : IntVector 13}
    {lowerEquations : Finset (MvPolynomial (Fin 12) ℤ)}
    {w : IntVector 12}
    (C : IsolatedVertexQuotientJacobianCertificate
      U p x₀ lowerEquations w) : ℤ :=
  integralJacobianMinor
    (indexedFinsetFamily
      (isolatedVertexQuotientAffineEquationFinset
        U p x₀ lowerEquations)) w C.rows C.cols

theorem value_ne_zero
    {U : IntegralUnimodularChange 13} {p : Parameters}
    {x₀ : IntVector 13}
    {lowerEquations : Finset (MvPolynomial (Fin 12) ℤ)}
    {w : IntVector 12}
    (C : IsolatedVertexQuotientJacobianCertificate
      U p x₀ lowerEquations w) :
    C.value ≠ 0 :=
  C.determinant_ne_zero

theorem value_height
    {U : IntegralUnimodularChange 13} {p : Parameters}
    {x₀ : IntVector 13}
    {lowerEquations : Finset (MvPolynomial (Fin 12) ℤ)}
    {w : IntVector 12}
    (C : IsolatedVertexQuotientJacobianCertificate
      U p x₀ lowerEquations w) :
    (C.value.natAbs : ℝ) ≤
      p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations :=
  C.determinant_height

end IsolatedVertexQuotientJacobianCertificate

/-- Every point of the displayed regular locus carries a bounded literal
certificate. -/
theorem nonempty_isolatedVertexQuotientJacobianCertificate
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset
      p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    {w : IntVector 12}
    (hw : w ∈ isolatedVertexRegularQuotientPointFinset
      U p x₀ sourceEquations CF lowerEquations) :
    Nonempty (IsolatedVertexQuotientJacobianCertificate
      U p x₀ lowerEquations w) := by
  obtain ⟨hwPoint, hwRegular⟩ :=
    (mem_isolatedVertexRegularQuotientPointFinset_iff
      U p x₀ sourceEquations CF lowerEquations w).1 hw
  obtain ⟨rows, cols, hrows, hcols, hminor, hheight⟩ :=
    exists_quotientAffineEquation_jacobianCertificate_le_heightPower
      U p sourceEquations CF hx₀ lowerEquations hwPoint hwRegular
  exact ⟨{
    rows := rows
    cols := cols
    rows_injective := hrows
    cols_injective := hcols
    determinant_ne_zero := hminor
    determinant_height := hheight }⟩

/-- A proof-independent selected certificate on the regular locus. -/
def selectedIsolatedVertexQuotientJacobianCertificate
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset
      p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (w : IntVector 12)
    (hw : w ∈ isolatedVertexRegularQuotientPointFinset
      U p x₀ sourceEquations CF lowerEquations) :
    IsolatedVertexQuotientJacobianCertificate
      U p x₀ lowerEquations w :=
  Classical.choice
    (nonempty_isolatedVertexQuotientJacobianCertificate
      U p sourceEquations CF hx₀ lowerEquations hw)

/-- Total integer certificate: the selected determinant on the regular
locus and `1` elsewhere. -/
def isolatedVertexQuotientSelectedCertificateValue
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset
      p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (w : IntVector 12) : ℤ :=
  if hw : w ∈ isolatedVertexRegularQuotientPointFinset
      U p x₀ sourceEquations CF lowerEquations then
    (selectedIsolatedVertexQuotientJacobianCertificate
      U p sourceEquations CF hx₀ lowerEquations w hw).value
  else 1

theorem isolatedVertexQuotientSelectedCertificateValue_eq
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset
      p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    {w : IntVector 12}
    (hw : w ∈ isolatedVertexRegularQuotientPointFinset
      U p x₀ sourceEquations CF lowerEquations) :
    isolatedVertexQuotientSelectedCertificateValue
        U p sourceEquations CF hx₀ lowerEquations w =
      (selectedIsolatedVertexQuotientJacobianCertificate
        U p sourceEquations CF hx₀ lowerEquations w hw).value := by
  simp [isolatedVertexQuotientSelectedCertificateValue, hw]

theorem isolatedVertexQuotientSelectedCertificateValue_ne_zero
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset
      p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    {w : IntVector 12}
    (hw : w ∈ isolatedVertexRegularQuotientPointFinset
      U p x₀ sourceEquations CF lowerEquations) :
    isolatedVertexQuotientSelectedCertificateValue
      U p sourceEquations CF hx₀ lowerEquations w ≠ 0 := by
  rw [isolatedVertexQuotientSelectedCertificateValue_eq
    U p sourceEquations CF hx₀ lowerEquations hw]
  exact (selectedIsolatedVertexQuotientJacobianCertificate
    U p sourceEquations CF hx₀ lowerEquations w hw).value_ne_zero

theorem isolatedVertexQuotientSelectedCertificateValue_height
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset
      p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    {w : IntVector 12}
    (hw : w ∈ isolatedVertexRegularQuotientPointFinset
      U p x₀ sourceEquations CF lowerEquations) :
    ((isolatedVertexQuotientSelectedCertificateValue
      U p sourceEquations CF hx₀ lowerEquations w).natAbs : ℝ) ≤
      p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations := by
  rw [isolatedVertexQuotientSelectedCertificateValue_eq
    U p sourceEquations CF hx₀ lowerEquations hw]
  exact (selectedIsolatedVertexQuotientJacobianCertificate
    U p sourceEquations CF hx₀ lowerEquations w hw).value_height

end

end TranslatedDepthSeven
