import TranslatedDepthSeven.IsolatedVertexQuotientNodeDecomposition
import TranslatedDepthSeven.GaloisMinimalComponentFrontier
import TranslatedDepthSeven.ProjectiveLinearSpanIsolation

/-!
# From a quotient-node lift to the literal exceptional locus

`QuotientNodeExceptionalLift` retains the actual geometric source component,
but its source section is written in transformed `Qbar` coordinates.  This
file gives the exact, assumption-transparent adapter to the literal
exceptional locus.  Its remaining inputs are precisely the ordinary
coordinate-transport statements: an equivalence of the two displayed
section ideals, preservation of Hilbert dimension and degree, a rational
matrix of bounded height, and membership of the source point.  No counting
or component-selection conclusion is assumed.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

set_option maxHeartbeats 2000000

/-- The numerical exceptional-component condition is preserved by a ring
equivalence once the literal projective Hilbert data are preserved. -/
theorem isDepthSevenExceptionalComponent_map_of_hilbert
    {c : ℕ} {P : Ideal (MvPolynomial (Fin 13) Qbar)}
    (e : MvPolynomial (Fin 13) Qbar ≃+* MvPolynomial (Fin 13) Qbar)
    (hP : IsDepthSevenExceptionalComponent (c := c) P)
    (hHilbert : ∀ r d : ℕ,
      HasGeometricProjectiveDimensionDegree P r d →
        HasGeometricProjectiveDimensionDegree (P.map e) r d) :
    IsDepthSevenExceptionalComponent (c := c) (P.map e) := by
  rcases hP with ⟨hc1, hc3, hexcess | hlow⟩ | ⟨hc4, r, d, hPd, hr⟩
  · left
    exact ⟨hc1, hc3, Or.inl ⟨hexcess.choose, hexcess.choose_spec.choose,
      hHilbert _ _ hexcess.choose_spec.choose_spec.1,
      hexcess.choose_spec.choose_spec.2⟩⟩
  · left
    exact ⟨hc1, hc3, Or.inr ⟨hlow.choose,
      hHilbert _ _ hlow.choose_spec.1, hlow.choose_spec.2⟩⟩
  · right
    exact ⟨hc4, r, d, hHilbert r d hPd, hr⟩

/-- Exact adapter from a transformed quotient-node exceptional lift to the
literal bounded-height exceptional locus.  The theorem does not hide the
three genuine transport obligations: equality of section ideals, Hilbert
data under the coordinate equivalence, and membership of the transported
source point. -/
theorem QuotientNodeExceptionalLift.memDepthSevenExceptionalLocus_of_transport
    {J : Ideal (MvPolynomial (Fin 12) Qbar)}
    {b : Fin 12 → Qbar} {m : Qbar} {hm : m ≠ 0}
    {A : Matrix (Fin 4) (Fin 13) Qbar}
    {quotientComponent : Ideal (MvPolynomial (Fin 13) Qbar)}
    {quotientDimension quotientDegree : ℕ}
    (L : QuotientNodeExceptionalLift J b m hm A quotientComponent
      quotientDimension quotientDegree)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (heightBound : ℕ)
    (x : Projectivization ℚ (Fin 13 → ℚ))
    (e : MvPolynomial (Fin 13) Qbar ≃+* MvPolynomial (Fin 13) Qbar)
    (D : Matrix (Fin L.codimension) (Fin 13) ℚ)
    (hD : D.rank = L.codimension)
    (hheight : rationalProjectiveLinearHeight D ≤ heightBound)
    (hideal :
      (projectiveConeFinIdeal Qbar 11 J ⊔
          matrixRowLinearIdeal L.sectionMatrix).map e =
        finiteEquationIdeal
          (geometricLinearSectionEquationFinset equations D))
    (hHilbert : ∀ r d : ℕ,
      HasGeometricProjectiveDimensionDegree L.sourceComponent r d →
        HasGeometricProjectiveDimensionDegree
          (L.sourceComponent.map e) r d)
    (hx : ProjectivePointVanishesOnGeometricIdeal
      (L.sourceComponent.map e) x) :
    MemDepthSevenExceptionalLocus equations heightBound x := by
  let I := projectiveConeFinIdeal Qbar 11 J ⊔
    matrixRowLinearIdeal L.sectionMatrix
  have hPmin : L.sourceComponent ∈ I.minimalPrimes := by
    exact (mem_finiteMinimalPrimes_iff I L.sourceComponent).mp
      L.sourceComponent_mem
  have hmapMin : L.sourceComponent.map e ∈
      (I.map e).minimalPrimes :=
    map_mem_minimalPrimes_of_ringEquiv e hPmin
  have hcomponent : IsProjectiveSectionComponent equations D
      (L.sourceComponent.map e) := by
    refine ⟨?_, geometricIrrelevantCoordinateIdeal_not_le_of_projectivePoint
      (L.sourceComponent.map e) x hx⟩
    have hfinite : L.sourceComponent.map e ∈
        finiteMinimalPrimes (I.map e) :=
      (mem_finiteMinimalPrimes_iff _ _).mpr hmapMin
    rw [hideal] at hfinite
    simpa only [finiteEquationMinimalPrimes] using hfinite
  refine ⟨L.codimension, L.one_le_codimension,
    L.codimension_le_four, D, hD, hheight,
    L.sourceComponent.map e, hcomponent, ?_, hx⟩
  exact isDepthSevenExceptionalComponent_map_of_hilbert
    e L.exceptional hHilbert

end

end TranslatedDepthSeven
