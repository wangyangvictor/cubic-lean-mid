import TranslatedDepthSeven.ProjectedSourcePacketSmallEquation

/-!
# Static gradient split of a projected source packet

For one fixed primitive image equation, the source packet is split into the
points whose projected image has zero gradient and its literal complement.
The first set lies on one fixed proper source section.  At each point of the
second set a spatial derivative gives the integer certificate used to choose
the reservoir modulus.  The polynomial and the split are fixed before that
modulus.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

local instance projectedSourcePacketGradientPropDecidable (Q : Prop) :
    Decidable Q := Classical.propDecidable Q

/-- Points mapping to the singular locus of the displayed image equation. -/
def projectedSourceGradientZeroPoints
    {N r : ℕ} (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ)
    (P : MvPolynomial (Fin (r + 2)) ℤ)
    (X : Finset (IntVector N)) : Finset (IntVector N) :=
  X.filter fun z ↦ ∀ i,
    MvPolynomial.eval (integralAffineChartProjection A z)
      (MvPolynomial.pderiv i P) = 0

/-- Literal complementary packet where some image partial is nonzero. -/
def projectedSourceGradientNonzeroPoints
    {N r : ℕ} (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ)
    (P : MvPolynomial (Fin (r + 2)) ℤ)
    (X : Finset (IntVector N)) : Finset (IntVector N) :=
  X.filter fun z ↦ ∃ i,
    MvPolynomial.eval (integralAffineChartProjection A z)
      (MvPolynomial.pderiv i P) ≠ 0

@[simp]
theorem mem_projectedSourceGradientZeroPoints_iff
    {N r : ℕ} (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ)
    (P : MvPolynomial (Fin (r + 2)) ℤ)
    (X : Finset (IntVector N)) (z : IntVector N) :
    z ∈ projectedSourceGradientZeroPoints A P X ↔
      z ∈ X ∧ ∀ i,
        MvPolynomial.eval (integralAffineChartProjection A z)
          (MvPolynomial.pderiv i P) = 0 := by
  simp [projectedSourceGradientZeroPoints]

@[simp]
theorem mem_projectedSourceGradientNonzeroPoints_iff
    {N r : ℕ} (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ)
    (P : MvPolynomial (Fin (r + 2)) ℤ)
    (X : Finset (IntVector N)) (z : IntVector N) :
    z ∈ projectedSourceGradientNonzeroPoints A P X ↔
      z ∈ X ∧ ∃ i,
        MvPolynomial.eval (integralAffineChartProjection A z)
          (MvPolynomial.pderiv i P) ≠ 0 := by
  simp [projectedSourceGradientNonzeroPoints]

/-- Exact static partition; there is no pointwise choice in its definition. -/
theorem projectedSourceGradientZero_union_nonzero
    {N r : ℕ} (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ)
    (P : MvPolynomial (Fin (r + 2)) ℤ)
    (X : Finset (IntVector N)) :
    projectedSourceGradientZeroPoints A P X ∪
      projectedSourceGradientNonzeroPoints A P X = X := by
  ext z
  simp only [Finset.mem_union, mem_projectedSourceGradientZeroPoints_iff,
    mem_projectedSourceGradientNonzeroPoints_iff]
  constructor
  · rintro (⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz
  · intro hz
    by_cases hzero : ∀ i,
        MvPolynomial.eval (integralAffineChartProjection A z)
          (MvPolynomial.pderiv i P) = 0
    · exact Or.inl ⟨hz, hzero⟩
    · right
      refine ⟨hz, ?_⟩
      push_neg at hzero
      exact hzero

/-- The fixed derivative section covers the whole singular-image subset. -/
theorem projectedSourceGradientZeroPoints_vanish_on_properCut
    {N r degree : ℕ} (hdegree : 0 < degree)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ)
    (G : MvPolynomial (Fin (r + 2)) ℚ)
    (hprojection :
      StandardAG.IsAffineChartFiniteBirationalLinearProjection
        (degree := degree) I hI A G)
    (P : MvPolynomial (Fin (r + 2)) ℤ)
    (hPirred : Irreducible (P.map (Int.castRingHom ℚ)))
    (hPhom : P.IsHomogeneous degree)
    (himage : RingHom.ker
      (StandardAG.projectiveMatrixCoordinateMap I
        (A.map (Int.castRingHom ℚ))).toRingHom =
        Ideal.span {P.map (Int.castRingHom ℚ)})
    (X : Finset (IntVector N)) :
    ∃ j : Fin (r + 2),
      let F := projectiveMatrixPolynomialPullback
        (A.map (Int.castRingHom ℚ))
        (MvPolynomial.pderiv j (P.map (Int.castRingHom ℚ)))
      F.IsHomogeneous (degree - 1) ∧ F ∉ I ∧
        ∀ z ∈ projectedSourceGradientZeroPoints A P X,
          MvPolynomial.eval
            (fun k ↦ (integralAffineChartVector z k : ℚ)) F = 0 := by
  obtain ⟨j, hhom, hnot, hzero⟩ :=
    exists_properSourceCut_vanishing_on_projectedSingularPoints hdegree I hI
      A G hprojection P hPirred hPhom himage
  refine ⟨j, hhom, hnot, ?_⟩
  intro z hz
  exact hzero z (mem_projectedSourceGradientZeroPoints_iff A P X z |>.1 hz).2

end

end TranslatedDepthSeven
