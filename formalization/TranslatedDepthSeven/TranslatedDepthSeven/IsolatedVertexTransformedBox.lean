import TranslatedDepthSeven.ProjectiveVertexTranslationInvariant
import TranslatedDepthSeven.SurfaceReservoirTangentBridge
import TranslatedDepthSeven.ConcreteIntegralCountRescaling

/-!
# The fixed unimodular change preserves an `O(T)` box

The isolated-vertex reduction uses one integral unimodular matrix depending
only on the fixed cone.  This file records, without asymptotic notation, the
elementary fact that its image of the normalized displacement box is again a
box whose side is a fixed constant times `T`.

The matrix norm below is the maximum `l1` norm of a row.  Consequently the
proof is only the triangle inequality.  In particular, no geometry-of-numbers
or point-counting input is hidden here.
-/

namespace TranslatedDepthSeven

noncomputable section

open Matrix

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The `l1` norm of one row of an integral square matrix. -/
def integralMatrixRowL1Norm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : ℕ :=
  ∑ j, (A i j).natAbs

/-- The maximum `l1` norm of a row of an integral square matrix. -/
def integralMatrixL1Norm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) : ℕ :=
  Finset.univ.sup (integralMatrixRowL1Norm A)

theorem integralMatrixRowL1Norm_le_integralMatrixL1Norm
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    integralMatrixRowL1Norm A i ≤ integralMatrixL1Norm A := by
  exact Finset.le_sup (f := integralMatrixRowL1Norm A) (Finset.mem_univ i)

/-- Triangle inequality for a finite sum, stated in `Nat` after applying
`Int.natAbs`. -/
theorem natAbs_finset_sum_le_sum_natAbs
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℤ) :
    (∑ i ∈ s, f i).natAbs ≤ ∑ i ∈ s, (f i).natAbs := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (Int.natAbs_add_le (f a) (∑ i ∈ s, f i)).trans
        (Nat.add_le_add_left ih _)

/-- A matrix sends the integral box of radius `M` into the box of radius
`||A||_1 M`, where `||A||_1` is the maximum row-sum norm above. -/
theorem matrix_mulVec_natAbs_le_integralMatrixL1Norm_mul
    {n M : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (x : IntVector n) (hx : ∀ j, (x j).natAbs ≤ M) (i : Fin n) :
    (Matrix.mulVec A x i).natAbs ≤ integralMatrixL1Norm A * M := by
  classical
  have htriangle :
      (∑ j, A i j * x j).natAbs ≤ ∑ j, (A i j * x j).natAbs := by
    simpa using natAbs_finset_sum_le_sum_natAbs
      (Finset.univ : Finset (Fin n)) (fun j ↦ A i j * x j)
  have hterms :
      (∑ j, (A i j * x j).natAbs) ≤
        ∑ j, (A i j).natAbs * M := by
    apply Finset.sum_le_sum
    intro j _hj
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul_left _ (hx j)
  have hrow :
      (∑ j, (A i j).natAbs * M) =
        integralMatrixRowL1Norm A i * M := by
    rw [integralMatrixRowL1Norm, Finset.sum_mul]
  change (∑ j, A i j * x j).natAbs ≤ _
  calc
    (∑ j, A i j * x j).natAbs ≤
        ∑ j, (A i j * x j).natAbs := htriangle
    _ ≤ ∑ j, (A i j).natAbs * M := hterms
    _ = integralMatrixRowL1Norm A i * M := hrow
    _ ≤ integralMatrixL1Norm A * M :=
      Nat.mul_le_mul_right M
        (integralMatrixRowL1Norm_le_integralMatrixL1Norm A i)

/-- The exact integral radius used after the fixed isolated-vertex coordinate
change. -/
def isolatedVertexTransformedNaturalSide {n : ℕ}
    (U : IntegralUnimodularChange n) (p : Parameters) : ℕ :=
  integralMatrixL1Norm U.forward * (2 * surfaceTangentNaturalSide p)

/-- Every normalized displacement lies in the transformed box with the
literal radius just defined. -/
theorem pointEquiv_coordinate_le_isolatedVertexTransformedNaturalSide
    (U : IntegralUnimodularChange 13)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {z : IntVector 13}
    (hz : z ∈ depthSevenNormalizedDisplacementFinset p x₀ equations CF) :
    ∀ i, ((U.pointEquiv z) i).natAbs ≤
      isolatedVertexTransformedNaturalSide U p := by
  intro i
  exact matrix_mulVec_natAbs_le_integralMatrixL1Norm_mul
    U.forward z
      (depthSevenNormalized_coordinate_le_two_surfaceTangentNaturalSide
        p x₀ equations CF hz) i

/-- Since the matrix is fixed, the transformed radius is at most an explicit
fixed multiple of the real normalized side `T`. -/
theorem isolatedVertexTransformedNaturalSide_cast_le
    {n : ℕ} (U : IntegralUnimodularChange n) (p : Parameters) :
    (isolatedVertexTransformedNaturalSide U p : ℝ) ≤
      (6 * integralMatrixL1Norm U.forward : ℕ) * p.T := by
  have hside := surfaceTangentNaturalSide_cast_le_three_mul p
  change (surfaceTangentNaturalSide p : ℝ) ≤ 3 * p.T at hside
  unfold isolatedVertexTransformedNaturalSide
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  nlinarith [show (0 : ℝ) ≤ integralMatrixL1Norm U.forward by positivity]

/-- The complete first-coordinate fibre factor is likewise an explicit fixed
multiple of `T`. -/
theorem isolatedVertexTransformed_fibreFactor_cast_le
    {n : ℕ} (U : IntegralUnimodularChange n) (p : Parameters) :
    ((2 * isolatedVertexTransformedNaturalSide U p + 1 : ℕ) : ℝ) ≤
      (12 * integralMatrixL1Norm U.forward + 1 : ℕ) * p.T := by
  have hside := isolatedVertexTransformedNaturalSide_cast_le U p
  have hT := p.one_le_T
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one,
    Nat.cast_ofNat] at hside ⊢
  nlinarith [show (0 : ℝ) ≤ integralMatrixL1Norm U.forward by positivity]

/-- An integral linear change commutes exactly with the affine rescaling
`x = x₀ + m z`. -/
theorem IntegralUnimodularChange.pointEquiv_integralAffineMap
    {n m : ℕ} (U : IntegralUnimodularChange n)
    (x₀ z : IntVector n) :
    U.pointEquiv (integralAffineMap x₀ z m) =
      integralAffineMap (U.pointEquiv x₀) (U.pointEquiv z) m := by
  funext i
  change (∑ j, U.forward i j * (x₀ j + (m : ℤ) * z j)) =
    (∑ j, U.forward i j * x₀ j) +
      (m : ℤ) * ∑ j, U.forward i j * z j
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- Forgetting the first coordinate also commutes with the affine
rescaling. -/
@[simp]
theorem dropFirstIntVector_integralAffineMap
    {n m : ℕ} (x₀ z : IntVector (n + 1)) :
    dropFirstIntVector (integralAffineMap x₀ z m) =
      integralAffineMap (dropFirstIntVector x₀)
        (dropFirstIntVector z) m := by
  rfl

/-- The literal quotient point set: the image of the exact normalized
displacement set under the fixed integral change followed by deletion of the
vertex coordinate.  Keeping this image, rather than replacing it by the full
zero locus of the quotient equations, retains all exceptional-set exclusions
needed later. -/
def isolatedVertexQuotientPointFinset
    (U : IntegralUnimodularChange 13)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ) :
    Finset (IntVector 12) := by
  classical
  exact (depthSevenNormalizedDisplacementFinset p x₀ equations CF).image
    (fun z ↦ dropFirstIntVector (U.pointEquiv z))

@[simp]
theorem mem_isolatedVertexQuotientPointFinset_iff
    (U : IntegralUnimodularChange 13)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (w : IntVector 12) :
    w ∈ isolatedVertexQuotientPointFinset U p x₀ equations CF ↔
      ∃ z ∈ depthSevenNormalizedDisplacementFinset p x₀ equations CF,
        dropFirstIntVector (U.pointEquiv z) = w := by
  classical
  simp [isolatedVertexQuotientPointFinset]

/-- Each quotient point is still in the exact transformed `O_U(T)` box. -/
theorem isolatedVertexQuotientPoint_coordinate_le
    (U : IntegralUnimodularChange 13)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {w : IntVector 12}
    (hw : w ∈ isolatedVertexQuotientPointFinset U p x₀ equations CF) :
    ∀ i, (w i).natAbs ≤ isolatedVertexTransformedNaturalSide U p := by
  obtain ⟨z, hz, rfl⟩ :=
    (mem_isolatedVertexQuotientPointFinset_iff
      U p x₀ equations CF w).1 hw
  intro i
  exact pointEquiv_coordinate_le_isolatedVertexTransformedNaturalSide
    U p x₀ equations CF hz i.succ

/-- Forgetting the transformed vertex coordinate has the exact elementary
fibre loss and no other multiplicity. -/
theorem card_depthSevenNormalizedDisplacementFinset_le_quotient_mul_fibre
    (U : IntegralUnimodularChange 13)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ) :
    (depthSevenNormalizedDisplacementFinset p x₀ equations CF).card ≤
      (isolatedVertexQuotientPointFinset U p x₀ equations CF).card *
        (2 * isolatedVertexTransformedNaturalSide U p + 1) := by
  classical
  let points := depthSevenNormalizedDisplacementFinset p x₀ equations CF
  let transformedPoints : Finset (IntVector 13) :=
    points.map U.pointEquiv.toEmbedding
  have hbox : ∀ y ∈ transformedPoints,
      (y 0).natAbs ≤ isolatedVertexTransformedNaturalSide U p := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hy
    exact pointEquiv_coordinate_le_isolatedVertexTransformedNaturalSide
      U p x₀ equations CF hz 0
  have hbound := card_le_dropFirst_image_mul_interval transformedPoints hbox
  have hcard : transformedPoints.card = points.card := Finset.card_map _
  have himage : transformedPoints.image dropFirstIntVector =
      isolatedVertexQuotientPointFinset U p x₀ equations CF := by
    ext w
    constructor
    · intro hw
      obtain ⟨y, hy, hyw⟩ := Finset.mem_image.mp hw
      obtain ⟨z, hz, hzy⟩ := Finset.mem_map.mp hy
      apply Finset.mem_image.mpr
      refine ⟨z, ?_, ?_⟩
      · simpa [points] using hz
      · exact (congrArg dropFirstIntVector hzy).trans hyw
    · intro hw
      obtain ⟨z, hz, hzw⟩ := Finset.mem_image.mp hw
      apply Finset.mem_image.mpr
      refine ⟨U.pointEquiv z, ?_, ?_⟩
      · apply Finset.mem_map.mpr
        exact ⟨z, by simpa [points] using hz, rfl⟩
      · exact hzw
  simpa [hcard, himage, points] using hbound

/-- If the affine images of the normalized points vanish on the original
integral equations, every literal quotient point vanishes on the correctly
translated and rescaled lower-dimensional equation family. -/
theorem isolatedVertexQuotientPoint_mem_lowerAffineZeroLocus
    (U : IntegralUnimodularChange 13)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (equationsI : Finset (MvPolynomial (Fin 13) ℤ))
    (hzero : ∀ x : IntVector 13,
      IntegralCommonZero (liftEquationFinsetAfterFirst lowerEquations)
          (U.pointEquiv x) ↔ IntegralCommonZero equationsI x)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (hpoints : ∀ z ∈ depthSevenNormalizedDisplacementFinset
        p x₀ equations CF,
      IntegralCommonZero equationsI (integralAffineMap x₀ z p.m))
    {w : IntVector 12}
    (hw : w ∈ isolatedVertexQuotientPointFinset U p x₀ equations CF) :
    w ∈ integralCommonZeroInBox
      (M := isolatedVertexTransformedNaturalSide U p)
      (integralAffineTransformEquationFinset
        (dropFirstIntVector (U.pointEquiv x₀)) p.m lowerEquations) := by
  obtain ⟨z, hz, hzw⟩ :=
    (mem_isolatedVertexQuotientPointFinset_iff
      U p x₀ equations CF w).1 hw
  apply (mem_integralCommonZeroInBox_iff _ _).2
  constructor
  · intro i
    rw [← hzw]
    exact pointEquiv_coordinate_le_isolatedVertexTransformedNaturalSide
      U p x₀ equations CF hz i.succ
  · apply (integralCommonZero_transform_iff
      (dropFirstIntVector (U.pointEquiv x₀)) w p.m lowerEquations).2
    have htransformed : IntegralCommonZero
        (liftEquationFinsetAfterFirst lowerEquations)
        (U.pointEquiv (integralAffineMap x₀ z p.m)) :=
      (hzero (integralAffineMap x₀ z p.m)).2 (hpoints z hz)
    have hlower :=
      (integralCommonZero_liftEquationFinsetAfterFirst_iff
        lowerEquations
        (U.pointEquiv (integralAffineMap x₀ z p.m))).1 htransformed
    rw [U.pointEquiv_integralAffineMap,
      dropFirstIntVector_integralAffineMap, hzw] at hlower
    exact hlower

/-- Exact affine quotient reduction for the literal normalized point set.

The conclusion retains the quotient set as an image of the original set.
Thus every exclusion appearing in `depthSevenNormalizedDisplacementFinset`
is retained, while membership in the translated twelve-variable zero locus
is also available for the second reservoir argument. -/
theorem exists_isolatedVertex_affineQuotientReduction
    (hvertexTheorem : StandardAG.ProjectiveVertexIdealTranslationStability)
    (hcylinder : StandardAG.TranslationStableHomogeneousIdealCylinderGenerators)
    (hcompletion : StandardLattice.PrimitiveDirectionUnimodularCompletion)
    (I : Ideal (MvPolynomial (Fin 13) ℚ))
    (hIradical : I.IsRadical)
    (hIhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ))
    (h : IntVector 13) (hprimitive : PrimitiveDirection h)
    (hvertex : LiesInGeometricProjectiveVertex h I) :
    ∃ (equationsI : Finset (MvPolynomial (Fin 13) ℤ))
        (U : IntegralUnimodularChange 13)
        (lowerHomogeneousEquations : Finset (MvPolynomial (Fin 12) ℤ)),
      Ideal.map (MvPolynomial.map (Int.castRingHom ℚ))
          (Ideal.span (equationsI : Set (MvPolynomial (Fin 13) ℤ))) = I ∧
      Matrix.mulVec U.forward h = firstCoordinateIntDirection ∧
      U.transformEquationFinset equationsI =
          liftEquationFinsetAfterFirst lowerHomogeneousEquations ∧
      (∀ g ∈ lowerHomogeneousEquations, ∃ d : ℕ, g.IsHomogeneous d) ∧
      ∀ (p : Parameters) (x₀ : IntVector 13)
          (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ),
        (∀ z ∈ depthSevenNormalizedDisplacementFinset p x₀ equations CF,
          IntegralPointVanishesOnRationalIdeal I
            (integralAffineMap x₀ z p.m)) →
        (isolatedVertexQuotientPointFinset U p x₀ equations CF ⊆
          integralCommonZeroInBox
            (M := isolatedVertexTransformedNaturalSide U p)
            (integralAffineTransformEquationFinset
              (dropFirstIntVector (U.pointEquiv x₀)) p.m
              lowerHomogeneousEquations)) ∧
        (depthSevenNormalizedDisplacementFinset p x₀ equations CF).card ≤
          (isolatedVertexQuotientPointFinset U p x₀ equations CF).card *
            (2 * isolatedVertexTransformedNaturalSide U p + 1) := by
  obtain ⟨equationsI, U, lowerEquations, hideal, hforward,
      hfamily, hhomogeneous, hzero⟩ :=
    exists_unimodular_firstCoordinateEquationReduction_of_projectiveVertex
      hvertexTheorem hcylinder hcompletion I hIradical hIhomogeneous h
        hprimitive hvertex
  refine ⟨equationsI, U, lowerEquations, hideal, hforward, hfamily,
    hhomogeneous, ?_⟩
  intro p x₀ equations CF hpoints
  constructor
  · intro w hw
    apply isolatedVertexQuotientPoint_mem_lowerAffineZeroLocus
      U lowerEquations equationsI hzero p x₀ equations CF
    · intro z hz
      exact integralCommonZero_of_vanishesOnRationalIdeal I equationsI
        hideal (integralAffineMap x₀ z p.m) (hpoints z hz)
    · exact hw
  · exact card_depthSevenNormalizedDisplacementFinset_le_quotient_mul_fibre
      U p x₀ equations CF

/-- Correct affine form of the isolated-vertex product bound.

The normalized displacement `z` need not vanish on the original homogeneous
ideal.  Its affine image `x₀ + m z` does.  After applying the fixed
unimodular matrix, the lower-dimensional equations must therefore be
translated by the lower coordinates of `U x₀` and rescaled by `m`.  This
theorem performs that substitution literally and then applies only the
elementary finite-fibre estimate. -/
theorem isolatedVertex_affineProductBound_on_normalizedDisplacements
    (hvertexTheorem : StandardAG.ProjectiveVertexIdealTranslationStability)
    (hcylinder : StandardAG.TranslationStableHomogeneousIdealCylinderGenerators)
    (hcompletion : StandardLattice.PrimitiveDirectionUnimodularCompletion)
    (I : Ideal (MvPolynomial (Fin 13) ℚ))
    (hIradical : I.IsRadical)
    (hIhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ))
    (h : IntVector 13) (hprimitive : PrimitiveDirection h)
    (hvertex : LiesInGeometricProjectiveVertex h I) :
    ∃ (equationsI : Finset (MvPolynomial (Fin 13) ℤ))
        (U : IntegralUnimodularChange 13)
        (lowerHomogeneousEquations : Finset (MvPolynomial (Fin 12) ℤ)),
      Ideal.map (MvPolynomial.map (Int.castRingHom ℚ))
          (Ideal.span (equationsI : Set (MvPolynomial (Fin 13) ℤ))) = I ∧
      Matrix.mulVec U.forward h = firstCoordinateIntDirection ∧
      U.transformEquationFinset equationsI =
          liftEquationFinsetAfterFirst lowerHomogeneousEquations ∧
      (∀ g ∈ lowerHomogeneousEquations, ∃ d : ℕ, g.IsHomogeneous d) ∧
      ∀ (p : Parameters) (x₀ : IntVector 13)
          (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ),
        (∀ z ∈ depthSevenNormalizedDisplacementFinset p x₀ equations CF,
          IntegralPointVanishesOnRationalIdeal I
            (integralAffineMap x₀ z p.m)) →
        (depthSevenNormalizedDisplacementFinset p x₀ equations CF).card ≤
          (2 * isolatedVertexTransformedNaturalSide U p + 1) *
            (integralCommonZeroInBox
              (M := isolatedVertexTransformedNaturalSide U p)
              (integralAffineTransformEquationFinset
                (dropFirstIntVector (U.pointEquiv x₀)) p.m
                lowerHomogeneousEquations)).card := by
  obtain ⟨equationsI, U, lowerEquations, hideal, hforward,
      hfamily, hhomogeneous, hreduction⟩ :=
    exists_isolatedVertex_affineQuotientReduction
      hvertexTheorem hcylinder hcompletion I hIradical hIhomogeneous h
        hprimitive hvertex
  refine ⟨equationsI, U, lowerEquations, hideal, hforward, hfamily,
    hhomogeneous, ?_⟩
  intro p x₀ equations CF hpoints
  obtain ⟨hsubset, hcard⟩ := hreduction p x₀ equations CF hpoints
  have hquotient := Finset.card_le_card hsubset
  calc
    (depthSevenNormalizedDisplacementFinset p x₀ equations CF).card ≤
        (isolatedVertexQuotientPointFinset U p x₀ equations CF).card *
          (2 * isolatedVertexTransformedNaturalSide U p + 1) := hcard
    _ ≤ (integralCommonZeroInBox
          (M := isolatedVertexTransformedNaturalSide U p)
          (integralAffineTransformEquationFinset
            (dropFirstIntVector (U.pointEquiv x₀)) p.m
            lowerEquations)).card *
        (2 * isolatedVertexTransformedNaturalSide U p + 1) :=
      Nat.mul_le_mul_right _ hquotient
    _ = (2 * isolatedVertexTransformedNaturalSide U p + 1) *
        (integralCommonZeroInBox
          (M := isolatedVertexTransformedNaturalSide U p)
          (integralAffineTransformEquationFinset
            (dropFirstIntVector (U.pointEquiv x₀)) p.m
            lowerEquations)).card := Nat.mul_comm _ _

end

end TranslatedDepthSeven
