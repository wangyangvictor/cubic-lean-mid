import TranslatedDepthSeven.RankSevenPersistentPlaneRecords
import TranslatedDepthSeven.RankSevenDegreeOneLowDirectionSource
import TranslatedDepthSeven.ProjectivePlaneAffineLine

/-!
# Full-line and star incidence for actual persistent planes

The only geometric input is the classical fact that an integral projective
surface of degree one is a linear plane.  Its prime and homogeneous ideal
hypotheses are verified for the actual retained component.  Every subsequent
incidence is deduced from the displayed divided-difference identity and the
literal source-section ideal.  In particular no star containment is assumed.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

namespace StandardAG

/-- The affine cone over an integral projective degree-one surface is a
linear subspace. This is the ordinary degree-one-variety theorem, with no
point count or assertion about translated families included. -/
def DegreeOneProjectiveSurfaceConeIsLinear : Prop :=
  ∀ (N : ℕ) (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
    I.IsPrime →
    I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
    HasProjectiveDimensionDegree I 2 1 →
    ∃ L : Submodule ℚ (Fin (N + 1) → ℚ),
      (L : Set (Fin (N + 1) → ℚ)) = affineIdealZeroLocus I

end StandardAG

section LiteralFamily

variable (p : Parameters) (x₀ : IntVector 13)
  (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
  (C : IntegralDepthSevenJacobianChartIndex equations)
  (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
  (hP : ∀ s ∈ P, s.Prime)
  (hlower : ∀ q : ReservoirModulus P k,
    manuscriptReservoirTarget normalizedSurfaceReservoirConstant
      p.T (5 / 7) ≤ q.1)
  (X : Finset (IntVector 13)) (markCount : ℕ)
  (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
  (selectedVar : Fin 11 → Fin 13)
  (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
  (markOf : IntVector 13 → Fin markCount)

local notation "PlaneOccurrence" =>
  RankSevenPersistentPlaneOccurrence p x₀ equations CF C denominator P k
    hP hlower X markCount localEquations selectedVar menu markOf

local notation "planeCell" =>
  rankSevenPersistentPlanePointCell p x₀ equations CF C denominator P k
    hP hlower X markCount localEquations selectedVar menu markOf

local notation "planeBase" =>
  rankSevenPersistentPlaneRepresentative p x₀ equations CF C denominator P k
    hP hlower X markCount localEquations selectedVar menu markOf

local notation "dividedDifference" =>
  rankSevenPersistentPlaneDividedDifference p x₀ equations CF C denominator P k
    hP hlower X markCount localEquations selectedVar menu markOf

theorem rankSevenPersistentPlaneComponent_mem_nodeComponents
    (o : PlaneOccurrence) :
    o.1.component ∈ finiteMinimalPrimes
      (rankSevenNodeEquationIdeal p x₀ equations CF C
        o.1.modulus.1 o.1.residue) := by
  have hplaneRecord := (mem_occupiedRankSevenPersistentPlaneRecords_iff
    p x₀ equations CF C denominator P k hP hlower X markCount
      localEquations selectedVar menu markOf o.1).mp o.2
  have hretained := (mem_occupiedRankSevenPersistentMultiplicityOneRecords_iff
    p x₀ equations CF C denominator P k markCount hP hlower X
      localEquations selectedVar menu markOf o.1).mp hplaneRecord.1 |>.1
  have hsurface := (mem_occupiedRankSevenPersistentRecords_iff
    p x₀ equations CF C P k markCount o.1).mp hretained |>.2
  exact (mem_rankSevenSurfaceNodeComponents_iff
    p x₀ equations CF C o.1.modulus.1 o.1.residue o.1.component).mp hsurface |>.1

/-- Apply the standard degree-one theorem to the literal retained ideal;
primality and homogeneity are not included in the record by fiat. -/
theorem exists_rankSevenPersistentPlane_linearCone
    (hplane : StandardAG.DegreeOneProjectiveSurfaceConeIsLinear)
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    (o : PlaneOccurrence) :
    ∃ L : Submodule ℚ (Fin 14 → ℚ),
      (L : Set (Fin 14 → ℚ)) = affineIdealZeroLocus o.1.component := by
  have hnode := rankSevenPersistentPlaneComponent_mem_nodeComponents
    p x₀ equations CF C denominator P k hP hlower X markCount
      localEquations selectedVar menu markOf o
  apply hplane 13 o.1.component
  · exact rankSevenNodeComponent_isPrime p x₀ equations CF C
      o.1.modulus.1 o.1.residue o.1.component hnode
  · exact rankSevenNodeComponent_isHomogeneous p x₀ equations CF hhomogeneous C
      o.1.modulus.1 o.1.residue o.1.component hnode
  · exact (mem_occupiedRankSevenPersistentPlaneRecords_iff
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf o.1).mp o.2 |>.2

/-- Every integral line in a rational combination of the two actual divided
differences belongs to the original fixed cone after `z ↦ x₀ + m z`. -/
theorem rankSevenPersistentPlane_fullLine_commonZero
    (hplane : StandardAG.DegreeOneProjectiveSurfaceConeIsLinear)
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    (o : PlaneOccurrence) (z₁ z₂ : IntVector 13)
    (hz₁ : z₁ ∈ planeCell o) (hz₂ : z₂ ∈ planeCell o)
    (h : IntVector 13) (a b : ℤ) (r : ℚ)
    (hscale : ∀ i, (h i : ℚ) = r *
      ((a * dividedDifference o z₁ i + b * dividedDifference o z₂ i : ℤ) : ℚ))
    (z : IntVector 13) (hz : z ∈ planeCell o) (t : ℤ) :
    IntegralCommonZero equations
      (fun i ↦ integralAffineMap x₀ z p.m i + t * ((p.m : ℤ) * h i)) := by
  obtain ⟨L, hL⟩ := exists_rankSevenPersistentPlane_linearCone
    p x₀ equations CF C denominator P k hP hlower X markCount
      localEquations selectedVar menu markOf hplane hhomogeneous o
  have hpoint (w : IntVector 13) (hw : w ∈ planeCell o) :
      (fun i ↦ (integralAffineChartVector w i : ℚ)) ∈ L := by
    change (fun i ↦ (integralAffineChartVector w i : ℚ)) ∈
      (L : Set (Fin 14 → ℚ))
    rw [hL]
    exact (mem_rankSevenPersistentRecordPointCell_iff
      p x₀ equations CF C markOf o.1 w).mp hw |>.2.2.1
  have hline := integralAffineChartLine_mem_of_dividedDifferences
    L (planeBase o) z z₁ z₂ (dividedDifference o z₁)
      (dividedDifference o z₂) h (rankSevenPersistentPlaneModulus o)
      (rankSevenPersistentPlaneModulus_pos p x₀ equations CF C denominator P k
        hP hlower X markCount localEquations selectedVar menu markOf o)
      (hpoint _ (rankSevenPersistentPlaneRepresentative_mem
        p x₀ equations CF C denominator P k hP hlower X markCount
          localEquations selectedVar menu markOf o))
      (hpoint z hz) (hpoint z₁ hz₁) (hpoint z₂ hz₂)
      (rankSevenPersistentPlaneDividedDifference_spec p x₀ equations CF C
        denominator P k hP hlower X markCount localEquations selectedVar
          menu markOf o hz₁)
      (rankSevenPersistentPlaneDividedDifference_spec p x₀ equations CF C
        denominator P k hP hlower X markCount localEquations selectedVar
          menu markOf o hz₂) a b r hscale t
  have hcomponent :
      (fun i ↦ (integralAffineChartVector (fun j ↦ z j + t * h j) i : ℚ)) ∈
        affineIdealZeroLocus o.1.component := by
    rw [← hL]
    exact hline
  have hnode := rankSevenPersistentPlaneComponent_mem_nodeComponents
    p x₀ equations CF C denominator P k hP hlower X markCount
      localEquations selectedVar menu markOf o
  have hsource :
      (fun i ↦ (integralAffineChartVector (fun j ↦ z j + t * h j) i : ℚ)) ∈
        affineIdealZeroLocus (rankSevenNodeEquationIdeal p x₀ equations CF C
          o.1.modulus.1 o.1.residue) :=
    fun f hf ↦ hcomponent f (le_of_mem_finiteMinimalPrimes hnode hf)
  have hzero := integralCommonZero_of_intPoint_mem_rankSevenNodeEquationIdeal
    p x₀ equations CF hhomogeneous C o.1.modulus.1 o.1.residue
      (fun j ↦ z j + t * h j) hsource
  convert hzero using 1
  ext i
  simp only [integralAffineMap]
  ring

/-- The selected direction itself is a point of the original homogeneous
cone. This follows from the leading coefficient of a polynomial restricted
to the full affine line, followed by cancelling the nonzero factor `m`. -/
theorem rankSevenPersistentPlane_direction_commonZero
    (hplane : StandardAG.DegreeOneProjectiveSurfaceConeIsLinear)
    (degree : MvPolynomial (Fin 13) ℤ → ℕ)
    (hdegree : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    (o : PlaneOccurrence) (z₁ z₂ : IntVector 13)
    (hz₁ : z₁ ∈ planeCell o) (hz₂ : z₂ ∈ planeCell o)
    (h : IntVector 13) (a b : ℤ) (r : ℚ)
    (hscale : ∀ i, (h i : ℚ) = r *
      ((a * dividedDifference o z₁ i + b * dividedDifference o z₂ i : ℤ) : ℚ)) :
    IntegralCommonZero equations h := by
  intro f hf
  have hline : ∀ t : ℤ, MvPolynomial.eval
      (fun i ↦ integralAffineMap x₀ z₁ p.m i + t * ((p.m : ℤ) * h i)) f = 0 :=
    fun t ↦ rankSevenPersistentPlane_fullLine_commonZero
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf hplane
        (fun f hf ↦ ⟨degree f, hdegree f hf⟩) o z₁ z₂ hz₁ hz₂
        h a b r hscale z₁ hz₁ t f hf
  have hzero := eval_direction_eq_zero_of_isHomogeneous_of_eval_line_zero
    f (integralAffineMap x₀ z₁ p.m) (fun i ↦ (p.m : ℤ) * h i)
      (degree f) (hdegree f hf) hline
  have hscaled : MvPolynomial.eval (fun i ↦ (p.m : ℤ) * h i) f =
      (p.m : ℤ) ^ degree f * MvPolynomial.eval h f :=
    eval_smul_of_isHomogeneous f h (p.m : ℤ) (degree f) (hdegree f hf)
  rw [hscaled] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left
    (pow_ne_zero _ (by exact_mod_cast p.hm.ne'))

/-- After grouping by the selected direction, every original nonzero point
lies on the single star centred at that direction. -/
theorem rankSevenPersistentPlane_originalPoint_mem_star
    (hplane : StandardAG.DegreeOneProjectiveSurfaceConeIsLinear)
    (degree : MvPolynomial (Fin 13) ℤ → ℕ)
    (hdegree : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    (o : PlaneOccurrence) (z₁ z₂ : IntVector 13)
    (hz₁ : z₁ ∈ planeCell o) (hz₂ : z₂ ∈ planeCell o)
    (h : IntVector 13) (a b : ℤ) (r : ℚ)
    (hscale : ∀ i, (h i : ℚ) = r *
      ((a * dividedDifference o z₁ i + b * dividedDifference o z₂ i : ℤ) : ℚ))
    (z : IntVector 13) (hz : z ∈ planeCell o)
    (hnonzero : integralAffineMap x₀ z p.m ≠ 0) :
    integralProjectiveClass (integralAffineMap x₀ z p.m) hnonzero ∈
      integralProjectiveStarLocus equations degree h := by
  apply basePoint_mem_projectiveStar_of_scaledIntegralLine
    equations degree hdegree (integralAffineMap x₀ z p.m) h p.m p.hm hnonzero
  intro t
  exact rankSevenPersistentPlane_fullLine_commonZero
    p x₀ equations CF C denominator P k hP hlower X markCount
      localEquations selectedVar menu markOf hplane
      (fun f hf ↦ ⟨degree f, hdegree f hf⟩) o z₁ z₂ hz₁ hz₂
      h a b r hscale z hz t

end LiteralFamily

end

end TranslatedDepthSeven
