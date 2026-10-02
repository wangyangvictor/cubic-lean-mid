import HessianTheorem11.UnconditionalValuativeImage
import HessianTheorem11.UnconditionalOrbitBoundary

/-! Actual special-linear generic matrices and valuative specializations of
their coefficient orbits. No orbit-closure degeneration theorem is an input. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
namespace HessianTheorem11.UnconditionalValuativeOrbit
open MvPolynomial Ideal PolynomialRestriction PolynomialWeightTransport
  NonzeroLimitTransport UnconditionalFiberClosed UnconditionalValuative
  UnconditionalChevalley UnconditionalOrbitIdeal UnconditionalPolynomialOrbit

abbrev SLCoordinateRing (n : ℕ) :=
  CoordinateRing (UnconditionalSpecialLinear.specialLinearLocus n)

instance slIdeal_isPrime (n : ℕ) :
    (vanishingIdeal GeometricField (UnconditionalSpecialLinear.specialLinearLocus n)).IsPrime :=
  UnconditionalSpecialLinear.specialLinearLocus_irreducible n

abbrev SLFunctionField (n : ℕ) := FractionRing (SLCoordinateRing n)

def genericSLMatrix (n : ℕ) : Matrix (Fin n) (Fin n) (SLFunctionField n) :=
  fun i j => genericPoint (UnconditionalSpecialLinear.specialLinearLocus n) (i,j)

theorem genericSLMatrix_det (n : ℕ) : (genericSLMatrix n).det = 1 := by
  let Z := UnconditionalSpecialLinear.specialLinearLocus n
  have hp : UnconditionalSpecialLinear.determinantPolynomial n - 1 ∈
      vanishingIdeal GeometricField Z := by
    intro x hx
    change eval x (UnconditionalSpecialLinear.determinantPolynomial n - 1) = 0
    simp only [map_sub,map_one,UnconditionalSpecialLinear.eval_determinantPolynomial]
    exact sub_eq_zero.mpr hx
  have he := genericPoint_equations Z _ hp
  have he' : eval₂ (algebraMap GeometricField (SLFunctionField n)) (genericPoint Z)
      (UnconditionalSpecialLinear.determinantPolynomial n) = 1 := by
    simpa only [eval₂_sub,eval₂_one,sub_eq_zero] using he
  have hd : eval₂ (algebraMap GeometricField (SLFunctionField n)) (genericPoint Z)
      (UnconditionalSpecialLinear.determinantPolynomial n) = (genericSLMatrix n).det := by
    change (eval₂Hom _ _) (Matrix.det _) = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [genericSLMatrix,Z]
  rwa [hd] at he'

theorem eval_generic_orbit_coefficient {n d : ℕ} (F : GeometricPolynomial n)
    (e : DegreeIndex n d) :
    eval₂ (algebraMap GeometricField (SLFunctionField n))
      (genericPoint (UnconditionalSpecialLinear.specialLinearLocus n))
      (orbitPolynomials F e) =
    coeff e.val (restrict (genericSLMatrix n)
      (map (algebraMap GeometricField (SLFunctionField n)) F)) := by
  let h := eval₂Hom (algebraMap GeometricField (SLFunctionField n))
    (genericPoint (UnconditionalSpecialLinear.specialLinearLocus n))
  change h (coeff e.val (universalRestriction F)) = _
  rw [← coeff_map,universalRestriction,map_restrict,MvPolynomial.map_map]
  have hM : (UnconditionalPolynomialOrbit.genericMatrix n).map h = genericSLMatrix n := by
    ext i j
    simp [UnconditionalPolynomialOrbit.genericMatrix,genericSLMatrix,h]
  have hC : h.comp C = algebraMap GeometricField (SLFunctionField n) := by
    ext z
    simp [h]
  rw [hM,hC]

/-- The generic SL orbit has coefficients in a valuation ring specializing
to any chosen coefficient-closure point. All coefficient equations have
exactly the prescribed residue values, expressed by their vanishing. -/
theorem exists_orbit_valuation {n d : ℕ} (F G : GeometricPolynomial n)
    (hG : G ∈ slOrbitClosure F) :
    ∃ V : ValuationSubring (SLFunctionField n), ∃ c : GeometricField →+* V,
      ∃ a : DegreeIndex n d → V,
      (∀ z, (c z : SLFunctionField n) = algebraMap GeometricField (SLFunctionField n) z) ∧
      (∀ e, (a e : SLFunctionField n) = coeff e.val
        (restrict (genericSLMatrix n) (map (algebraMap GeometricField (SLFunctionField n)) F))) ∧
      (∀ q : MvPolynomial (DegreeIndex n d) GeometricField,
        eval₂ c a q ∈ IsLocalRing.maximalIdeal V ↔ eval (coefficientVector G) q = 0) := by
  let Z := UnconditionalSpecialLinear.specialLinearLocus n
  let P := orbitPolynomials (d := d) F
  have hy := UnconditionalOrbitBoundary.coefficientVector_mem_imageClosure (d := d) F G hG
  obtain ⟨V,g,hg,hcenter⟩ := exists_image_valuation P Z
    (UnconditionalSpecialLinear.specialLinearLocus_irreducible n) (coefficientVector G) hy
  let j : MvPolynomial (DegreeIndex n d) GeometricField →+* V :=
    g.comp (Ideal.Quotient.mk (vanishingIdeal GeometricField (polynomialMap P '' Z)))
  let c : GeometricField →+* V := j.comp C
  let a : DegreeIndex n d → V := fun e => j (X e)
  have hj : eval₂Hom c a = j := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [c]
    · intro e
      simp [a]
  refine ⟨V,c,a,?_,?_,?_⟩
  · intro z
    change (g (Ideal.Quotient.mk _ (C z)) : SLFunctionField n) = _
    rw [hg]
    simp [Z,SLFunctionField,SLCoordinateRing]
  · intro e
    change (g (Ideal.Quotient.mk _ (X e)) : SLFunctionField n) = _
    rw [hg]
    simpa only [aeval_X] using eval_generic_orbit_coefficient (d := d) F e
  · intro q
    change eval₂Hom c a q ∈ _ ↔ _
    rw [hj]
    exact hcenter q

end HessianTheorem11.UnconditionalValuativeOrbit
