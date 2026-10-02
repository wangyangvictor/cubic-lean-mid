import CubicTenVariables.FixedIntegralSurfacePointCount
import TranslatedDepthSeven.HypersurfaceOccupiedSmoothResidues
import TranslatedDepthSeven.HypersurfaceSurfaceResidueDiscFirstChart
import TranslatedDepthSeven.QuantitativePrefixSurfaceCountEffective
import Mathlib.Data.Nat.Prime.Factorial

/-!
# Prime-field form of the fixed integral surface point count

The fixed-surface slicing theorem counts the standard affine chart written
directly as `F(1,x)=0`.  The determinant-method interface uses instead the
zero set of the integral dehomogenization after reduction.  This file proves
that these are literally the same finite point set and packages the finite
field threshold and bad-characteristic integer into one positive natural
exceptional divisor.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace TranslatedDepthSeven

open MvPolynomial
open Published
open CubicTenVariables
open HessianTheorem11
open CubicTenVariables.FixedIntegralSurfacePointCount
open CubicTenVariables.SurfacePointCountByPlaneSlices
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Reduction commutes with the literal first-chart dehomogenization. -/
theorem map_surfaceHypersurfaceFirstChartDehomogenize
    (p : ℕ) (F : MvPolynomial (Fin 4) ℤ) :
    map (Int.castRingHom (ZMod p))
        (surfaceHypersurfaceFirstChartDehomogenize F) =
      eval₂Hom C (Fin.cases 1 X)
        (map (Int.castRingHom (ZMod p)) F) := by
  change map (Int.castRingHom (ZMod p))
      (eval₂ C (Fin.cases 1 X) F) =
    eval₂ C (Fin.cases 1 X) (map (Int.castRingHom (ZMod p)) F)
  rw [map_eval₂]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp

/-- The reduction-zero point type is equivalent to the standard affine-chart
point type counted by `exists_fixed_integral_surface_point_count`. -/
def surfaceReductionZeroPointEquivStandardChart
    (p : ℕ) (F : MvPolynomial (Fin 4) ℤ) :
    SurfaceReductionZeroPoint p (surfaceHypersurfaceFirstChartDehomogenize F) ≃
      {x : Fin 3 → ZMod p //
        eval (Fin.cases 1 x) (map (Int.castRingHom (ZMod p)) F) = 0} :=
  Equiv.subtypeEquivRight (fun x ↦ by
    have heval :
        eval x (map (Int.castRingHom (ZMod p))
          (surfaceHypersurfaceFirstChartDehomogenize F)) =
        eval (Fin.cases 1 x) (map (Int.castRingHom (ZMod p)) F) := by
      rw [map_surfaceHypersurfaceFirstChartDehomogenize]
      change eval x (eval₂ C (Fin.cases 1 X)
        (map (Int.castRingHom (ZMod p)) F)) = _
      rw [eval_eval₂]
      have hcoeff : (eval x).comp C = RingHom.id (ZMod p) := by
        ext z
        simp
      have hcoords : (fun i : Fin 4 ↦ eval x (Fin.cases 1 X i)) =
          Fin.cases 1 x := by
        funext i
        refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
      rw [hcoeff, hcoords, eval₂_id]
    rw [heval])

/-- The corresponding point counts are equal, with no geometric or
characteristic hypothesis. -/
theorem card_surfaceReductionZeroPoint_eq_standardChart
    (p : ℕ) (F : MvPolynomial (Fin 4) ℤ) :
    Nat.card
        (SurfaceReductionZeroPoint p
          (surfaceHypersurfaceFirstChartDehomogenize F)) =
      Nat.card {x : Fin 3 → ZMod p //
        eval (Fin.cases 1 x) (map (Int.castRingHom (ZMod p)) F) = 0} :=
  Nat.card_congr (surfaceReductionZeroPointEquivStandardChart p F)

/-- A fixed geometrically integral homogeneous surface has the exact
prime-field point-count hypothesis consumed by the quantitative determinant
method, away from one positive natural integer.  Only the geometric
integrality openness input and affine plane-curve Weil input used by the
fixed-surface slicing theorem remain explicit. -/
theorem exists_fixed_integral_surface_prime_count
    (integralityOpen : Literature.HomogeneousHypersurfaceIntegralityOpen)
    (curveWeil : Literature.AffinePlaneCurveWeil)
    {d : ℕ} (hd : 2 ≤ d)
    (F : MvPolynomial (Fin 4) ℤ) (hF0 : F ≠ 0)
    (hF : F.IsHomogeneous d)
    (hgeom : IsDomain (MvPolynomial (Fin 4) GeometricField ⧸
      Ideal.span {map (Int.castRingHom GeometricField) F}))
    (K₀ : ℝ) (hK₀ : 1 < K₀) :
    ∃ Dex : ℕ, 0 < Dex ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ Dex →
        (Nat.card (SurfaceReductionZeroPoint p
          (surfaceHypersurfaceFirstChartDehomogenize F)) : ℝ) ≤
            K₀ * (p : ℝ) ^ 2 := by
  obtain ⟨_, N, g, _, _, _, hN, hcount⟩ :=
    exists_fixed_integral_surface_point_count
      integralityOpen curveWeil hd F hF0 hF hgeom K₀ hK₀
  let T : ℕ := Nat.ceil
    (surfaceSliceThreshold curveWeil d (by omega) g.totalDegree K₀)
  let Dex : ℕ := N.natAbs * T.factorial
  have hNabs : 0 < N.natAbs := Int.natAbs_pos.mpr hN
  have hDex : 0 < Dex := Nat.mul_pos hNabs (Nat.factorial_pos T)
  refine ⟨Dex, hDex, ?_⟩
  intro p hp hpDex
  letI : Fact p.Prime := ⟨hp⟩
  have hpNabs : ¬ p ∣ N.natAbs := fun h ↦
    hpDex (dvd_mul_of_dvd_left h T.factorial)
  have hpFact : ¬ p ∣ T.factorial := fun h ↦
    hpDex (dvd_mul_of_dvd_right h N.natAbs)
  have hNmod : (N : ZMod p) ≠ 0 :=
    intCast_zmod_ne_zero_of_not_dvd_natAbs N p hpNabs
  have hTp : T < p := by
    rw [hp.dvd_factorial] at hpFact
    exact lt_of_not_ge hpFact
  have hthreshold :
      surfaceSliceThreshold curveWeil d (by omega) g.totalDegree K₀ ≤
        (Fintype.card (ZMod p) : ℝ) := by
    rw [ZMod.card]
    exact (Nat.le_ceil _).trans (by exact_mod_cast hTp.le)
  rw [card_surfaceReductionZeroPoint_eq_standardChart]
  simpa only [ZMod.card] using hcount (ZMod p) hNmod hthreshold

/-- The same exceptional integer supplies the point-count hypothesis after
it is multiplied into any larger exceptional modulus.  This is the form used
when the point-count exclusion is combined with the determinant method's
other fixed exceptional factors. -/
theorem exists_fixed_integral_surface_prime_count_of_multiple
    (integralityOpen : Literature.HomogeneousHypersurfaceIntegralityOpen)
    (curveWeil : Literature.AffinePlaneCurveWeil)
    {d : ℕ} (hd : 2 ≤ d)
    (F : MvPolynomial (Fin 4) ℤ) (hF0 : F ≠ 0)
    (hF : F.IsHomogeneous d)
    (hgeom : IsDomain (MvPolynomial (Fin 4) GeometricField ⧸
      Ideal.span {map (Int.castRingHom GeometricField) F}))
    (K₀ : ℝ) (hK₀ : 1 < K₀) :
    ∃ Dsurface : ℕ, 0 < Dsurface ∧
      ∀ Dex : ℕ, Dsurface ∣ Dex →
        ∀ p : ℕ, p.Prime → ¬ p ∣ Dex →
          (Nat.card (SurfaceReductionZeroPoint p
            (surfaceHypersurfaceFirstChartDehomogenize F)) : ℝ) ≤
              K₀ * (p : ℝ) ^ 2 := by
  obtain ⟨Dsurface, hDsurface, hcount⟩ :=
    exists_fixed_integral_surface_prime_count
      integralityOpen curveWeil hd F hF0 hF hgeom K₀ hK₀
  refine ⟨Dsurface, hDsurface, ?_⟩
  intro Dex hdiv p hp hpDex
  exact hcount p hp (fun hpDsurface ↦ hpDex (hpDsurface.trans hdiv))

/-- Effective quantitative surface-count endpoint with its prime-field
surface bound discharged by the fixed integral surface theorem.  The one new
divisibility condition says that the global exceptional modulus contains the
fixed surface-count factor. -/
theorem
    exists_fixedSurface_quantitativePrefixSurfaceCount_effective_of_integralSurface
    (integralityOpen : Literature.HomogeneousHypersurfaceIntegralityOpen)
    (curveWeil : Literature.AffinePlaneCurveWeil)
    (hCurve : CDHNV2025Corollary22)
    {d : ℕ} (hd : 2 ≤ d)
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    (hprime : (finiteEquationIdeal sourceEquations).IsPrime)
    (hgeometricPrime : ((finiteEquationIdeal sourceEquations).map
      (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime)
    (hhom : (finiteEquationIdeal sourceEquations).IsHomogeneous
      (homogeneousSubmodule (Fin 4) ℚ))
    (hchart : MvPolynomial.X 0 ∉ finiteEquationIdeal sourceEquations)
    (hdegree : HasProjectiveDimensionDegree
      (finiteEquationIdeal sourceEquations) 2 d)
    (F : MvPolynomial (Fin 4) ℤ) (hF0 : F ≠ 0)
    (hF : F.IsHomogeneous d)
    (hgeom : IsDomain (MvPolynomial (Fin 4) GeometricField ⧸
      Ideal.span {map (Int.castRingHom GeometricField) F}))
    (Kred : ℝ) (hKred : 1 < Kred) (Aex : ℕ)
    (η a : ℝ) (hη : 0 < η)
    (ha : Real.sqrt Kred / Real.sqrt (d : ℝ) < a) :
    ∃ Dsurface b D A H₀ : ℕ, ∃ Cdet Ccurve : ℝ,
      0 < Dsurface ∧
      1 ≤ D ∧ 2 ≤ A ∧ 2 ≤ H₀ ∧ 0 ≤ Cdet ∧ 0 < Ccurve ∧
      ∀ (P : Finset ℕ) (depth H Baux Bpoint m Dex : ℕ)
        (u : IntVector 3) (X : Finset (IntVector 3))
        (allowed : IntVector 3 → Finset ℕ) (z₀ : IntVector 3),
      Dsurface ∣ Dex →
      (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, ¬ p ∣ m) →
      H₀ ≤ H → 1 ≤ Baux →
      0 < Dex → Dex ≤ H ^ Aex → m * primeProduct P ∣ Dex →
      m ≠ 0 →
      z₀ ∈ X →
      (∀ z ∈ X, allowed z ⊆ P) →
      (∀ z ∈ X, depth ≤ (allowed z).card) →
      (∀ z ∈ X, ∀ i,
        (progressionHomogeneousPoint u m z i).natAbs ≤ H) →
      (∀ z ∈ X, ∀ i, (z i).natAbs ≤ Baux) →
      (∀ z ∈ X,
        MvPolynomial.eval (progressionHomogeneousPoint u m z) F = 0) →
      (∀ z ∈ X, ∃ v, MvPolynomial.eval
        (fun i => u i + (m : ℤ) * z i)
        (MvPolynomial.pderiv v
          (surfaceHypersurfaceFirstChartDehomogenize F)) ≠ 0) →
      (∀ z ∈ X, ∀ p ∈ P, ∃ v,
        (MvPolynomial.eval (fun i => u i + (m : ℤ) * z i)
          (MvPolynomial.pderiv v
            (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0) →
      (∀ z ∈ X,
        (fun i => (progressionHomogeneousPoint u m z i : ℚ)) ∈
          finiteAffineCommonZeroLocus sourceEquations) →
      1 ≤ Bpoint →
      (∀ z ∈ X, ∀ i,
        |(integralAffineMap u z m i : ℝ)| ≤ (Bpoint : ℝ)) →
      ∃ blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ,
        ∃ auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
          (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
            MvPolynomial (Fin 4) ℚ,
        (∀ v : PrimeSubsetPrefix.Vertex P depth,
          0 < blockDegree v ∧
          ((blockDegree v : ℕ) : ℝ) ≤ 2 * (H : ℝ) ^ η *
            (1 + (Baux : ℝ) ^ a /
              (PrimeSubsetPrefix.modulus v : ℝ)) ∧
          (∀ ρ ∈ occupiedIntegralResidues
              (PrimeSubsetPrefix.modulus v) X,
            (auxiliary v ρ).IsHomogeneous (b + blockDegree v) ∧
              auxiliary v ρ ∉ finiteEquationIdeal sourceEquations) ∧
          ∀ z ∈ X, MvPolynomial.eval
            (fun i => (progressionHomogeneousPoint u m z i : ℚ))
              (auxiliary v (integralResidueVector z)) = 0) ∧
        (let root := PrimeSubsetPrefix.root P depth
         let G₀ := auxiliary root (integralResidueVector z₀)
         let cell := quantitativePrefixPersistentCell sourceEquations auxiliary
           u m X allowed
         let active := activeQbarPersistentRootComponentOptions
           sourceEquations G₀ cell
         ∃ (representative : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
              IntVector 3)
            (terminalVertex : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
              PrimeSubsetPrefix.Vertex P depth)
            (terminalDegree : Option (Ideal (MvPolynomial (Fin 4) Qbar)) → ℕ)
            (terminalCut : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
              MvPolynomial (Fin 4) ℚ),
            (∀ o ∈ active, representative o ∈ cell o) ∧
            (∀ o ∈ active,
              terminalVertex o ∈ PrimeSubsetPrefix.survivingVertices P
                (allowed (representative o)) depth ∧
              (terminalVertex o).1.card = depth) ∧
            (∀ o,
              terminalDegree o = b + blockDegree (terminalVertex o) ∧
              terminalCut o = auxiliary (terminalVertex o)
                (integralResidueVector (representative o))) ∧
            active.card ≤ d * (b + blockDegree root) ∧
            (X.card : ℝ) ≤
              (((PrimeSubsetPrefix.directedEdges P depth).card *
                quantitativePrefixEdgeMajorant
                  F P depth d b H Baux η a : ℕ) : ℝ) +
              ((quantitativePrefixPersistentRationalLinearPointUnion
                (finiteEquationIdeal sourceEquations) active terminalCut
                  u m cell).card : ℝ) +
              quantitativePrefixEffectiveCurveResidual
                Ccurve d b H Baux Bpoint η a) := by
  obtain ⟨Dsurface, hDsurface, hsurface⟩ :=
    exists_fixed_integral_surface_prime_count_of_multiple
      integralityOpen curveWeil hd F hF0 hF hgeom Kred hKred
  obtain ⟨b, D, A, H₀, Cdet, Ccurve,
      hD, hA, hH₀, hCdet, hCcurve, hendpoint⟩ :=
    exists_fixedSurface_quantitativePrefixSurfaceCount_effective_globalEdgeBound
      hCurve (by omega) sourceEquations hprime hgeometricPrime hhom hchart
        hdegree F Kred hKred.le Aex η a hη ha
  refine ⟨Dsurface, b, D, A, H₀, Cdet, Ccurve,
    hDsurface, hD, hA, hH₀, hCdet, hCcurve, ?_⟩
  intro P depth H Baux Bpoint m Dex u X allowed z₀ hDsurfaceDex hP hPm
    hH hBaux hDex hDexHeight hmPDex hm hz₀ hallowed hroom hheight
    hboxAux hzero hgradient hsmooth hsource hBpoint hboxPoint
  exact hendpoint P depth H Baux Bpoint m Dex u X allowed z₀ hP hPm hH
    hBaux hDex hDexHeight hmPDex hm hz₀ hallowed hroom
    (hsurface Dex hDsurfaceDex) hheight hboxAux hzero hgradient hsmooth
    hsource hBpoint hboxPoint

end TranslatedDepthSeven
