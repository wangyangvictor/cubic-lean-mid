import TranslatedDepthSeven.SurfaceNormalizationResidueDisc
import TranslatedDepthSeven.LocalizedCompleteIntersectionStandardSmooth
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# A literal nonsingular hypersurface residue disc

The hypersurface is given by an integral polynomial in three variables.  We
use the last two coordinates as the base parameters and invert the first
partial derivative.  The presentation keeps all three ambient variables,
with two additional equations identifying the parameters with coordinates.
This avoids any implicit change of the displayed hypersurface or its points.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial

abbrev SurfaceHypersurfacePolynomial := MvPolynomial (Fin 3) ℤ
abbrev SurfaceHypersurfacePresentationPolynomial :=
  MvPolynomial (Fin 3) BivariateIntPolynomial

/-- The hypersurface equation, and the two equations identifying the base
parameters with the last two ambient coordinates. -/
def surfaceHypersurfaceEquations (F : SurfaceHypersurfacePolynomial) :
    Fin 3 → SurfaceHypersurfacePresentationPolynomial :=
  ![MvPolynomial.map MvPolynomial.C F,
    MvPolynomial.X 1 - MvPolynomial.C (MvPolynomial.X 0),
    MvPolynomial.X 2 - MvPolynomial.C (MvPolynomial.X 1)]

abbrev SurfaceHypersurfaceQuotient (F : SurfaceHypersurfacePolynomial) :=
  EquationQuotient (surfaceHypersurfaceEquations F)

def surfaceHypersurfaceJacobian (F : SurfaceHypersurfacePolynomial) :
    SurfaceHypersurfaceQuotient F :=
  (equationPreSubmersivePresentation (surfaceHypersurfaceEquations F)
    id Function.injective_id).jacobian

abbrev SurfaceHypersurfaceChart (F : SurfaceHypersurfacePolynomial) :=
  Localization.Away (surfaceHypersurfaceJacobian F)

theorem surfaceHypersurfaceJacobian_eq (F : SurfaceHypersurfacePolynomial) :
    surfaceHypersurfaceJacobian F =
      Ideal.Quotient.mk (Ideal.span (Set.range (surfaceHypersurfaceEquations F)))
        (MvPolynomial.map MvPolynomial.C (MvPolynomial.pderiv 0 F)) := by
  classical
  unfold surfaceHypersurfaceJacobian
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
  congr 1
  simp [equationPreSubmersivePresentation,
    Algebra.PreSubmersivePresentation.jacobiMatrix_naive,
    Matrix.det_fin_three, surfaceHypersurfaceEquations, MvPolynomial.pderiv_map]

instance surfaceHypersurfaceChart_formallyEtale (F : SurfaceHypersurfacePolynomial) :
    Algebra.FormallyEtale BivariateIntPolynomial (SurfaceHypersurfaceChart F) := by
  letI : IsLocalization.Away
      (1 * (equationPreSubmersivePresentation (surfaceHypersurfaceEquations F)
        id Function.injective_id).jacobian) (SurfaceHypersurfaceChart F) := by
    simpa only [one_mul] using (inferInstance :
      IsLocalization.Away (surfaceHypersurfaceJacobian F) (SurfaceHypersurfaceChart F))
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 0
      BivariateIntPolynomial (SurfaceHypersurfaceChart F) := by
    simpa using finEquationQuotient_localizedAt_mul_jacobian_isStandardSmoothOfRelativeDimension
      (surfaceHypersurfaceEquations F) id Function.injective_id 1
      (SurfaceHypersurfaceChart F)
  infer_instance

/-- A nilpotent-kernel reduction reflects units. -/
theorem isUnit_of_surjective_nilpotent_kernel {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hsurj : Function.Surjective f)
    (hker : IsNilpotent (RingHom.ker f)) {x : R} (hx : IsUnit (f x)) :
    IsUnit x := by
  apply hker.isUnit_quotient_mk_iff.mp
  have h := hx.map (f.quotientKerEquivOfSurjective hsurj).symm.toRingHom
  simpa only [RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, ← RingHom.quotientKerEquivOfSurjective_apply_mk hsurj,
    RingEquiv.symm_apply_apply] using h

/-- Evaluation of the presentation with parameters equal to the last two
coordinates of the displayed point. -/
def surfaceHypersurfaceModEval (n : ℕ) (y : Fin 3 → ℤ) :
    SurfaceHypersurfacePresentationPolynomial →+* ZMod n :=
  MvPolynomial.eval₂Hom
    (evalBivariateIntPolynomialZMod n (fun i => y i.succ))
    (fun i => (y i : ZMod n))

theorem surfaceHypersurfaceModEval_map (n : ℕ) (y : Fin 3 → ℤ)
    (F : SurfaceHypersurfacePolynomial) :
    surfaceHypersurfaceModEval n y (MvPolynomial.map MvPolynomial.C F) =
      (MvPolynomial.eval y F : ℤ) := by
  have h : (surfaceHypersurfaceModEval n y).comp (MvPolynomial.map MvPolynomial.C) =
      (Int.castRingHom (ZMod n)).comp (MvPolynomial.eval y) := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [surfaceHypersurfaceModEval, evalBivariateIntPolynomialZMod]
    · intro i
      simp [surfaceHypersurfaceModEval]
  exact RingHom.congr_fun h F

theorem surfaceHypersurfaceModEval_equations (n : ℕ) (y : Fin 3 → ℤ)
    (F : SurfaceHypersurfacePolynomial)
    (hF : (MvPolynomial.eval y F : ZMod n) = 0) (i : Fin 3) :
    surfaceHypersurfaceModEval n y (surfaceHypersurfaceEquations F i) = 0 := by
  fin_cases i
  · simpa [surfaceHypersurfaceEquations, surfaceHypersurfaceModEval_map] using hF
  · simp [surfaceHypersurfaceEquations, surfaceHypersurfaceModEval,
      evalBivariateIntPolynomialZMod]
  · simp [surfaceHypersurfaceEquations, surfaceHypersurfaceModEval,
      evalBivariateIntPolynomialZMod]

/-- The equation vanishing gives the actual map out of its coordinate ring. -/
def surfaceHypersurfaceQuotientEval (n : ℕ) (y : Fin 3 → ℤ)
    (F : SurfaceHypersurfacePolynomial)
    (hF : (MvPolynomial.eval y F : ZMod n) = 0) :
    SurfaceHypersurfaceQuotient F →+* ZMod n :=
  Ideal.Quotient.lift _ (surfaceHypersurfaceModEval n y) (by
    have hle : Ideal.span (Set.range (surfaceHypersurfaceEquations F)) ≤
        RingHom.ker (surfaceHypersurfaceModEval n y) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact surfaceHypersurfaceModEval_equations n y F hF i
    intro a ha
    exact hle ha)

@[simp] theorem surfaceHypersurfaceQuotientEval_mk (n : ℕ) (y : Fin 3 → ℤ)
    (F : SurfaceHypersurfacePolynomial)
    (hF : (MvPolynomial.eval y F : ZMod n) = 0)
    (G : SurfaceHypersurfacePresentationPolynomial) :
    surfaceHypersurfaceQuotientEval n y F hF
      (Ideal.Quotient.mk _ G) = surfaceHypersurfaceModEval n y G := rfl

@[simp] theorem surfaceHypersurfaceQuotientEval_jacobian (n : ℕ) (y : Fin 3 → ℤ)
    (F : SurfaceHypersurfacePolynomial)
    (hF : (MvPolynomial.eval y F : ZMod n) = 0) :
    surfaceHypersurfaceQuotientEval n y F hF (surfaceHypersurfaceJacobian F) =
      (MvPolynomial.eval y (MvPolynomial.pderiv 0 F) : ℤ) := by
  rw [surfaceHypersurfaceJacobian_eq, surfaceHypersurfaceQuotientEval_mk,
    surfaceHypersurfaceModEval_map]

/-- The derivative being a unit gives the actual map on the principal open. -/
def surfaceHypersurfaceChartEval (n : ℕ) (y : Fin 3 → ℤ)
    (F : SurfaceHypersurfacePolynomial)
    (hF : (MvPolynomial.eval y F : ZMod n) = 0)
    (hJ : IsUnit (MvPolynomial.eval y (MvPolynomial.pderiv 0 F) : ZMod n)) :
    SurfaceHypersurfaceChart F →+* ZMod n :=
  IsLocalization.Away.lift (surfaceHypersurfaceJacobian F)
    (g := surfaceHypersurfaceQuotientEval n y F hF) (by simpa using hJ)

@[simp] theorem surfaceHypersurfaceChartEval_algebraMap (n : ℕ) (y : Fin 3 → ℤ)
    (F : SurfaceHypersurfacePolynomial)
    (hF : (MvPolynomial.eval y F : ZMod n) = 0)
    (hJ : IsUnit (MvPolynomial.eval y (MvPolynomial.pderiv 0 F) : ZMod n))
    (a : SurfaceHypersurfaceQuotient F) :
    surfaceHypersurfaceChartEval n y F hF hJ
      (algebraMap (SurfaceHypersurfaceQuotient F) (SurfaceHypersurfaceChart F) a) =
        surfaceHypersurfaceQuotientEval n y F hF a :=
  IsLocalization.Away.lift_eq _ _ _

/-- The literal ambient polynomial map into the hypersurface principal open. -/
def surfaceHypersurfaceAmbient (F : SurfaceHypersurfacePolynomial) :
    SurfaceHypersurfacePolynomial →+* SurfaceHypersurfaceChart F :=
  (algebraMap (SurfaceHypersurfaceQuotient F) (SurfaceHypersurfaceChart F)).comp
    ((Ideal.Quotient.mk _).comp (MvPolynomial.map MvPolynomial.C))

theorem surfaceHypersurfaceChartEval_base (n : ℕ) (y : Fin 3 → ℤ)
    (F : SurfaceHypersurfacePolynomial)
    (hF : (MvPolynomial.eval y F : ZMod n) = 0)
    (hJ : IsUnit (MvPolynomial.eval y (MvPolynomial.pderiv 0 F) : ZMod n)) :
    (surfaceHypersurfaceChartEval n y F hF hJ).comp
      (algebraMap BivariateIntPolynomial (SurfaceHypersurfaceChart F)) =
        evalBivariateIntPolynomialZMod n (fun i => y i.succ) := by
  apply RingHom.ext
  intro a
  rw [RingHom.comp_apply,
    IsScalarTower.algebraMap_apply BivariateIntPolynomial
      (SurfaceHypersurfaceQuotient F) (SurfaceHypersurfaceChart F),
    surfaceHypersurfaceChartEval_algebraMap]
  change surfaceHypersurfaceQuotientEval n y F hF (Ideal.Quotient.mk _ (C a)) = _
  simp [surfaceHypersurfaceModEval]

theorem surfaceHypersurfaceChartEval_ambient (n : ℕ) (y : Fin 3 → ℤ)
    (F : SurfaceHypersurfacePolynomial)
    (hF : (MvPolynomial.eval y F : ZMod n) = 0)
    (hJ : IsUnit (MvPolynomial.eval y (MvPolynomial.pderiv 0 F) : ZMod n)) :
    (surfaceHypersurfaceChartEval n y F hF hJ).comp
      (surfaceHypersurfaceAmbient F) =
        MvPolynomial.eval₂Hom (Int.castRingHom (ZMod n)) (fun i => (y i : ZMod n)) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [surfaceHypersurfaceAmbient]
  · intro i
    simp [surfaceHypersurfaceAmbient, surfaceHypersurfaceModEval]

/-- Congruent integer points give equal polynomial values modulo the modulus. -/
theorem surfaceHypersurface_eval_mod_congruent {σ : Type*} (n : ℕ)
    (y z : σ → ℤ) (hyz : ∀ i, (n : ℤ) ∣ y i - z i)
    (G : MvPolynomial σ ℤ) :
    (MvPolynomial.eval y G : ZMod n) = (MvPolynomial.eval z G : ZMod n) := by
  have h : (Int.castRingHom (ZMod n)).comp (MvPolynomial.eval y) =
      (Int.castRingHom (ZMod n)).comp (MvPolynomial.eval z) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.eval_X]
      change (y i : ZMod n) = (z i : ZMod n)
      rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hyz i
  exact RingHom.congr_fun h G

/-- A first partial which is nonzero at the common residue point is invertible
at every positive prime-power specialization of that residue class. -/
theorem surfaceHypersurface_partial_isUnit (p E : ℕ) (hp : p.Prime) (hE : 0 < E)
    (F : SurfaceHypersurfacePolynomial) (y z : Fin 3 → ℤ)
    (hyz : ∀ i, (p : ℤ) ∣ y i - z i)
    (hJ : (MvPolynomial.eval z (MvPolynomial.pderiv 0 F) : ZMod p) ≠ 0) :
    IsUnit (MvPolynomial.eval y (MvPolynomial.pderiv 0 F) : ZMod (p ^ E)) := by
  letI : Fact p.Prime := ⟨hp⟩
  apply isUnit_of_surjective_nilpotent_kernel (zmodPrimePowerReduction p E hE)
    (zmodPrimePowerReduction_surjective p E hE)
    (ker_zmodPrimePowerReduction_isNilpotent p E hE)
  rw [map_intCast, surfaceHypersurface_eval_mod_congruent p y z hyz]
  exact isUnit_iff_ne_zero.mpr hJ

theorem surfaceHypersurfaceChartEval_reduction (p E : ℕ) (hE : 0 < E)
    (F : SurfaceHypersurfacePolynomial) (y z : Fin 3 → ℤ)
    (hyz : ∀ i, (p : ℤ) ∣ y i - z i)
    (hyF : (MvPolynomial.eval y F : ZMod (p ^ E)) = 0)
    (hzF : (MvPolynomial.eval z F : ZMod p) = 0)
    (hyJ : IsUnit (MvPolynomial.eval y (MvPolynomial.pderiv 0 F) : ZMod (p ^ E)))
    (hzJ : IsUnit (MvPolynomial.eval z (MvPolynomial.pderiv 0 F) : ZMod p)) :
    (zmodPrimePowerReduction p E hE).comp
      (surfaceHypersurfaceChartEval (p ^ E) y F hyF hyJ) =
        surfaceHypersurfaceChartEval p z F hzF hzJ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (surfaceHypersurfaceJacobian F))
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, surfaceHypersurfaceChartEval_algebraMap,
      surfaceHypersurfaceQuotientEval_mk, surfaceHypersurfaceModEval,
      MvPolynomial.eval₂Hom_C]
    exact RingHom.congr_fun
      (zmodPrimePowerReduction_comp_evalBivariateIntPolynomialZMod p E hE
        (fun i => y i.succ) (fun i => z i.succ) (fun i => hyz i.succ)) a
  · intro i
    simp only [RingHom.comp_apply, surfaceHypersurfaceChartEval_algebraMap,
      surfaceHypersurfaceQuotientEval_mk, surfaceHypersurfaceModEval,
      MvPolynomial.eval₂Hom_X', map_intCast]
    rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hyz i

/-- Construct the entire formally etale residue-disc datum from a literal
integral hypersurface and a nonsingular common reduction of its integer points.
No chart, local determinant estimate, or formal-etaleness hypothesis is supplied. -/
def surfaceHypersurfaceResidueDisc {ι : Type*}
    (p E : ℕ) (hp : p.Prime) (hE : 0 < E)
    (F : SurfaceHypersurfacePolynomial) (y : ι → Fin 3 → ℤ) (z : Fin 3 → ℤ)
    (hyF : ∀ j, MvPolynomial.eval (y j) F = 0)
    (hzF : (MvPolynomial.eval z F : ZMod p) = 0)
    (hyz : ∀ j i, (p : ℤ) ∣ y j i - z i)
    (hzJ : (MvPolynomial.eval z (MvPolynomial.pderiv 0 F) : ZMod p) ≠ 0) :
    SurfaceNormalizationResidueDisc (Fin 3) ι p E hE y := by
  letI : Fact p.Prime := ⟨hp⟩
  have hunit : IsUnit (MvPolynomial.eval z (MvPolynomial.pderiv 0 F) : ZMod p) :=
    isUnit_iff_ne_zero.mpr hzJ
  have hzero (j : ι) : (MvPolynomial.eval (y j) F : ZMod (p ^ E)) = 0 := by
    rw [hyF j, Int.cast_zero]
  have hunitE (j : ι) :
      IsUnit (MvPolynomial.eval (y j) (MvPolynomial.pderiv 0 F) : ZMod (p ^ E)) :=
    surfaceHypersurface_partial_isUnit p E hp hE F (y j) z (hyz j) hzJ
  exact {
    Chart := SurfaceHypersurfaceChart F
    ambient := surfaceHypersurfaceAmbient F
    center := fun i => z i.succ
    parameters := fun j i => y j i.succ
    congruent := fun j i => hyz j i.succ
    point := surfaceHypersurfaceChartEval p z F hzF hunit
    point_base := surfaceHypersurfaceChartEval_base p z F hzF hunit
    specialization := fun j => surfaceHypersurfaceChartEval (p ^ E) (y j) F (hzero j) (hunitE j)
    specialization_base := fun j =>
      surfaceHypersurfaceChartEval_base (p ^ E) (y j) F (hzero j) (hunitE j)
    specialization_reduction := fun j =>
      surfaceHypersurfaceChartEval_reduction p E hE F (y j) z (hyz j)
        (hzero j) hzF (hunitE j) hunit
    specialization_ambient := fun j =>
      surfaceHypersurfaceChartEval_ambient (p ^ E) (y j) F (hzero j) (hunitE j) }

/-- For a nonempty family the residue equation itself follows from one of
the integer solutions, so it need not be a separate hypothesis. -/
def surfaceHypersurfaceResidueDiscOfNonempty {ι : Type*} [Nonempty ι]
    (p E : ℕ) (hp : p.Prime) (hE : 0 < E)
    (F : SurfaceHypersurfacePolynomial) (y : ι → Fin 3 → ℤ) (z : Fin 3 → ℤ)
    (hyF : ∀ j, MvPolynomial.eval (y j) F = 0)
    (hyz : ∀ j i, (p : ℤ) ∣ y j i - z i)
    (hzJ : (MvPolynomial.eval z (MvPolynomial.pderiv 0 F) : ZMod p) ≠ 0) :
    SurfaceNormalizationResidueDisc (Fin 3) ι p E hE y := by
  have hzF : (MvPolynomial.eval z F : ZMod p) = 0 := by
    obtain ⟨j⟩ := ‹Nonempty ι›
    rw [← surfaceHypersurface_eval_mod_congruent p (y j) z (hyz j) F,
      hyF j, Int.cast_zero]
  exact surfaceHypersurfaceResidueDisc p E hp hE F y z hyF hzF hyz hzJ

/-- The concrete hypersurface assumptions now imply the surface determinant
divisibility already proved for actual formally etale residue discs. -/
theorem surfaceHypersurfaceIntegerEvaluations_det_dvd
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (t s : ℕ) (hcard : Fintype.card ι = affinePlaneMonomialCount t + s)
    (hE : 0 < affinePlaneMonomialWeight t + (t + 1) * s)
    (p : ℕ) (hp : p.Prime)
    (F : SurfaceHypersurfacePolynomial) (y : ι → Fin 3 → ℤ) (z : Fin 3 → ℤ)
    (hyF : ∀ j, MvPolynomial.eval (y j) F = 0)
    (hyz : ∀ j i, (p : ℤ) ∣ y j i - z i)
    (hzJ : (MvPolynomial.eval z (MvPolynomial.pderiv 0 F) : ZMod p) ≠ 0)
    (G : ι → SurfaceHypersurfacePolynomial) :
    (p : ℤ) ^ (affinePlaneMonomialWeight t + (t + 1) * s) ∣
      (Matrix.of (fun i j => MvPolynomial.eval (y j) (G i))).det := by
  exact (surfaceHypersurfaceResidueDiscOfNonempty p
    (affinePlaneMonomialWeight t + (t + 1) * s) hp hE F y z hyF hyz hzJ).det_dvd
      t s hcard hE p y G

end
end TranslatedDepthSeven
