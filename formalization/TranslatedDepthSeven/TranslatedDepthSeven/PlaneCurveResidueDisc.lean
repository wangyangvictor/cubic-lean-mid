import TranslatedDepthSeven.CurveNormalizationResidueDisc
import TranslatedDepthSeven.LocalizedCompleteIntersectionStandardSmooth
import TranslatedDepthSeven.HypersurfaceSurfaceResidueDisc
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# A literal nonsingular plane-curve residue disc

For an integral polynomial in two variables, this file constructs the actual
formally-etale one-parameter chart obtained by using the second coordinate as
parameter and inverting the first partial derivative.  Thus the local curve
determinant applies to a nonsingular residue class without a separate chart
hypothesis.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial

abbrev PlaneCurvePolynomial := MvPolynomial (Fin 2) ℤ
abbrev PlaneCurvePresentationPolynomial :=
  MvPolynomial (Fin 2) UnivariateIntPolynomial

/-- The plane-curve equation together with the equation identifying the base
parameter with the second ambient coordinate. -/
def planeCurveEquations (F : PlaneCurvePolynomial) :
    Fin 2 → PlaneCurvePresentationPolynomial :=
  ![MvPolynomial.map MvPolynomial.C F,
    MvPolynomial.X 1 - MvPolynomial.C (MvPolynomial.X 0)]

abbrev PlaneCurveQuotient (F : PlaneCurvePolynomial) :=
  EquationQuotient (planeCurveEquations F)

def planeCurveJacobian (F : PlaneCurvePolynomial) : PlaneCurveQuotient F :=
  (equationPreSubmersivePresentation (planeCurveEquations F)
    id Function.injective_id).jacobian

abbrev PlaneCurveChart (F : PlaneCurvePolynomial) :=
  Localization.Away (planeCurveJacobian F)

theorem planeCurveJacobian_eq (F : PlaneCurvePolynomial) :
    planeCurveJacobian F =
      Ideal.Quotient.mk (Ideal.span (Set.range (planeCurveEquations F)))
        (MvPolynomial.map MvPolynomial.C (MvPolynomial.pderiv 0 F)) := by
  classical
  unfold planeCurveJacobian
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
  congr 1
  simp [equationPreSubmersivePresentation,
    Algebra.PreSubmersivePresentation.jacobiMatrix_naive,
    Matrix.det_fin_two, planeCurveEquations, MvPolynomial.pderiv_map]

instance planeCurveChart_formallyEtale (F : PlaneCurvePolynomial) :
    Algebra.FormallyEtale UnivariateIntPolynomial (PlaneCurveChart F) := by
  letI : IsLocalization.Away
      (1 * (equationPreSubmersivePresentation (planeCurveEquations F)
        id Function.injective_id).jacobian) (PlaneCurveChart F) := by
    simpa only [one_mul] using (inferInstance :
      IsLocalization.Away (planeCurveJacobian F) (PlaneCurveChart F))
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 0
      UnivariateIntPolynomial (PlaneCurveChart F) := by
    simpa using finEquationQuotient_localizedAt_mul_jacobian_isStandardSmoothOfRelativeDimension
      (planeCurveEquations F) id Function.injective_id 1 (PlaneCurveChart F)
  infer_instance

/-- Evaluation with the one base parameter equal to the second coordinate of
the displayed point. -/
def planeCurveModEval (n : ℕ) (y : Fin 2 → ℤ) :
    PlaneCurvePresentationPolynomial →+* ZMod n :=
  MvPolynomial.eval₂Hom
    (evalUnivariateIntPolynomialZMod n (fun _ ↦ y 1))
    (fun i ↦ (y i : ZMod n))

theorem planeCurveModEval_map (n : ℕ) (y : Fin 2 → ℤ)
    (F : PlaneCurvePolynomial) :
    planeCurveModEval n y (MvPolynomial.map MvPolynomial.C F) =
      (MvPolynomial.eval y F : ℤ) := by
  have h : (planeCurveModEval n y).comp (MvPolynomial.map MvPolynomial.C) =
      (Int.castRingHom (ZMod n)).comp (MvPolynomial.eval y) := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [planeCurveModEval, evalUnivariateIntPolynomialZMod]
    · intro i
      simp [planeCurveModEval]
  exact RingHom.congr_fun h F

theorem planeCurveModEval_equations (n : ℕ) (y : Fin 2 → ℤ)
    (F : PlaneCurvePolynomial)
    (hF : (MvPolynomial.eval y F : ZMod n) = 0) (i : Fin 2) :
    planeCurveModEval n y (planeCurveEquations F i) = 0 := by
  fin_cases i
  · simpa [planeCurveEquations, planeCurveModEval_map] using hF
  · simp [planeCurveEquations, planeCurveModEval,
      evalUnivariateIntPolynomialZMod]

def planeCurveQuotientEval (n : ℕ) (y : Fin 2 → ℤ)
    (F : PlaneCurvePolynomial)
    (hF : (MvPolynomial.eval y F : ZMod n) = 0) :
    PlaneCurveQuotient F →+* ZMod n :=
  Ideal.Quotient.lift _ (planeCurveModEval n y) (by
    have hle : Ideal.span (Set.range (planeCurveEquations F)) ≤
        RingHom.ker (planeCurveModEval n y) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact planeCurveModEval_equations n y F hF i
    intro a ha
    exact hle ha)

@[simp] theorem planeCurveQuotientEval_mk (n : ℕ) (y : Fin 2 → ℤ)
    (F : PlaneCurvePolynomial)
    (hF : (MvPolynomial.eval y F : ZMod n) = 0)
    (G : PlaneCurvePresentationPolynomial) :
    planeCurveQuotientEval n y F hF (Ideal.Quotient.mk _ G) =
      planeCurveModEval n y G := rfl

@[simp] theorem planeCurveQuotientEval_jacobian (n : ℕ) (y : Fin 2 → ℤ)
    (F : PlaneCurvePolynomial)
    (hF : (MvPolynomial.eval y F : ZMod n) = 0) :
    planeCurveQuotientEval n y F hF (planeCurveJacobian F) =
      (MvPolynomial.eval y (MvPolynomial.pderiv 0 F) : ℤ) := by
  rw [planeCurveJacobian_eq, planeCurveQuotientEval_mk, planeCurveModEval_map]

def planeCurveChartEval (n : ℕ) (y : Fin 2 → ℤ)
    (F : PlaneCurvePolynomial)
    (hF : (MvPolynomial.eval y F : ZMod n) = 0)
    (hJ : IsUnit (MvPolynomial.eval y (MvPolynomial.pderiv 0 F) : ZMod n)) :
    PlaneCurveChart F →+* ZMod n :=
  IsLocalization.Away.lift (planeCurveJacobian F)
    (g := planeCurveQuotientEval n y F hF) (by simpa using hJ)

@[simp] theorem planeCurveChartEval_algebraMap (n : ℕ) (y : Fin 2 → ℤ)
    (F : PlaneCurvePolynomial)
    (hF : (MvPolynomial.eval y F : ZMod n) = 0)
    (hJ : IsUnit (MvPolynomial.eval y (MvPolynomial.pderiv 0 F) : ZMod n))
    (a : PlaneCurveQuotient F) :
    planeCurveChartEval n y F hF hJ
      (algebraMap (PlaneCurveQuotient F) (PlaneCurveChart F) a) =
        planeCurveQuotientEval n y F hF a :=
  IsLocalization.Away.lift_eq _ _ _

def planeCurveAmbient (F : PlaneCurvePolynomial) :
    PlaneCurvePolynomial →+* PlaneCurveChart F :=
  (algebraMap (PlaneCurveQuotient F) (PlaneCurveChart F)).comp
    ((Ideal.Quotient.mk _).comp (MvPolynomial.map MvPolynomial.C))

theorem planeCurveChartEval_base (n : ℕ) (y : Fin 2 → ℤ)
    (F : PlaneCurvePolynomial)
    (hF : (MvPolynomial.eval y F : ZMod n) = 0)
    (hJ : IsUnit (MvPolynomial.eval y (MvPolynomial.pderiv 0 F) : ZMod n)) :
    (planeCurveChartEval n y F hF hJ).comp
      (algebraMap UnivariateIntPolynomial (PlaneCurveChart F)) =
        evalUnivariateIntPolynomialZMod n (fun _ ↦ y 1) := by
  apply RingHom.ext
  intro a
  rw [RingHom.comp_apply,
    IsScalarTower.algebraMap_apply UnivariateIntPolynomial
      (PlaneCurveQuotient F) (PlaneCurveChart F),
    planeCurveChartEval_algebraMap]
  change planeCurveQuotientEval n y F hF (Ideal.Quotient.mk _ (C a)) = _
  simp [planeCurveModEval]

theorem planeCurveChartEval_ambient (n : ℕ) (y : Fin 2 → ℤ)
    (F : PlaneCurvePolynomial)
    (hF : (MvPolynomial.eval y F : ZMod n) = 0)
    (hJ : IsUnit (MvPolynomial.eval y (MvPolynomial.pderiv 0 F) : ZMod n)) :
    (planeCurveChartEval n y F hF hJ).comp (planeCurveAmbient F) =
      MvPolynomial.eval₂Hom (Int.castRingHom (ZMod n))
        (fun i ↦ (y i : ZMod n)) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [planeCurveAmbient]
  · intro i
    simp [planeCurveAmbient, planeCurveModEval]

theorem planeCurve_partial_isUnit (p E : ℕ) (hp : p.Prime) (hE : 0 < E)
    (F : PlaneCurvePolynomial) (y z : Fin 2 → ℤ)
    (hyz : ∀ i, (p : ℤ) ∣ y i - z i)
    (hJ : (MvPolynomial.eval z (MvPolynomial.pderiv 0 F) : ZMod p) ≠ 0) :
    IsUnit (MvPolynomial.eval y (MvPolynomial.pderiv 0 F) : ZMod (p ^ E)) := by
  letI : Fact p.Prime := ⟨hp⟩
  apply isUnit_of_surjective_nilpotent_kernel (zmodPrimePowerReduction p E hE)
    (zmodPrimePowerReduction_surjective p E hE)
    (ker_zmodPrimePowerReduction_isNilpotent p E hE)
  rw [map_intCast, surfaceHypersurface_eval_mod_congruent p y z hyz]
  exact isUnit_iff_ne_zero.mpr hJ

theorem planeCurveChartEval_reduction (p E : ℕ) (hE : 0 < E)
    (F : PlaneCurvePolynomial) (y z : Fin 2 → ℤ)
    (hyz : ∀ i, (p : ℤ) ∣ y i - z i)
    (hyF : (MvPolynomial.eval y F : ZMod (p ^ E)) = 0)
    (hzF : (MvPolynomial.eval z F : ZMod p) = 0)
    (hyJ : IsUnit (MvPolynomial.eval y (MvPolynomial.pderiv 0 F) : ZMod (p ^ E)))
    (hzJ : IsUnit (MvPolynomial.eval z (MvPolynomial.pderiv 0 F) : ZMod p)) :
    (zmodPrimePowerReduction p E hE).comp
      (planeCurveChartEval (p ^ E) y F hyF hyJ) =
        planeCurveChartEval p z F hzF hzJ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (planeCurveJacobian F))
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, planeCurveChartEval_algebraMap,
      planeCurveQuotientEval_mk, planeCurveModEval,
      MvPolynomial.eval₂Hom_C]
    exact RingHom.congr_fun
      (zmodPrimePowerReduction_comp_evalUnivariateIntPolynomialZMod p E hE
        (fun _ ↦ y 1) (fun _ ↦ z 1) (fun _ ↦ hyz 1)) a
  · intro i
    simp only [RingHom.comp_apply, planeCurveChartEval_algebraMap,
      planeCurveQuotientEval_mk, planeCurveModEval,
      MvPolynomial.eval₂Hom_X', map_intCast]
    rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hyz i

/-- Construct the entire formally-etale curve residue disc from a literal
integral plane curve and one nonzero partial at the common residue point. -/
def planeCurveResidueDisc {ι : Type*}
    (p E : ℕ) (hp : p.Prime) (hE : 0 < E)
    (F : PlaneCurvePolynomial) (y : ι → Fin 2 → ℤ) (z : Fin 2 → ℤ)
    (hyF : ∀ j, MvPolynomial.eval (y j) F = 0)
    (hzF : (MvPolynomial.eval z F : ZMod p) = 0)
    (hyz : ∀ j i, (p : ℤ) ∣ y j i - z i)
    (hzJ : (MvPolynomial.eval z (MvPolynomial.pderiv 0 F) : ZMod p) ≠ 0) :
    CurveNormalizationResidueDisc (Fin 2) ι p E hE y := by
  letI : Fact p.Prime := ⟨hp⟩
  have hunit : IsUnit (MvPolynomial.eval z (MvPolynomial.pderiv 0 F) : ZMod p) :=
    isUnit_iff_ne_zero.mpr hzJ
  have hzero (j : ι) : (MvPolynomial.eval (y j) F : ZMod (p ^ E)) = 0 := by
    rw [hyF j, Int.cast_zero]
  have hunitE (j : ι) :
      IsUnit (MvPolynomial.eval (y j) (MvPolynomial.pderiv 0 F) : ZMod (p ^ E)) :=
    planeCurve_partial_isUnit p E hp hE F (y j) z (hyz j) hzJ
  exact {
    Chart := PlaneCurveChart F
    ambient := planeCurveAmbient F
    center := fun _ ↦ z 1
    parameters := fun j _ ↦ y j 1
    congruent := fun j _ ↦ hyz j 1
    point := planeCurveChartEval p z F hzF hunit
    point_base := planeCurveChartEval_base p z F hzF hunit
    specialization := fun j ↦
      planeCurveChartEval (p ^ E) (y j) F (hzero j) (hunitE j)
    specialization_base := fun j ↦
      planeCurveChartEval_base (p ^ E) (y j) F (hzero j) (hunitE j)
    specialization_reduction := fun j ↦
      planeCurveChartEval_reduction p E hE F (y j) z (hyz j)
        (hzero j) hzF (hunitE j) hunit
    specialization_ambient := fun j ↦
      planeCurveChartEval_ambient (p ^ E) (y j) F (hzero j) (hunitE j) }

def planeCurveResidueDiscOfNonempty {ι : Type*} [Nonempty ι]
    (p E : ℕ) (hp : p.Prime) (hE : 0 < E)
    (F : PlaneCurvePolynomial) (y : ι → Fin 2 → ℤ) (z : Fin 2 → ℤ)
    (hyF : ∀ j, MvPolynomial.eval (y j) F = 0)
    (hyz : ∀ j i, (p : ℤ) ∣ y j i - z i)
    (hzJ : (MvPolynomial.eval z (MvPolynomial.pderiv 0 F) : ZMod p) ≠ 0) :
    CurveNormalizationResidueDisc (Fin 2) ι p E hE y := by
  have hzF : (MvPolynomial.eval z F : ZMod p) = 0 := by
    obtain ⟨j⟩ := ‹Nonempty ι›
    rw [← surfaceHypersurface_eval_mod_congruent p (y j) z (hyz j) F,
      hyF j, Int.cast_zero]
  exact planeCurveResidueDisc p E hp hE F y z hyF hzF hyz hzJ

/-- Relabel the two affine coordinates of an actual curve residue disc. -/
def planeCurveResidueDiscUnpermute {ι : Type*} {p E : ℕ} {hE : 0 < E}
    {y : ι → Fin 2 → ℤ} (e : Fin 2 ≃ Fin 2)
    (d : CurveNormalizationResidueDisc (Fin 2) ι p E hE
      (fun j i ↦ y j (e i))) :
    CurveNormalizationResidueDisc (Fin 2) ι p E hE y where
  Chart := d.Chart
  ambient := d.ambient.comp (MvPolynomial.rename e.symm).toRingHom
  center := d.center
  parameters := d.parameters
  congruent := d.congruent
  point := d.point
  point_base := d.point_base
  specialization := d.specialization
  specialization_base := d.specialization_base
  specialization_reduction := d.specialization_reduction
  specialization_ambient j := by
    rw [← RingHom.comp_assoc, d.specialization_ambient]
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      simp

/-- Any nonzero affine partial supplies the actual one-parameter residue disc;
the other affine coordinate is used as parameter. -/
def planeCurveResidueDiscAt {ι : Type*} [Nonempty ι]
    (p E : ℕ) (hp : p.Prime) (hE : 0 < E)
    (F : PlaneCurvePolynomial) (y : ι → Fin 2 → ℤ) (z : Fin 2 → ℤ)
    (hyF : ∀ j, MvPolynomial.eval (y j) F = 0)
    (hyz : ∀ j i, (p : ℤ) ∣ y j i - z i)
    (v : Fin 2)
    (hzJ : (MvPolynomial.eval z (MvPolynomial.pderiv v F) : ZMod p) ≠ 0) :
    CurveNormalizationResidueDisc (Fin 2) ι p E hE y := by
  let e : Fin 2 ≃ Fin 2 := Equiv.swap 0 v
  have heval (x : Fin 2 → ℤ) (G : PlaneCurvePolynomial) :
      MvPolynomial.eval (fun i ↦ x (e i)) (MvPolynomial.rename e.symm G) =
        MvPolynomial.eval x G := by
    rw [MvPolynomial.eval_rename]
    simp only [Function.comp_def, Equiv.apply_symm_apply]
  have hderiv : MvPolynomial.pderiv 0 (MvPolynomial.rename e.symm F) =
      MvPolynomial.rename e.symm (MvPolynomial.pderiv v F) := by
    simpa [e] using MvPolynomial.pderiv_rename e.symm.injective v F
  apply planeCurveResidueDiscUnpermute e
  apply planeCurveResidueDiscOfNonempty p E hp hE
    (MvPolynomial.rename e.symm F) (fun j i ↦ y j (e i)) (fun i ↦ z (e i))
  · intro j
    rw [heval, hyF]
  · intro j i
    exact hyz j (e i)
  · rw [hderiv, heval]
    exact hzJ

end
end TranslatedDepthSeven
