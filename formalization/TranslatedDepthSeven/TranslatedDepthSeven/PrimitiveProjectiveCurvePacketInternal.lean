import TranslatedDepthSeven.PlaneCurveModularResidueDisc
import TranslatedDepthSeven.Salberger2023PlaneCurveMonomialBlockInternal
import TranslatedDepthSeven.HomogeneousCone

/-! Local determinants for primitive projective points. Normalization is
performed modulo the determinant prime power, and homogeneous scaling
transfers vanishing back to the original integral evaluation matrix. -/
namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
open scoped BigOperators
set_option maxHeartbeats 2500000

/-- Lift the normalized affine coordinates modulo n to literal integers. -/
def projectiveModularFirstChart (n : ℕ) (x : Fin 3 → ℤ)
    (u : (ZMod n)ˣ) : Fin 2 → ℤ :=
  fun i ↦ ZMod.cast ((↑u⁻¹ : ZMod n) * (x i.succ : ZMod n))

 theorem projectiveModularFirstChart_scaling (n : ℕ) (x : Fin 3 → ℤ)
    (u : (ZMod n)ˣ) (hu : (u : ZMod n) = (x 0 : ZMod n)) :
    ∀ i, (x i : ZMod n) =
      (x 0 : ZMod n) * (planeCurveFirstChartPoint (projectiveModularFirstChart n x u) i : ZMod n) := by
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [planeCurveFirstChartPoint]
  · simp only [planeCurveFirstChartPoint, Fin.cases_succ, projectiveModularFirstChart,
      ZMod.intCast_zmod_cast, ← hu]
    simp [← mul_assoc]

 theorem eval_homogeneous_scaled_modular {n k : ℕ}
    (F : MvPolynomial (Fin 3) ℤ) (hF : F.IsHomogeneous k)
    (x : Fin 3 → ℤ) (y : Fin 2 → ℤ)
    (hxy : ∀ i, (x i : ZMod n) =
      (x 0 : ZMod n) * (planeCurveFirstChartPoint y i : ZMod n)) :
    (eval x F : ZMod n) = (x 0 : ZMod n) ^ k *
      (eval (planeCurveFirstChartPoint y) F : ZMod n) := by
  have hcast (z : Fin 3 → ℤ) :
      eval (fun i ↦ (z i : ZMod n)) (F.map (Int.castRingHom (ZMod n))) =
        (eval z F : ZMod n) := by
    rw [eval_map]
    exact (eval₂_comp (Int.castRingHom (ZMod n)) z F).symm
  rw [← hcast x, ← hcast (planeCurveFirstChartPoint y)]
  rw [show (fun i ↦ (x i : ZMod n)) =
      (fun i ↦ (x 0 : ZMod n) * (planeCurveFirstChartPoint y i : ZMod n))
      from funext hxy]
  exact eval_smul_of_isHomogeneous _ _ _ k (hF.map _)

/-- Smooth projective reduction gives the exact curve jet divisor for
homogeneous evaluations on the original, unnormalized integer vectors. -/
theorem projectivePlaneCurve_evaluation_det_dvd
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p d k : ℕ} (hp : p.Prime)
    (hE : 0 < affineLineJetWeight (Fintype.card ι))
    (P : MvPolynomial (Fin 3) ℤ) (hPhom : P.IsHomogeneous d)
    (x : ι → Fin 3 → ℤ) (hxP : ∀ j, eval (x j) P = 0)
    (hx0 : ∀ j, (x j 0 : ZMod p) ≠ 0)
    (center : Fin 2 → ℤ)
    (hcenter : (eval center (planeCurveFirstChartDehomogenize P) : ZMod p) = 0)
    (hcong : ∀ j i, (x j i.succ : ZMod p) =
      (x j 0 : ZMod p) * (center i : ZMod p))
    (v : Fin 2)
    (hpartial : (eval center (pderiv v (planeCurveFirstChartDehomogenize P)) : ZMod p) ≠ 0)
    (F : ι → MvPolynomial (Fin 3) ℤ) (hF : ∀ i, (F i).IsHomogeneous k) :
    (p : ℤ) ^ affineLineJetWeight (Fintype.card ι) ∣
      (Matrix.of (fun i j ↦ eval (x j) (F i))).det := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let E := affineLineJetWeight (Fintype.card ι)
  let red := zmodPrimePowerReduction p E hE
  have hxunit : ∀ j, IsUnit (x j 0 : ZMod (p ^ E)) := by
    intro j
    apply isUnit_of_surjective_nilpotent_kernel red
      (zmodPrimePowerReduction_surjective p E hE)
      (ker_zmodPrimePowerReduction_isNilpotent p E hE)
    simpa [red] using isUnit_iff_ne_zero.mpr (hx0 j)
  choose u hu using hxunit
  let y : ι → Fin 2 → ℤ := fun j ↦ projectiveModularFirstChart (p ^ E) (x j) (u j)
  have hscale (j : ι) (i : Fin 3) :
      (x j i : ZMod (p ^ E)) = (x j 0 : ZMod (p ^ E)) *
        (planeCurveFirstChartPoint (y j) i : ZMod (p ^ E)) :=
    projectiveModularFirstChart_scaling (p ^ E) (x j) (u j) (hu j) i
  have hyP (j : ι) : (eval (y j) (planeCurveFirstChartDehomogenize P) : ZMod (p ^ E)) = 0 := by
    rw [planeCurveFirstChart_eval]
    have hunit : IsUnit (x j 0 : ZMod (p ^ E)) := ⟨u j, hu j⟩
    apply (hunit.pow d).mul_right_eq_zero.mp
    rw [← eval_homogeneous_scaled_modular P hPhom (x j) (y j) (hscale j), hxP j]
    simp
  have hycong : ∀ j i, (p : ℤ) ∣ y j i - center i := by
    intro j i
    have hs := congrArg red (hscale j i.succ)
    simp only [map_intCast, map_mul, planeCurveFirstChartPoint, Fin.cases_succ] at hs
    have heq : (y j i : ZMod p) = (center i : ZMod p) := by
      exact mul_left_cancel₀ (hx0 j) (hs.symm.trans (hcong j i))
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, heq, sub_self]
  let disc := planeCurveResidueDiscFirstChart
    (planeCurveModularResidueDiscAt p E hp hE
      (planeCurveFirstChartDehomogenize P) y center hyP hcenter hycong v hpartial)
  have hnormdiv := CurveNormalizationResidueDisc.det_dvd hE p
    (fun j ↦ planeCurveFirstChartPoint (y j)) disc F
  have hnormzero :
      (Matrix.of (fun i j ↦ (eval (planeCurveFirstChartPoint (y j)) (F i) : ZMod (p ^ E)))).det = 0 := by
    change ((Int.castRingHom (ZMod (p ^ E))).mapMatrix
      (Matrix.of (fun i j ↦ eval (planeCurveFirstChartPoint (y j)) (F i)))).det = 0
    rw [← (Int.castRingHom (ZMod (p ^ E))).map_det]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by simpa [E] using hnormdiv)
  change ((p ^ E : ℕ) : ℤ) ∣ _
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  change (Int.castRingHom (ZMod (p ^ E)))
    (Matrix.of (fun i j ↦ eval (x j) (F i))).det = 0
  rw [(Int.castRingHom (ZMod (p ^ E))).map_det]
  have heq : (Int.castRingHom (ZMod (p ^ E))).mapMatrix
      (Matrix.of (fun i j ↦ eval (x j) (F i))) =
      Matrix.of (fun i j ↦ (x j 0 : ZMod (p ^ E)) ^ k *
        (eval (planeCurveFirstChartPoint (y j)) (F i) : ZMod (p ^ E))) := by
    ext i j
    exact eval_homogeneous_scaled_modular (F i) (hF i) (x j) (y j) (hscale j)
  rw [heq, Matrix.det_mul_row]
  exact mul_eq_zero_of_right _ hnormzero

end
end TranslatedDepthSeven
