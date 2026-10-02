import TranslatedDepthSeven.PlaneCurveResidueDiscFirstChart

/-! A curve residue disc only needs the equation modulo the determinant
prime power. This version also covers integer representatives of normalized
projective points, which need not satisfy the affine equation over Z. -/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial

/-- Actual modular curve points with a common smooth reduction define the
same formally etale residue disc as exact integral points. -/
def planeCurveModularResidueDisc {ι : Type*}
    (p E : ℕ) (hp : p.Prime) (hE : 0 < E)
    (F : PlaneCurvePolynomial) (y : ι → Fin 2 → ℤ) (z : Fin 2 → ℤ)
    (hyF : ∀ j, (eval (y j) F : ZMod (p ^ E)) = 0)
    (hzF : (eval z F : ZMod p) = 0)
    (hyz : ∀ j i, (p : ℤ) ∣ y j i - z i)
    (hzJ : (eval z (pderiv 0 F) : ZMod p) ≠ 0) :
    CurveNormalizationResidueDisc (Fin 2) ι p E hE y := by
  letI : Fact p.Prime := ⟨hp⟩
  have hunit : IsUnit (eval z (pderiv 0 F) : ZMod p) :=
    isUnit_iff_ne_zero.mpr hzJ
  have hunitE (j : ι) : IsUnit (eval (y j) (pderiv 0 F) : ZMod (p ^ E)) :=
    planeCurve_partial_isUnit p E hp hE F (y j) z (hyz j) hzJ
  exact {
    Chart := PlaneCurveChart F
    ambient := planeCurveAmbient F
    center := fun _ ↦ z 1
    parameters := fun j _ ↦ y j 1
    congruent := fun j _ ↦ hyz j 1
    point := planeCurveChartEval p z F hzF hunit
    point_base := planeCurveChartEval_base p z F hzF hunit
    specialization := fun j ↦ planeCurveChartEval (p ^ E) (y j) F (hyF j) (hunitE j)
    specialization_base := fun j ↦
      planeCurveChartEval_base (p ^ E) (y j) F (hyF j) (hunitE j)
    specialization_reduction := fun j ↦
      planeCurveChartEval_reduction p E hE F (y j) z (hyz j)
        (hyF j) hzF (hunitE j) hunit
    specialization_ambient := fun j ↦
      planeCurveChartEval_ambient (p ^ E) (y j) F (hyF j) (hunitE j) }

/-- Any nonzero affine partial suffices in the modular version. -/
def planeCurveModularResidueDiscAt {ι : Type*}
    (p E : ℕ) (hp : p.Prime) (hE : 0 < E)
    (F : PlaneCurvePolynomial) (y : ι → Fin 2 → ℤ) (z : Fin 2 → ℤ)
    (hyF : ∀ j, (eval (y j) F : ZMod (p ^ E)) = 0)
    (hzF : (eval z F : ZMod p) = 0)
    (hyz : ∀ j i, (p : ℤ) ∣ y j i - z i)
    (v : Fin 2)
    (hzJ : (eval z (pderiv v F) : ZMod p) ≠ 0) :
    CurveNormalizationResidueDisc (Fin 2) ι p E hE y := by
  let e : Fin 2 ≃ Fin 2 := Equiv.swap 0 v
  have heval (x : Fin 2 → ℤ) (G : PlaneCurvePolynomial) :
      eval (fun i ↦ x (e i)) (rename e.symm G) = eval x G := by
    rw [eval_rename]
    simp only [Function.comp_def, Equiv.apply_symm_apply]
  have hderiv : pderiv 0 (rename e.symm F) = rename e.symm (pderiv v F) := by
    simpa [e] using pderiv_rename e.symm.injective v F
  apply planeCurveResidueDiscUnpermute e
  apply planeCurveModularResidueDisc p E hp hE
    (rename e.symm F) (fun j i ↦ y j (e i)) (fun i ↦ z (e i))
  · intro j
    simpa only [heval] using hyF j
  · simpa only [heval] using hzF
  · intro j i
    exact hyz j (e i)
  · simpa only [hderiv, heval] using hzJ

end
end TranslatedDepthSeven
