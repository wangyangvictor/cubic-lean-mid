import TranslatedDepthSeven.PlaneCurveResidueDiscFirstChart
import TranslatedDepthSeven.PlaneCurveSmoothResidueCount
import TranslatedDepthSeven.ProjectedHypersurfaceDerivativeBridge
import TranslatedDepthSeven.AffinePolynomialChange

/-!
# A literal integer certificate for smooth plane residues

At an integral point select the first nonzero affine partial, using the
second partial when the first is zero.  The resulting integer is zero
exactly on the affine gradient-zero locus, and a prime avoiding it gives
one of the actual smooth residues.  Euler's identity identifies this
exceptional locus with the projective gradient-zero locus on the curve.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

/-- An explicit choice of one of the two evaluated affine derivatives. -/
def planeCurveDerivativeCertificate
    (f : MvPolynomial (Fin 2) ℤ) (z : IntVector 2) : ℤ :=
  if eval z (pderiv 0 f) = 0 then eval z (pderiv 1 f)
  else eval z (pderiv 0 f)

theorem exists_partial_eq_planeCurveDerivativeCertificate
    (f : MvPolynomial (Fin 2) ℤ) (z : IntVector 2) :
    ∃ j : Fin 2, eval z (pderiv j f) = planeCurveDerivativeCertificate f z := by
  unfold planeCurveDerivativeCertificate
  split_ifs
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩

theorem planeCurveDerivativeCertificate_eq_zero_iff
    (f : MvPolynomial (Fin 2) ℤ) (z : IntVector 2) :
    planeCurveDerivativeCertificate f z = 0 ↔
      ∀ j : Fin 2, eval z (pderiv j f) = 0 := by
  unfold planeCurveDerivativeCertificate
  split_ifs with h
  · constructor
    · intro h1 j
      fin_cases j
      · exact h
      · exact h1
    · intro hall
      exact hall 1
  · constructor
    · exact fun hz ↦ (h hz).elim
    · intro hall
      exact hall 0

theorem planeCurveDerivativeCertificate_natAbs_le
    (f : MvPolynomial (Fin 2) ℤ) (z : IntVector 2) (B : ℕ)
    (hB : ∀ j : Fin 2, (eval z (pderiv j f)).natAbs ≤ B) :
    (planeCurveDerivativeCertificate f z).natAbs ≤ B := by
  obtain ⟨j, hj⟩ := exists_partial_eq_planeCurveDerivativeCertificate f z
  rw [← hj]
  exact hB j

theorem residue_mem_planeCurveSmoothResidues_of_certificate
    (f : MvPolynomial (Fin 2) ℤ) (z : IntVector 2)
    (hzero : eval z f = 0) {p : ℕ} (hp : p.Prime)
    (hcertificate : ¬ (p : ℤ) ∣ planeCurveDerivativeCertificate f z) :
    integralResidueVector z ∈ planeCurveSmoothResidues f p := by
  obtain ⟨j, hj⟩ := exists_partial_eq_planeCurveDerivativeCertificate f z
  apply integralResidueVector_mem_planeCurveSmoothResidues f hp z hzero j
  rw [hj]
  exact hcertificate

theorem planeCurveFirstChartDehomogenize_eq_integral :
    planeCurveFirstChartDehomogenize =
      (integralDehomogenizeAtZeroHom (N := 2)) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [planeCurveFirstChartDehomogenize]
  · intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;>
      simp [planeCurveFirstChartDehomogenize]

theorem eval_pderiv_planeCurveFirstChartDehomogenize
    (P : MvPolynomial (Fin 3) ℤ) (z : IntVector 2) (j : Fin 2) :
    eval z (pderiv j (planeCurveFirstChartDehomogenize P)) =
      eval (integralAffineChartVector z) (pderiv j.succ P) := by
  rw [planeCurveFirstChartDehomogenize_eq_integral]
  exact eval_pderiv_integralDehomogenizeAtZeroHom P z j

/-- Dehomogenizing a plane equation cannot increase total degree. -/
theorem totalDegree_planeCurveFirstChartDehomogenize_le
    (P : MvPolynomial (Fin 3) ℤ) :
    (planeCurveFirstChartDehomogenize P).totalDegree ≤ P.totalDegree := by
  rw [planeCurveFirstChartDehomogenize_eq_integral]
  apply totalDegree_aeval_le_of_totalDegree_le_one
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp

/-- On the actual homogeneous curve, the zero certificate detects all three
projective derivatives, without dividing by the degree. -/
theorem planeCurveDerivativeCertificate_eq_zero_iff_projective_gradient
    {δ : ℕ} (P : MvPolynomial (Fin 3) ℤ) (hPhom : P.IsHomogeneous δ)
    (z : IntVector 2) (hPzero : eval (integralAffineChartVector z) P = 0) :
    planeCurveDerivativeCertificate (planeCurveFirstChartDehomogenize P) z = 0 ↔
      ∀ j : Fin 3, eval (integralAffineChartVector z) (pderiv j P) = 0 := by
  rw [planeCurveDerivativeCertificate_eq_zero_iff]
  constructor
  · intro haffine
    by_contra hfull
    push_neg at hfull
    obtain ⟨j, hj⟩ := exists_nonzero_affine_partial_of_homogeneous_gradient
      P hPhom (integralAffineChartVector z) rfl hPzero hfull
    exact hj ((eval_pderiv_planeCurveFirstChartDehomogenize P z j).symm.trans
      (haffine j))
  · intro hfull j
    rw [eval_pderiv_planeCurveFirstChartDehomogenize]
    exact hfull j.succ

end

end TranslatedDepthSeven
