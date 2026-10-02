import TranslatedDepthSeven.HomogeneousLinearElimination

/-!
# A monic relation gives a homogeneous separator

The coefficients of a monic polynomial in one coordinate need not be
homogeneous.  Its homogeneous component of the polynomial's degree still
has value one at `[1:0:...:0]`.  Substituting degree-one forms that vanish
at an exterior point transports this assertion to that point.  Thus no
homogeneity assertion about minimal-polynomial coefficients is needed.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

universe u v w

variable {K : Type u} [Field K] {σ : Type v} [Finite σ]

/-- The component of the monic degree keeps its pure leading power and
therefore takes value one on the distinguished coordinate axis. -/
theorem eval_affineChartZero_homogeneousComponent_monic
    (p : Polynomial (MvPolynomial σ K)) (hp : p.Monic) :
    eval (affineChartVector (0 : σ → K))
      (homogeneousComponent p.natDegree ((optionEquivLeft K σ).symm p)) = 1 := by
  classical
  let m : Option σ →₀ ℕ := (0 : σ →₀ ℕ).optionElim p.natDegree
  let F := (optionEquivLeft K σ).symm p
  let H := homogeneousComponent p.natDegree F
  have hmdegree : m.degree = p.natDegree := by simp [m]
  have hFcoeff : coeff m F = 1 := by
    have h := optionEquivLeft_coeff_coeff K σ m F
    have hpcoeff : p.coeff p.natDegree = 1 := hp.coeff_natDegree
    simpa [F, m, hpcoeff] using h.symm
  have hHcoeff : coeff m H = 1 := by
    simp only [H, coeff_homogeneousComponent, hmdegree, if_true, hFcoeff]
  have hHhom : H.IsHomogeneous p.natDegree :=
    homogeneousComponent_isHomogeneous p.natDegree F
  have htop := coeff_optionEquivLeft_degree_eq_C_eval_affineChartVector_zero
    H p.natDegree hHhom
  have heval : coeff 0 ((optionEquivLeft K σ H).coeff p.natDegree) =
      eval (affineChartVector (0 : σ → K)) H := by
    have h := congrArg (coeff (0 : σ →₀ ℕ)) htop
    simpa using h
  have htopcoeff : coeff 0 ((optionEquivLeft K σ H).coeff p.natDegree) = coeff m H := by
    simpa [m] using optionEquivLeft_coeff_coeff K σ m H
  exact heval.symm.trans (htopcoeff.trans hHcoeff)

/-- Substitution by degree-one forms whose displayed values are `1,0,...,0`
preserves the value-one homogeneous separator. -/
theorem eval_homogeneousComponent_monic_linear_substitution
    {τ : Type w} (p : Polynomial (MvPolynomial σ K)) (hp : p.Monic)
    (l : Option σ → MvPolynomial τ K)
    (hl : ∀ i, (l i).IsHomogeneous 1)
    (x : τ → K) (hxnone : eval x (l none) = 1)
    (hxsome : ∀ i, eval x (l (some i)) = 0) :
    eval x (homogeneousComponent p.natDegree
      (aeval l ((optionEquivLeft K σ).symm p))) = 1 := by
  rw [homogeneousComponent_aeval_degreeOne l hl]
  have hcomposition : (aeval x).comp (aeval l) =
      aeval (affineChartVector (0 : σ → K)) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | none => simpa only [AlgHom.comp_apply, MvPolynomial.aeval_X] using hxnone
    | some i => simpa only [AlgHom.comp_apply, MvPolynomial.aeval_X] using hxsome i
  have heval := DFunLike.congr_fun hcomposition
    (homogeneousComponent p.natDegree ((optionEquivLeft K σ).symm p))
  change eval x (aeval l (homogeneousComponent p.natDegree
      ((optionEquivLeft K σ).symm p))) = _ at heval
  exact heval.trans (eval_affineChartZero_homogeneousComponent_monic p hp)

end

end TranslatedDepthSeven
