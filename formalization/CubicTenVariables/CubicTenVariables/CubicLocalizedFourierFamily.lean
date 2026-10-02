import CubicTenVariables.UniformFourierFamily
import CubicTenVariables.CubicTaylorExpansion
import CubicTenVariables.PolynomialCalculus

/-! Uniform Fourier decay for the actual localized cubic amplitudes. The center,
scale and scaled phase vary over a compact set, including scale zero. Smoothness
and joint continuity of all derivatives are proved, not assumed for the family.
Bump normalization, the localization identity and the outer gradient-window
estimate are separate steps and are not asserted here. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CubicLocalizedFourierFamily
open MvPolynomial MeasureTheory HessianTheorem11
open scoped BigOperators ContDiff Topology FourierTransform

variable {n : ℕ}

/-- The nonlinear Taylor remainder after its quadratic scale has been removed. -/
def remainder (F : MvPolynomial (Fin n) ℝ) (y : Fin n → ℝ) (δ : ℝ)
    (z : Fin n → ℝ) : ℝ :=
  CubicTaylorExpansion.quadraticAt F y z + δ * eval z F

/-- The actual localized amplitude, before the shifted Fourier character. -/
def amplitude (F : MvPolynomial (Fin n) ℝ) (w φ : (Fin n → ℝ) → ℝ)
    (y : Fin n → ℝ) (δ ℓ : ℝ) (z : Fin n → ℝ) : ℂ :=
  (w (y + δ • z) : ℂ) * (φ z : ℂ) *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ℓ * remainder F y δ z : ℝ))

/-- No division by the scale is needed, so the identity includes scale zero. -/
theorem scaled_remainder (F : MvPolynomial (Fin n) ℝ) (hF : F.IsHomogeneous 3)
    (y z : Fin n → ℝ) (t δ : ℝ) :
    t * (eval (y + δ • z) F - eval y F -
      δ * CubicTaylorExpansion.directional F y z) =
      (t * δ^2) * remainder F y δ z := by
  rw [CubicTaylorExpansion.eval_cubic_add_smul F hF]
  unfold remainder
  ring

private theorem smooth_partial_derivatives
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : P → E → ℂ) (hA : ContDiff ℝ ∞ (Function.uncurry A)) (j : ℕ) :
    ContDiff ℝ ∞ (fun z : P × E => iteratedFDeriv ℝ j (A z.1) z.2) := by
  induction j with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply] using
      (continuousMultilinearCurryFin0 ℝ E ℂ).symm.toContinuousLinearEquiv.contDiff.comp hA
  | succ j ih =>
    have hd : ContDiff ℝ ∞ (fun z : P × E =>
        fderiv ℝ (iteratedFDeriv ℝ j (A z.1)) z.2) := by
      have hh : ContDiff ℝ ∞ (Function.uncurry
          (fun z : P × E => iteratedFDeriv ℝ j (A z.1))) :=
        ih.comp (show ContDiff ℝ ∞ (fun z : (P × E) × E => (z.1.1,z.2)) from
          contDiff_fst.fst.prodMk contDiff_snd)
      exact hh.fderiv (n := ∞) contDiff_snd (by simp)
    simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply] using
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => E) ℂ).symm.toContinuousLinearEquiv.contDiff.comp hd

/-- Joint smoothness in the center, scale, scaled phase and integration variable. -/
theorem amplitude_smooth (F : MvPolynomial (Fin n) ℝ)
    (w φ : (Fin n → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (fun p : ((Fin n → ℝ) × ℝ × ℝ) × (Fin n → ℝ) =>
      amplitude F w φ p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  have hy : ContDiff ℝ ∞ (fun p : ((Fin n → ℝ) × ℝ × ℝ) × (Fin n → ℝ) => p.1.1) :=
    contDiff_fst.fst
  have hδ : ContDiff ℝ ∞ (fun p : ((Fin n → ℝ) × ℝ × ℝ) × (Fin n → ℝ) => p.1.2.1) :=
    contDiff_fst.snd.fst
  have hℓ : ContDiff ℝ ∞ (fun p : ((Fin n → ℝ) × ℝ × ℝ) × (Fin n → ℝ) => p.1.2.2) :=
    contDiff_fst.snd.snd
  have hz : ContDiff ℝ ∞ (fun p : ((Fin n → ℝ) × ℝ × ℝ) × (Fin n → ℝ) => p.2) := contDiff_snd
  have hq : ContDiff ℝ ∞ (fun p : ((Fin n → ℝ) × ℝ × ℝ) × (Fin n → ℝ) =>
      CubicTaylorExpansion.quadraticAt F p.1.1 p.2) := by
    unfold CubicTaylorExpansion.quadraticAt CubicTaylorExpansion.directional dotProduct gradient
    apply ContDiff.sum
    intro i _
    exact ((contDiff_apply ℝ ℝ i).comp hy).mul
      ((PolynomialCalculus.contDiff_eval (pderiv i F)).comp hz)
  have hr := hq.add (hδ.mul ((PolynomialCalculus.contDiff_eval F).comp hz))
  exact ((Complex.ofRealCLM.contDiff.comp (hw.comp (hy.add (hδ.smul hz)))).mul
    (Complex.ofRealCLM.contDiff.comp (hφ.comp hz))).mul
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (hℓ.mul hr))).cexp

/-- The fixed bump supplies a common support independently of every parameter. -/
theorem amplitude_support (F : MvPolynomial (Fin n) ℝ)
    (w φ : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ) (δ ℓ : ℝ) :
    tsupport (amplitude F w φ y δ ℓ) ⊆ tsupport φ := by
  apply closure_mono
  intro z hz
  by_contra hφ
  apply hz
  simp only [Function.mem_support, not_not] at hφ
  simp [amplitude, hφ]

/-- A single decay constant works for every center in the fixed compact set,
all scales in the closed unit interval, all bounded scaled phases, and every
frequency. The support and derivative hypotheses needed for uniform Fourier
decay have been discharged for this literal amplitude. -/
theorem exists_uniform_bound (F : MvPolynomial (Fin n) ℝ)
    (w φ : (Fin n → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (Y : Set (Fin n → ℝ)) (hY : IsCompact Y) (Λ : ℝ) (_hΛ : 0 ≤ Λ) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ y ∈ Y, ∀ δ ∈ Set.Icc (0 : ℝ) 1,
      ∀ ℓ ∈ Set.Icc (-Λ) Λ, ∀ ξ : Fin n → ℝ,
        ‖ScalarLatticePoisson.fourier (amplitude F w φ y δ ℓ) ξ‖ ≤
          C / (1 + ‖ξ‖)^N := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let S : Set ((Fin n → ℝ) × ℝ × ℝ) := Y ×ˢ (Set.Icc 0 1 ×ˢ Set.Icc (-Λ) Λ)
  have hS : IsCompact S := hY.prod (isCompact_Icc.prod isCompact_Icc)
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let B : ((Fin n → ℝ) × ℝ × ℝ) → EuclideanSpace ℝ (Fin n) → ℂ :=
    fun p z => amplitude F w φ p.1 p.2.1 p.2.2 (e z)
  have hB : ContDiff ℝ ∞ (Function.uncurry B) :=
    (amplitude_smooth F w φ hw hφ).comp
      (contDiff_fst.prodMk (e.contDiff.comp contDiff_snd))
  let A : S → EuclideanSpace ℝ (Fin n) → ℂ := fun p => B p.val
  have hA : ∀ p, ContDiff ℝ ∞ (A p) := fun p =>
    hB.comp (contDiff_const.prodMk contDiff_id)
  let K := tsupport (fun z : EuclideanSpace ℝ (Fin n) => φ (e z))
  have hK : IsCompact K := hcφ.comp_homeomorph e.toHomeomorph
  have hs : ∀ p, tsupport (A p) ⊆ K := by
    intro p
    apply closure_mono
    intro z hz
    by_contra hzero
    apply hz
    simp only [Function.mem_support, not_not] at hzero
    simp [A, B, amplitude, hzero]
  have hj : ∀ j, j ≤ N → Continuous (fun z : S × EuclideanSpace ℝ (Fin n) =>
      iteratedFDeriv ℝ j (A z.1) z.2) := by
    intro j _
    exact (smooth_partial_derivatives B hB j).continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨C,hC,hbound⟩ := UniformFourierFamily.exists_coordinate_bound A hA K hK hs N hj
  refine ⟨C,hC,?_⟩
  intro y hy δ hδ ℓ hℓ ξ
  simpa [A,B,e] using hbound ⟨(y,δ,ℓ),hy,hδ,hℓ⟩ ξ

end CubicTenVariables.CubicLocalizedFourierFamily
