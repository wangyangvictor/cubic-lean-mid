import CubicTenVariables.OscillatoryLocalizationApplication
import CubicTenVariables.ExponentialSums
import CubicTenVariables.LocalSupremumWindow
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Literal dyadic nonzero-frequency error from eq:defERROR2. Continuity and
integrability of each physical frequency contribution are proved explicitly;
summability of the lattice series is a separate theorem, not a convention. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.DyadicFrequencyError
open MvPolynomial MeasureTheory OscillatoryLocalization
open scoped BigOperators Topology ContDiff
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

/-- Exactly the integer moduli R < q <= 2R. -/
def moduli (R : ℝ) : Finset ℕ :=
  (Finset.range (⌊2*R⌋₊+1)).filter fun q => R < (q : ℝ) ∧ (q : ℝ) ≤ 2*R

@[simp] theorem mem_moduli (R : ℝ) (q : ℕ) :
    q ∈ moduli R ↔ R < (q : ℝ) ∧ (q : ℝ) ≤ 2*R := by
  simp only [moduli,Finset.mem_filter,Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨Nat.lt_succ_of_le (Nat.le_floor h.2),h⟩

/-- The original theta shell, with the source's strict lower endpoint. -/
def shell (φ : ℝ) : Set ℝ := {θ | φ < |θ| ∧ |θ| ≤ 2*φ}

theorem measurableSet_shell (φ : ℝ) : MeasurableSet (shell φ) :=
  (isOpen_lt continuous_const continuous_abs).measurableSet.inter
    (isClosed_le continuous_abs continuous_const).measurableSet

theorem shell_subset_Icc (φ : ℝ) : shell φ ⊆ Set.Icc (-2*φ) (2*φ) := by
  intro θ hθ
  simpa only [neg_mul] using abs_le.mp hθ.2

theorem volume_shell_ne_top (φ : ℝ) : volume (shell φ) ≠ ⊤ :=
  ne_top_of_le_ne_top (isCompact_Icc.measure_lt_top.ne) (measure_mono (shell_subset_Icc φ))

theorem volume_shell_le (φ : ℝ) : volume (shell φ) ≤ ENNReal.ofReal (4*φ) := by
  calc
    _ ≤ volume (Set.Icc (-2*φ) (2*φ)) := measure_mono (shell_subset_Icc φ)
    _ = _ := by rw [Real.volume_Icc]; congr 1; ring

/-- The actual physical integral depends continuously on theta. -/
theorem continuous_scaledIntegral (F : MvPolynomial (Fin n) ℝ)
    (w : (Fin n → ℝ) → ℝ) (hw : Continuous w) (hc : HasCompactSupport w)
    (P : ℝ) (hP : P ≠ 0) (β : Fin n → ℝ) :
    Continuous (fun θ => scaledIntegral F w P θ β) := by
  let W : (Fin n → ℝ) → ℝ := fun x => w (P⁻¹ • x)
  have hW : HasCompactSupport W := by
    have hh := chartWeight_compact w hc (0 : Fin n → ℝ) P hP
    change HasCompactSupport (fun x => w (P⁻¹ • (x-0))) at hh
    simpa only [sub_zero] using hh
  let f : ℝ → (Fin n → ℝ) → ℂ := fun θ x => (W x : ℂ)*Complex.exp
    (2*(Real.pi : ℂ)*Complex.I*((θ*eval x F-∑ i,β i*x i : ℝ) : ℂ))
  have hf : Continuous f.uncurry := by
    have hF := F.continuous_eval
    dsimp [f,W,Function.uncurry]
    fun_prop
  have he (θ : ℝ) : scaledIntegral F w P θ β=∫ x in tsupport W, f θ x := by
    change (∫ x, f θ x)=_
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : W x=0 := image_eq_zero_of_notMem_tsupport hx
    simp only [f,hz,Complex.ofReal_zero,zero_mul]
  simp_rw [he]
  exact continuous_parametric_integral_of_continuous hf hW.isCompact

/-- One fixed modulus/frequency's nonnegative mass in the original shell. -/
def frequencyMass (F : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ)
    (P φ : ℝ) (q : ℕ) (v : Fin n → ℤ) : ℝ :=
  ∫ θ in shell φ, ‖scaledIntegral (map (Int.castRingHom ℝ) F) w P θ
    ((q : ℝ)⁻¹ • (fun i => (v i : ℝ)))‖

theorem frequency_integrable (F : MvPolynomial (Fin n) ℤ)
    (w : (Fin n → ℝ) → ℝ) (hw : Continuous w) (hc : HasCompactSupport w)
    (P φ : ℝ) (hP : P ≠ 0) (q : ℕ) (v : Fin n → ℤ) :
    IntegrableOn (fun θ => ‖scaledIntegral (map (Int.castRingHom ℝ) F) w P θ
      ((q : ℝ)⁻¹ • (fun i => (v i : ℝ)))‖) (shell φ) :=
  (continuous_scaledIntegral _ w hw hc P hP _).norm.integrableOn_Icc.mono_set
    (shell_subset_Icc φ)

theorem frequencyMass_nonneg (F : MvPolynomial (Fin n) ℤ)
    (w : (Fin n → ℝ) → ℝ) (P φ : ℝ) (q : ℕ) (v : Fin n → ℤ) :
    0 ≤ frequencyMass F w P φ q v := integral_nonneg fun _ => norm_nonneg _

/-- A uniform pointwise bound integrates over a shell of length at most 4phi. -/
theorem frequencyMass_le (F : MvPolynomial (Fin n) ℤ)
    (w : (Fin n → ℝ) → ℝ) (hw : Continuous w) (hc : HasCompactSupport w)
    (P φ : ℝ) (hP : P ≠ 0) (hφ : 0 ≤ φ) (q : ℕ) (v : Fin n → ℤ)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ θ ∈ shell φ,
      ‖scaledIntegral (map (Int.castRingHom ℝ) F) w P θ
        ((q : ℝ)⁻¹ • (fun i => (v i : ℝ)))‖ ≤ M) :
    frequencyMass F w P φ q v ≤ 4*φ*M := by
  have hi := frequency_integrable F w hw hc P φ hP q v
  have hcst : IntegrableOn (fun _ : ℝ => M) (shell φ) :=
    integrableOn_const (volume_shell_ne_top φ)
  have hb : (volume (shell φ)).toReal ≤ 4*φ := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (volume_shell_le φ)
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 4*φ)] using h
  calc
    _ ≤ ∫ _θ in shell φ, M := setIntegral_mono_on hi hcst (measurableSet_shell φ) hbound
    _ = (volume (shell φ)).toReal*M := by simp [MeasureTheory.measureReal_def]
    _ ≤ _ := mul_le_mul_of_nonneg_right hb hM

/-- The literal summand, with only the zero frequency removed. -/
def term (F : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ)
    (P φ : ℝ) (q : ℕ) (v : Fin n → ℤ) : ℝ :=
  if v=0 then 0 else ‖completeCubicSum F q v‖*frequencyMass F w P φ q v

theorem term_nonneg (F : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ)
    (P φ : ℝ) (q : ℕ) (v : Fin n → ℤ) : 0 ≤ term F w P φ q v := by
  unfold term
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (norm_nonneg _) (frequencyMass_nonneg F w P φ q v)

/-- Exact source E(P;R,phi). Its analytic use requires the proved summability
of the nonzero-frequency series; no convergence is asserted by a definition. -/
def error (F : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ)
    (P R φ : ℝ) : ℝ :=
  ∑ q ∈ moduli R, ((q : ℝ)^n)⁻¹ * ∑' v : Fin n → ℤ, term F w P φ q v

def truncatedError (F : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ)
    (P R φ B : ℝ) : ℝ :=
  ∑ q ∈ moduli R, ((q : ℝ)^n)⁻¹ *
    ∑ v ∈ LocalSupremumWindow.frequencies n B,
      ‖completeCubicSum F q v‖*frequencyMass F w P φ q v

end CubicTenVariables.DyadicFrequencyError
