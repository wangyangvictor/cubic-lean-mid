import CubicTenVariables.SelectedGradientCoordinates
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Lebesgue-volume control of actual gradient fibers on a fixed bounded
selected-gradient chart. The chart distance estimate is explicit; the
measure comparison is proved from mathlib without a literature premise. -/
noncomputable section
namespace CubicTenVariables.GradientChartVolume
open MvPolynomial HessianTheorem11 SelectedGradientCoordinates MeasureTheory Set
open scoped BigOperators ENNReal NNReal

theorem volume_le_pow_mul_image {ι κ : Type*} [Fintype ι] [Fintype κ]
    (hcard : Fintype.card ι = Fintype.card κ)
    (f : (ι → ℝ) → (κ → ℝ)) (U : Set (ι → ℝ)) (C : ℝ≥0)
    (hf : AntilipschitzWith C (U.restrict f))
    (S : Set (ι → ℝ)) (hS : S ⊆ U) :
    volume S ≤ (C : ℝ≥0∞)^(Fintype.card ι) * volume (f '' S) := by
  let S' : Set U := Subtype.val ⁻¹' S
  have hcoe : Subtype.val '' S' = S := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x,hS hx⟩,hx,rfl⟩
  have himage : U.restrict f '' S' = f '' S := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨x,hx,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hS hx⟩,hx,rfl⟩
  have hleft := (isometry_subtype_coe : Isometry (Subtype.val : U → (ι → ℝ))).hausdorffMeasure_image
    (d := (Fintype.card ι : ℝ)) (Or.inl (by positivity)) S'
  rw [hcoe,hausdorffMeasure_pi_real] at hleft
  have h := hf.le_hausdorffMeasure_image (d := (Fintype.card ι : ℝ)) (by positivity) S'
  rw [← hleft,himage,ENNReal.rpow_natCast,hcard,hausdorffMeasure_pi_real] at h
  simpa only [hcard] using h

/-- The selected gradient output written as a single finite real product. -/
def chart {n r : ℕ} (F : MvPolynomial (Fin n) ℝ) (rows cols : Fin r → Fin n)
    (x : Fin n → ℝ) : Fin r ⊕ Complement cols → ℝ :=
  Sum.elim (fun i => eval x (pderiv (rows i) F)) (fun j => x j)

private theorem output_card {n r : ℕ} (cols : Fin r → Fin n)
    (hc : Function.Injective cols) : Fintype.card (Fin r ⊕ Complement cols)=n := by
  have h := finrank_selected_output (K := ℝ) cols hc
  simpa only [Module.finrank_prod,Module.finrank_fintype_fun_eq_card,Fintype.card_sum,
    Fintype.card_fin] using h.symm

private theorem chart_antilipschitz {n r : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (rows cols : Fin r → Fin n) (U : Set (Fin n → ℝ)) (C : ℝ≥0)
    (hf : AntilipschitzWith C (U.restrict (selectedGradientCoordinates F rows cols))) :
    AntilipschitzWith C (U.restrict (chart F rows cols)) := by
  have he := (IsometryEquiv.sumArrowIsometryEquivProdArrow (α := Fin r) (β := Complement cols)
    (γ := ℝ)).symm.isometry.antilipschitz.comp hf
  simpa only [mul_one] using he

/-- A literal fiber window for all formal first partial derivatives. -/
def fiber {n : ℕ} (F : MvPolynomial (Fin n) ℝ) (K : Set (Fin n → ℝ))
    (b : Fin n → ℝ) (δ : ℝ) : Set (Fin n → ℝ) :=
  {x | x ∈ K ∧ ∀ i, |eval x (pderiv i F)-b i| ≤ δ}

private def rectangle {n r : ℕ} (cols : Fin r → Fin n) (b : Fin r → ℝ)
    (δ B : ℝ) : Set (Fin r ⊕ Complement cols → ℝ) :=
  Icc (Sum.elim (fun i => b i-δ) (fun _ => -B))
    (Sum.elim (fun i => b i+δ) (fun _ => B))

private theorem volume_rectangle {n r : ℕ} (cols : Fin r → Fin n)
    (b : Fin r → ℝ) (δ B : ℝ) :
    volume (rectangle cols b δ B) =
      ENNReal.ofReal (2*δ)^r * ENNReal.ofReal (2*B)^(Fintype.card (Complement cols)) := by
  classical
  rw [rectangle,Real.volume_Icc_pi,Fintype.prod_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr]
  have he (i : Fin r) : (b i+δ)-(b i-δ)=2*δ := by ring
  simp only [he,sub_neg_eq_add,← two_mul,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

private theorem image_fiber_subset {n r : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (rows cols : Fin r → Fin n) (K : Set (Fin n → ℝ)) (B : ℝ)
    (hK : ∀ x ∈ K, ∀ i, |x i| ≤ B) (b : Fin n → ℝ) (δ : ℝ) :
    chart F rows cols '' fiber F K b δ ⊆ rectangle cols (fun i => b (rows i)) δ B := by
  rintro _ ⟨x,hx,rfl⟩
  constructor
  · intro i
    rcases i with i|i
    · change b (rows i)-δ ≤ eval x (pderiv (rows i) F)
      have hi := abs_le.mp (hx.2 (rows i))
      linarith
    · exact (abs_le.mp (hK x hx.1 i)).1
  · intro i
    rcases i with i|i
    · change eval x (pderiv (rows i) F) ≤ b (rows i)+δ
      have hi := abs_le.mp (hx.2 (rows i))
      linarith
    · exact (abs_le.mp (hK x hx.1 i)).2

/-- The inverse-distance estimate on the actual selected-gradient chart
bounds a fiber by the volume of its rectangular image. -/
theorem volume_fiber_le {n r : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (rows cols : Fin r → Fin n) (hc : Function.Injective cols)
    (U K : Set (Fin n → ℝ)) (C : ℝ≥0)
    (hf : AntilipschitzWith C (U.restrict (selectedGradientCoordinates F rows cols)))
    (hKU : K ⊆ U) (B : ℝ) (hB : 0 ≤ B)
    (hK : ∀ x ∈ K, ∀ i, |x i| ≤ B) (b : Fin n → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) :
    volume (fiber F K b δ) ≤
      ENNReal.ofReal (((C : ℝ)^n * 2^r * (2*B)^(Fintype.card (Complement cols))) * δ^r) := by
  classical
  have h := volume_le_pow_mul_image
    (by simpa only [Fintype.card_fin] using (output_card cols hc).symm)
    (chart F rows cols) U C (chart_antilipschitz F rows cols U C hf)
    (fiber F K b δ) (fun _ hx => hKU hx.1)
  have hm : volume (chart F rows cols '' fiber F K b δ) ≤
      volume (rectangle cols (fun i => b (rows i)) δ B) :=
    measure_mono (image_fiber_subset F rows cols K B hK b δ)
  have he : (C : ℝ≥0∞)^n * volume (rectangle cols (fun i => b (rows i)) δ B) =
      ENNReal.ofReal (((C : ℝ)^n * 2^r * (2*B)^(Fintype.card (Complement cols))) * δ^r) := by
    rw [volume_rectangle, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_pow (NNReal.coe_nonneg C),
      ← ENNReal.ofReal_pow (by positivity : 0 ≤ 2*δ),
      ← ENNReal.ofReal_pow (by positivity : 0 ≤ 2*B),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ (2*δ)^r),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ (C : ℝ)^n)]
    congr 1
    simp only [mul_pow]
    ring
  calc
    volume (fiber F K b δ) ≤ (C : ℝ≥0∞)^n * volume (chart F rows cols '' fiber F K b δ) := by
      simpa only [Fintype.card_fin] using h
    _ ≤ (C : ℝ≥0∞)^n * volume (rectangle cols (fun i => b (rows i)) δ B) :=
      mul_le_mul_right hm _
    _ = _ := he

private theorem volume_le_box {n : ℕ} (K : Set (Fin n → ℝ)) (B : ℝ) (hB : 0 ≤ B)
    (hK : ∀ x ∈ K, ∀ i, |x i| ≤ B) :
    volume K ≤ ENNReal.ofReal ((2*B)^n) := by
  have hs : K ⊆ Icc (fun _ => -B) (fun _ => B) := by
    intro x hx
    exact ⟨fun i => (abs_le.mp (hK x hx i)).1,fun i => (abs_le.mp (hK x hx i)).2⟩
  have he : volume (Icc (fun _ : Fin n => -B) (fun _ => B)) = ENNReal.ofReal ((2*B)^n) := by
    rw [Real.volume_Icc_pi]
    simp only [sub_neg_eq_add,← two_mul,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
      ENNReal.ofReal_pow (by positivity : 0 ≤ 2*B)]
  exact (measure_mono hs).trans_eq he

/-- One constant precedes every gradient center and every window width.
The bounded set need not be measurable, and the zero-width case is included. -/
theorem exists_bound {n r : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (rows cols : Fin r → Fin n) (hc : Function.Injective cols)
    (U K : Set (Fin n → ℝ)) (C : ℝ≥0)
    (hf : AntilipschitzWith C (U.restrict (selectedGradientCoordinates F rows cols)))
    (hKU : K ⊆ U) (B : ℝ) (hB : 1 ≤ B)
    (hK : ∀ x ∈ K, ∀ i, |x i| ≤ B) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (b : Fin n → ℝ) (δ : ℝ), 0 ≤ δ →
      volume (fiber F K b δ) ≤ ENNReal.ofReal (A*min 1 (δ^r)) := by
  let D : ℝ := (C : ℝ)^n * 2^r * (2*B)^(Fintype.card (Complement cols))
  have hD : 0 ≤ D := by positivity
  let M : ℝ := (2*B)^n
  have hM : 0 ≤ M := by positivity
  let A : ℝ := 1+D+M
  have hA : 1 ≤ A := by dsimp [A]; linarith
  refine ⟨A,hA,?_⟩
  intro b δ hδ
  by_cases hr : δ^r ≤ 1
  · rw [min_eq_right hr]
    apply (volume_fiber_le F rows cols hc U K C hf hKU B (by linarith) hK b δ hδ).trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right
    · change D ≤ A
      dsimp [A]
      linarith
    · positivity
  · rw [min_eq_left (le_of_not_ge hr),mul_one]
    calc
      volume (fiber F K b δ) ≤ volume K := measure_mono (fun _ hx => hx.1)
      _ ≤ ENNReal.ofReal M := volume_le_box K B (by linarith) hK
      _ ≤ ENNReal.ofReal A := ENNReal.ofReal_le_ofReal (by dsimp [A]; linarith)

/-- The same uniform comparison as a finite real volume bound. -/
theorem exists_real_bound {n r : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (rows cols : Fin r → Fin n) (hc : Function.Injective cols)
    (U K : Set (Fin n → ℝ)) (C : ℝ≥0)
    (hf : AntilipschitzWith C (U.restrict (selectedGradientCoordinates F rows cols)))
    (hKU : K ⊆ U) (B : ℝ) (hB : 1 ≤ B)
    (hK : ∀ x ∈ K, ∀ i, |x i| ≤ B) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (b : Fin n → ℝ) (δ : ℝ), 0 ≤ δ →
      (volume (fiber F K b δ)).toReal ≤ A*min 1 (δ^r) := by
  obtain ⟨A,hA,hbound⟩ := exists_bound F rows cols hc U K C hf hKU B hB hK
  refine ⟨A,hA,?_⟩
  intro b δ hδ
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbound b δ hδ)
  simpa only [ENNReal.toReal_ofReal (mul_nonneg (zero_le_one.trans hA)
    (le_min zero_le_one (pow_nonneg hδ r)))] using h

/-- Norm-form windows have the same bound; the norm here is the actual
supremum norm on the finite real coordinate space. -/
theorem exists_norm_bound {n r : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (rows cols : Fin r → Fin n) (hc : Function.Injective cols)
    (U K : Set (Fin n → ℝ)) (C : ℝ≥0)
    (hf : AntilipschitzWith C (U.restrict (selectedGradientCoordinates F rows cols)))
    (hKU : K ⊆ U) (B : ℝ) (hB : 1 ≤ B)
    (hK : ∀ x ∈ K, ∀ i, |x i| ≤ B) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (b : Fin n → ℝ) (δ : ℝ), 0 ≤ δ →
      volume {x | x ∈ K ∧ ‖gradient F x-b‖ ≤ δ} ≤ ENNReal.ofReal (A*min 1 (δ^r)) := by
  obtain ⟨A,hA,hbound⟩ := exists_bound F rows cols hc U K C hf hKU B hB hK
  refine ⟨A,hA,?_⟩
  intro b δ hδ
  apply (measure_mono ?_).trans (hbound b δ hδ)
  intro x hx
  refine ⟨hx.1,?_⟩
  intro i
  have hi := (norm_le_pi_norm (gradient F x-b) i).trans hx.2
  simpa only [Pi.sub_apply,Real.norm_eq_abs,gradient] using hi

/-- A literal nonzero Hessian minor constructs both the open chart and the
volume constant. Every subset of that one chart shares the same constant. -/
theorem exists_local_bound {n r : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (rows cols : Fin r → Fin n) (x : Fin n → ℝ)
    (hdet : ((hessian F x).submatrix rows cols).det ≠ 0) :
    ∃ (U : Set (Fin n → ℝ)) (A : ℝ), x ∈ U ∧ IsOpen U ∧ 1 ≤ A ∧
      ∀ K : Set (Fin n → ℝ), K ⊆ U → ∀ (b : Fin n → ℝ) (δ : ℝ), 0 ≤ δ →
        volume (fiber F K b δ) ≤ ENNReal.ofReal (A*min 1 (δ^r)) := by
  obtain ⟨V,C,hxV,hV,hanti⟩ := exists_selectedGradient_antilipschitz F rows cols x hdet
  let U : Set (Fin n → ℝ) := V ∩ Metric.ball x 1
  have hxU : x ∈ U := ⟨hxV,Metric.mem_ball_self (by norm_num)⟩
  have hU : IsOpen U := hV.inter Metric.isOpen_ball
  have hB : 1 ≤ ‖x‖+1 := by linarith [norm_nonneg x]
  have hbox : ∀ y ∈ U, ∀ i, |y i| ≤ ‖x‖+1 := by
    intro y hy i
    have hb := Metric.mem_ball.mp hy.2
    have ht := dist_triangle y x 0
    simp only [dist_zero_right] at ht
    have hi := norm_le_pi_norm y i
    rw [Real.norm_eq_abs] at hi
    linarith
  obtain ⟨A,hA,hbound⟩ := exists_bound F rows cols
    (cols_injective_of_submatrix_det_ne_zero _ _ _ hdet) V U C hanti
    (fun _ hy => hy.1) (‖x‖+1) hB hbox
  refine ⟨U,A,hxU,hU,hA,?_⟩
  intro K hK b δ hδ
  apply (measure_mono ?_).trans (hbound b δ hδ)
  intro y hy
  exact ⟨hK hy.1,hy.2⟩

end CubicTenVariables.GradientChartVolume
