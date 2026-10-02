import CubicTenVariables.GradientChartVolume

/-! Actual fixed-input-coordinate slices of a selected-gradient chart.
The selected output rows and varying input columns remain independent. -/
noncomputable section
namespace CubicTenVariables.SelectedGradientSliceVolume
open MvPolynomial HessianTheorem11 SelectedGradientCoordinates MeasureTheory Set
open scoped BigOperators NNReal ENNReal
variable {n r : ℕ}

/-- The selected input columns and their actual complement partition all coordinates. -/
def indexEquiv (cols : Fin r → Fin n) (hc : Function.Injective cols) :
    Fin r ⊕ Complement cols ≃ Fin n := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective cols hc) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range cols))

@[simp] theorem indexEquiv_inl (cols : Fin r → Fin n) (hc : Function.Injective cols)
    (i : Fin r) : indexEquiv cols hc (Sum.inl i)=cols i := rfl

@[simp] theorem indexEquiv_inr (cols : Fin r → Fin n) (hc : Function.Injective cols)
    (i : Complement cols) : indexEquiv cols hc (Sum.inr i)=i := rfl

/-- Reconstruct the original vector from the varying selected inputs and
fixed untouched input coordinates. -/
def combine (cols : Fin r → Fin n) (hc : Function.Injective cols)
    (z : Fin r → ℝ) (w : Complement cols → ℝ) : Fin n → ℝ :=
  fun i => Sum.elim z w ((indexEquiv cols hc).symm i)

@[simp] theorem combine_selected (cols : Fin r → Fin n) (hc : Function.Injective cols)
    (z : Fin r → ℝ) (w : Complement cols → ℝ) (i : Fin r) :
    combine cols hc z w (cols i)=z i := by
  change Sum.elim z w ((indexEquiv cols hc).symm (indexEquiv cols hc (Sum.inl i)))=z i
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem combine_complement (cols : Fin r → Fin n) (hc : Function.Injective cols)
    (z : Fin r → ℝ) (w : Complement cols → ℝ) (i : Complement cols) :
    combine cols hc z w i=w i := by
  change Sum.elim z w ((indexEquiv cols hc).symm (indexEquiv cols hc (Sum.inr i)))=w i
  rw [Equiv.symm_apply_apply]
  rfl

theorem combine_reconstruct (cols : Fin r → Fin n) (hc : Function.Injective cols)
    (x : Fin n → ℝ) : combine cols hc (fun i => x (cols i)) (fun j => x j)=x := by
  funext i
  obtain ⟨j,rfl⟩ := (indexEquiv cols hc).surjective i
  cases j <;> simp

/-- The complete coordinate split, for later integration over fixed complementary fibers. -/
def splitEquiv (cols : Fin r → Fin n) (hc : Function.Injective cols) :
    (Fin n → ℝ) ≃ (Fin r → ℝ) × (Complement cols → ℝ) :=
  (((indexEquiv cols hc).symm).arrowCongr (Equiv.refl ℝ)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

@[simp] theorem splitEquiv_symm (cols : Fin r → Fin n) (hc : Function.Injective cols)
    (z : Fin r → ℝ) (w : Complement cols → ℝ) :
    (splitEquiv cols hc).symm (z,w)=combine cols hc z w := rfl

/-- Reconstruction on a fixed complementary fiber preserves the exact sup distance. -/
theorem dist_combine (cols : Fin r → Fin n) (hc : Function.Injective cols)
    (w : Complement cols → ℝ) (z z' : Fin r → ℝ) :
    dist (combine cols hc z w) (combine cols hc z' w)=dist z z' := by
  apply le_antisymm
  · apply (dist_pi_le_iff dist_nonneg).mpr
    intro i
    obtain ⟨j,rfl⟩ := (indexEquiv cols hc).surjective i
    cases j with
    | inl j => simpa using dist_le_pi_dist z z' j
    | inr j => simp
  · apply (dist_pi_le_iff dist_nonneg).mpr
    intro i
    simpa using dist_le_pi_dist (combine cols hc z w) (combine cols hc z' w) (cols i)

/-- Literal selected formal partials after fixing the untouched inputs. -/
def sliceGradient (F : MvPolynomial (Fin n) ℝ) (rows cols : Fin r → Fin n)
    (hc : Function.Injective cols) (w : Complement cols → ℝ) (z : Fin r → ℝ) : Fin r → ℝ :=
  fun i => eval (combine cols hc z w) (pderiv (rows i) F)

def sliceDomain (cols : Fin r → Fin n) (hc : Function.Injective cols)
    (U : Set (Fin n → ℝ)) (w : Complement cols → ℝ) : Set (Fin r → ℝ) :=
  {z | combine cols hc z w ∈ U}

theorem selectedGradientCoordinates_combine (F : MvPolynomial (Fin n) ℝ)
    (rows cols : Fin r → Fin n) (hc : Function.Injective cols)
    (w : Complement cols → ℝ) (z : Fin r → ℝ) :
    selectedGradientCoordinates F rows cols (combine cols hc z w)=
      (sliceGradient F rows cols hc w z,w) := by
  apply Prod.ext
  · rfl
  · funext i
    exact combine_complement cols hc z w i

/-- The actual chart inverse-distance bound restricts to every fixed
complementary input fiber with the same constant. -/
theorem slice_antilipschitz (F : MvPolynomial (Fin n) ℝ)
    (rows cols : Fin r → Fin n) (hc : Function.Injective cols)
    (U : Set (Fin n → ℝ)) (C : ℝ≥0)
    (hf : AntilipschitzWith C (U.restrict (selectedGradientCoordinates F rows cols)))
    (w : Complement cols → ℝ) :
    AntilipschitzWith C ((sliceDomain cols hc U w).restrict (sliceGradient F rows cols hc w)) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro z z'
  have h := hf.le_mul_dist ⟨combine cols hc z w,z.property⟩
    ⟨combine cols hc z' w,z'.property⟩
  change dist (combine cols hc z w) (combine cols hc z' w) ≤
    (C : ℝ)*dist (selectedGradientCoordinates F rows cols (combine cols hc z w))
      (selectedGradientCoordinates F rows cols (combine cols hc z' w)) at h
  rw [dist_combine,selectedGradientCoordinates_combine,selectedGradientCoordinates_combine] at h
  simpa only [Prod.dist_eq,dist_self,max_eq_left dist_nonneg] using h

/-- Fixed untouched inputs leave only selected-gradient variation in the
full chart distance. This statement uses the original vectors directly. -/
theorem dist_le_selected_of_complement_eq (F : MvPolynomial (Fin n) ℝ)
    (rows cols : Fin r → Fin n) (U : Set (Fin n → ℝ)) (C : ℝ≥0)
    (hf : AntilipschitzWith C (U.restrict (selectedGradientCoordinates F rows cols)))
    (x y : Fin n → ℝ) (hx : x ∈ U) (hy : y ∈ U)
    (hxy : ∀ i : Complement cols, x i=y i) :
    dist x y ≤ (C : ℝ)*dist (fun i => eval x (pderiv (rows i) F))
      (fun i => eval y (pderiv (rows i) F)) := by
  have h := hf.le_mul_dist ⟨x,hx⟩ ⟨y,hy⟩
  change dist x y ≤ (C : ℝ)*dist
    ((fun i => eval x (pderiv (rows i) F)),fun j : Complement cols => x j)
    ((fun i => eval y (pderiv (rows i) F)),fun j : Complement cols => y j) at h
  rw [Prod.dist_eq,funext hxy,dist_self,max_eq_left dist_nonneg] at h
  exact h

/-- The actual selected-gradient window on a fixed input slice. -/
def sliceFiber (F : MvPolynomial (Fin n) ℝ) (rows cols : Fin r → Fin n)
    (hc : Function.Injective cols) (K : Set (Fin n → ℝ))
    (w : Complement cols → ℝ) (b : Fin r → ℝ) (δ : ℝ) : Set (Fin r → ℝ) :=
  {z | combine cols hc z w ∈ K ∧ ∀ i, |sliceGradient F rows cols hc w z i-b i| ≤ δ}

/-- Uniform r-dimensional slice volume, with no principal-minor assumption
and no supplied point-count or measure estimate. -/
theorem volume_slice_le (F : MvPolynomial (Fin n) ℝ)
    (rows cols : Fin r → Fin n) (hc : Function.Injective cols)
    (U K : Set (Fin n → ℝ)) (C : ℝ≥0)
    (hf : AntilipschitzWith C (U.restrict (selectedGradientCoordinates F rows cols)))
    (hKU : K ⊆ U) (w : Complement cols → ℝ) (b : Fin r → ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    volume (sliceFiber F rows cols hc K w b δ) ≤
      ENNReal.ofReal (((C : ℝ)^r*2^r)*δ^r) := by
  classical
  have h := GradientChartVolume.volume_le_pow_mul_image rfl
    (sliceGradient F rows cols hc w) (sliceDomain cols hc U w) C
    (slice_antilipschitz F rows cols hc U C hf w)
    (sliceFiber F rows cols hc K w b δ) (fun _ hz => hKU hz.1)
  have himage : sliceGradient F rows cols hc w '' sliceFiber F rows cols hc K w b δ ⊆
      Icc (fun i => b i-δ) (fun i => b i+δ) := by
    rintro _ ⟨z,hz,rfl⟩
    exact ⟨fun i => by have h := abs_le.mp (hz.2 i); linarith,
      fun i => by have h := abs_le.mp (hz.2 i); linarith⟩
  have hv : volume (Icc (fun i : Fin r => b i-δ) (fun i => b i+δ))=
      ENNReal.ofReal ((2*δ)^r) := by
    rw [Real.volume_Icc_pi]
    have he (i : Fin r) : (b i+δ)-(b i-δ)=2*δ := by ring
    simp only [he,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
      ENNReal.ofReal_pow (by positivity : 0 ≤ 2*δ)]
  have hm := measure_mono (μ := volume) himage
  rw [hv] at hm
  calc
    _ ≤ (C : ℝ≥0∞)^r * volume (sliceGradient F rows cols hc w '' sliceFiber F rows cols hc K w b δ) := by
      simpa only [Fintype.card_fin] using h
    _ ≤ (C : ℝ≥0∞)^r * ENNReal.ofReal ((2*δ)^r) := mul_le_mul_right hm _
    _ = _ := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_pow (NNReal.coe_nonneg C),
        ← ENNReal.ofReal_mul (pow_nonneg (NNReal.coe_nonneg C) r)]
      congr 1
      rw [mul_pow]
      ring

/-- The slice measure is finite, including the empty-rank and zero-width cases. -/
theorem volume_slice_ne_top (F : MvPolynomial (Fin n) ℝ)
    (rows cols : Fin r → Fin n) (hc : Function.Injective cols)
    (U K : Set (Fin n → ℝ)) (C : ℝ≥0)
    (hf : AntilipschitzWith C (U.restrict (selectedGradientCoordinates F rows cols)))
    (hKU : K ⊆ U) (w : Complement cols → ℝ) (b : Fin r → ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ) : volume (sliceFiber F rows cols hc K w b δ) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (volume_slice_le F rows cols hc U K C hf hKU w b δ hδ)

/-- One real constant precedes every fixed complementary coordinate, gradient
center, and nonnegative window width. -/
theorem exists_real_bound (F : MvPolynomial (Fin n) ℝ)
    (rows cols : Fin r → Fin n) (hc : Function.Injective cols)
    (U K : Set (Fin n → ℝ)) (C : ℝ≥0)
    (hf : AntilipschitzWith C (U.restrict (selectedGradientCoordinates F rows cols)))
    (hKU : K ⊆ U) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (w : Complement cols → ℝ) (b : Fin r → ℝ) (δ : ℝ),
      0 ≤ δ → (volume (sliceFiber F rows cols hc K w b δ)).toReal ≤ A*δ^r := by
  let A : ℝ := 1+(C : ℝ)^r*2^r
  have hD : 0 ≤ (C : ℝ)^r*2^r := by positivity
  have hA : 1 ≤ A := by dsimp [A]; linarith
  refine ⟨A,hA,?_⟩
  intro w b δ hδ
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (volume_slice_le F rows cols hc U K C hf hKU w b δ hδ)
  rw [ENNReal.toReal_ofReal (mul_nonneg hD (pow_nonneg hδ r))] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right
  · dsimp [A]
    linarith
  · positivity

/-- A fixed bounded chart subset supplies the trivial bound as well, uniformly
in the fixed complementary inputs, including slices which are empty. -/
theorem exists_bounded_bound (F : MvPolynomial (Fin n) ℝ)
    (rows cols : Fin r → Fin n) (hc : Function.Injective cols)
    (U K : Set (Fin n → ℝ)) (C : ℝ≥0)
    (hf : AntilipschitzWith C (U.restrict (selectedGradientCoordinates F rows cols)))
    (hKU : K ⊆ U) (B : ℝ) (hB : 1 ≤ B)
    (hK : ∀ x ∈ K, ∀ i, |x i| ≤ B) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (w : Complement cols → ℝ) (b : Fin r → ℝ) (δ : ℝ),
      0 ≤ δ → volume (sliceFiber F rows cols hc K w b δ) ≤
        ENNReal.ofReal (A*min 1 (δ^r)) := by
  let D : ℝ := (C : ℝ)^r*2^r
  let M : ℝ := (2*B)^r
  have hD : 0 ≤ D := by positivity
  have hM : 0 ≤ M := by positivity
  let A : ℝ := 1+D+M
  have hA : 1 ≤ A := by dsimp [A]; linarith
  refine ⟨A,hA,?_⟩
  intro w b δ hδ
  by_cases h : δ^r ≤ 1
  · rw [min_eq_right h]
    apply (volume_slice_le F rows cols hc U K C hf hKU w b δ hδ).trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right
    · change D ≤ A
      dsimp [A]
      linarith
    · positivity
  · rw [min_eq_left (le_of_not_ge h),mul_one]
    have hs : sliceFiber F rows cols hc K w b δ ⊆
        Icc (fun _ => -B) (fun _ => B) := by
      intro z hz
      have hzi (i : Fin r) : |z i| ≤ B := by
        simpa only [combine_selected] using hK _ hz.1 (cols i)
      exact ⟨fun i => (abs_le.mp (hzi i)).1,fun i => (abs_le.mp (hzi i)).2⟩
    have hv : volume (Icc (fun _ : Fin r => -B) (fun _ => B))=ENNReal.ofReal M := by
      rw [Real.volume_Icc_pi]
      simp only [sub_neg_eq_add,← two_mul,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
        M,ENNReal.ofReal_pow (by positivity : 0 ≤ 2*B)]
    calc
      _ ≤ volume (Icc (fun _ : Fin r => -B) (fun _ => B)) := measure_mono hs
      _ = ENNReal.ofReal M := hv
      _ ≤ ENNReal.ofReal A := ENNReal.ofReal_le_ofReal (by dsimp [A]; linarith)

/-- The bounded-slice estimate as a real volume, with the constant preceding
all complementary coordinates and selected-gradient centers. -/
theorem exists_bounded_real_bound (F : MvPolynomial (Fin n) ℝ)
    (rows cols : Fin r → Fin n) (hc : Function.Injective cols)
    (U K : Set (Fin n → ℝ)) (C : ℝ≥0)
    (hf : AntilipschitzWith C (U.restrict (selectedGradientCoordinates F rows cols)))
    (hKU : K ⊆ U) (B : ℝ) (hB : 1 ≤ B)
    (hK : ∀ x ∈ K, ∀ i, |x i| ≤ B) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (w : Complement cols → ℝ) (b : Fin r → ℝ) (δ : ℝ),
      0 ≤ δ → (volume (sliceFiber F rows cols hc K w b δ)).toReal ≤ A*min 1 (δ^r) := by
  obtain ⟨A,hA,hbound⟩ := exists_bounded_bound F rows cols hc U K C hf hKU B hB hK
  refine ⟨A,hA,?_⟩
  intro w b δ hδ
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbound w b δ hδ)
  simpa only [ENNReal.toReal_ofReal (mul_nonneg (zero_le_one.trans hA)
    (le_min zero_le_one (pow_nonneg hδ r)))] using h

end CubicTenVariables.SelectedGradientSliceVolume
