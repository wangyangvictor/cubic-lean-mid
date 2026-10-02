import TranslatedDepthSeven.DepthSevenJacobianCharts
import TranslatedDepthSeven.DepthSevenOccupiedTangentPackets
import TranslatedDepthSeven.FiniteFirstOccurrence

/-!
# The literal normalized depth-seven Jacobian partition

For a finite integral equation family in thirteen variables, the
rank-at-most-six locus is cut out by the original equations together with
all of their `7 × 7` Jacobian minors.  Applying the literal affine
substitution `x = x₀ + m z` gives a finite equation family in the normalized
variable `z` defining exactly the corresponding part of the normalized
point set.

The complementary points are assigned one of the finitely many choices of
seven actual equation rows and seven actual coordinate columns on which the
minor is nonzero.  The assignment below is a static choice function.  Its
fibres, together with the rank-at-most-six locus, are an honest finite
partition; no dimensional claim about the rank-at-most-six locus is made.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

set_option maxRecDepth 2000

/-- The polynomial matrix whose evaluation is the selected integral
Jacobian submatrix. -/
def integralJacobianMinorPolynomialMatrix {c N r : ℕ}
    (F : Fin c → MvPolynomial (Fin N) ℤ)
    (rows : Fin r → Fin c) (cols : Fin r → Fin N) :
    Matrix (Fin r) (Fin r) (MvPolynomial (Fin N) ℤ) :=
  Matrix.of fun i j ↦ MvPolynomial.pderiv (cols j) (F (rows i))

/-- A selected integral Jacobian minor as a literal polynomial. -/
def integralJacobianMinorPolynomial {c N r : ℕ}
    (F : Fin c → MvPolynomial (Fin N) ℤ)
    (rows : Fin r → Fin c) (cols : Fin r → Fin N) :
    MvPolynomial (Fin N) ℤ :=
  (integralJacobianMinorPolynomialMatrix F rows cols).det

/-- Evaluating the polynomial minor gives the previously defined numerical
integral Jacobian minor. -/
theorem eval_integralJacobianMinorPolynomial {c N r : ℕ}
    (F : Fin c → MvPolynomial (Fin N) ℤ) (x : IntVector N)
    (rows : Fin r → Fin c) (cols : Fin r → Fin N) :
    MvPolynomial.eval x (integralJacobianMinorPolynomial F rows cols) =
      integralJacobianMinor F x rows cols := by
  let M := integralJacobianMinorPolynomialMatrix F rows cols
  have hmap := (MvPolynomial.aeval x).map_det M
  change MvPolynomial.aeval x M.det =
    ((integralJacobianMatrix F x).submatrix rows cols).det
  calc
    MvPolynomial.aeval x M.det =
        ((MvPolynomial.aeval x).mapMatrix M).det := hmap
    _ = ((integralJacobianMatrix F x).submatrix rows cols).det := by
      congr 1

/-- A nonzero integral `r × r` Jacobian minor forces rational Jacobian
rank at least `r`. -/
theorem rationalJacobian_rank_ge_of_integralMinor_ne_zero {c N r : ℕ}
    (F : Fin c → MvPolynomial (Fin N) ℤ) (x : IntVector N)
    (rows : Fin r → Fin c) (cols : Fin r → Fin N)
    (hminor : integralJacobianMinor F x rows cols ≠ 0) :
    r ≤ ((integralJacobianMatrix F x).map (Int.castRingHom ℚ)).rank := by
  apply rank_ge_card_of_submatrix_det_ne_zero
    ((integralJacobianMatrix F x).map (Int.castRingHom ℚ)) rows cols
  have hcast : ((integralJacobianMinor F x rows cols : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast hminor
  change (((integralJacobianMatrix F x).map (Int.castRingHom ℚ)).submatrix
    rows cols).det ≠ 0
  rw [Matrix.submatrix_map]
  change ((Int.castRingHom ℚ).mapMatrix
    ((integralJacobianMatrix F x).submatrix rows cols)).det ≠ 0
  rw [← (Int.castRingHom ℚ).map_det]
  exact hcast

/-- The finite family of every displayed `7 × 7` integral Jacobian minor.
Repeated rows or columns are harmless and simply contribute the zero
polynomial. -/
def depthSevenIntegralJacobianMinorFinset
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) :
    Finset (MvPolynomial (Fin 13) ℤ) := by
  classical
  exact Finset.univ.image fun rc :
      (Fin 7 → Fin equations.card) × (Fin 7 → Fin 13) ↦
    integralJacobianMinorPolynomial
      (indexedFinsetFamily equations) rc.1 rc.2

@[simp]
theorem mem_depthSevenIntegralJacobianMinorFinset_iff
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (g : MvPolynomial (Fin 13) ℤ) :
    g ∈ depthSevenIntegralJacobianMinorFinset equations ↔
      ∃ (rows : Fin 7 → Fin equations.card) (cols : Fin 7 → Fin 13),
        integralJacobianMinorPolynomial
          (indexedFinsetFamily equations) rows cols = g := by
  classical
  constructor
  · intro hg
    obtain ⟨rc, _hrc, hrc⟩ := Finset.mem_image.mp hg
    exact ⟨rc.1, rc.2, hrc⟩
  · rintro ⟨rows, cols, rfl⟩
    exact Finset.mem_image.mpr ⟨(rows, cols), Finset.mem_univ _, rfl⟩

/-- The original equations augmented by every `7 × 7` Jacobian minor.
This is the promised explicit equation family for the rank-at-most-six
locus. -/
def depthSevenRankAtMostSixEquationFinset
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) :
    Finset (MvPolynomial (Fin 13) ℤ) :=
  equations ∪ depthSevenIntegralJacobianMinorFinset equations

/-- Simultaneous vanishing of all polynomial minors is exactly failure of
the literal rational rank-seven condition. -/
theorem all_depthSevenIntegralJacobianMinors_zero_iff_not_regular
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (x : IntVector 13) :
    (∀ (rows : Fin 7 → Fin equations.card) (cols : Fin 7 → Fin 13),
      MvPolynomial.eval x
        (integralJacobianMinorPolynomial
          (indexedFinsetFamily equations) rows cols) = 0) ↔
      ¬ IsDepthSevenJacobianRegularAt equations x := by
  constructor
  · intro hall hregular
    obtain ⟨rows, cols, _hrows, _hcols, hminor⟩ :=
      exists_nonzero_integralJacobianMinor_of_rank_ge
        (indexedFinsetFamily equations) x hregular
    apply hminor
    rw [← eval_integralJacobianMinorPolynomial]
    exact hall rows cols
  · intro hnot rows cols
    rw [eval_integralJacobianMinorPolynomial]
    by_contra hminor
    exact hnot (rationalJacobian_rank_ge_of_integralMinor_ne_zero
      (indexedFinsetFamily equations) x rows cols hminor)

/-- The augmented finite family cuts out exactly the common zeros of the
original equations whose rational Jacobian rank is at most six. -/
theorem integralCommonZero_depthSevenRankAtMostSixEquationFinset_iff
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (x : IntVector 13) :
    IntegralCommonZero (depthSevenRankAtMostSixEquationFinset equations) x ↔
      IntegralCommonZero equations x ∧
        ¬ IsDepthSevenJacobianRegularAt equations x := by
  constructor
  · intro hx
    have hequations : IntegralCommonZero equations x := by
      intro f hf
      exact hx f (Finset.mem_union_left _ hf)
    refine ⟨hequations,
      (all_depthSevenIntegralJacobianMinors_zero_iff_not_regular
        equations x).mp ?_⟩
    intro rows cols
    apply hx
    apply Finset.mem_union_right equations
    exact (mem_depthSevenIntegralJacobianMinorFinset_iff equations _).mpr
      ⟨rows, cols, rfl⟩
  · rintro ⟨hequations, hrank⟩ f hf
    rcases Finset.mem_union.mp hf with hf | hf
    · exact hequations f hf
    · obtain ⟨rows, cols, rfl⟩ :=
        (mem_depthSevenIntegralJacobianMinorFinset_iff equations f).mp hf
      exact (all_depthSevenIntegralJacobianMinors_zero_iff_not_regular
        equations x).mpr hrank rows cols

/-- The preceding equation family after the exact affine substitution
`x = x₀ + m z`. -/
def normalizedDepthSevenRankAtMostSixEquationFinset
    (x₀ : IntVector 13) (m : ℕ)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) :
    Finset (MvPolynomial (Fin 13) ℤ) := by
  classical
  exact (depthSevenRankAtMostSixEquationFinset equations).image
    (integralAffineTransform x₀ m)

/-- The transformed family has exactly the expected normalized common-zero
set. -/
theorem integralCommonZero_normalizedDepthSevenRankAtMostSixEquationFinset_iff
    (x₀ z : IntVector 13) (m : ℕ)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) :
    IntegralCommonZero
        (normalizedDepthSevenRankAtMostSixEquationFinset x₀ m equations) z ↔
      IntegralCommonZero (depthSevenRankAtMostSixEquationFinset equations)
        (integralAffineMap x₀ z m) := by
  classical
  constructor
  · intro hz f hf
    have hmem : integralAffineTransform x₀ m f ∈
        normalizedDepthSevenRankAtMostSixEquationFinset x₀ m equations :=
      Finset.mem_image.mpr ⟨f, hf, rfl⟩
    rw [← eval_integralAffineTransform]
    exact hz _ hmem
  · intro hx g hg
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
    rw [eval_integralAffineTransform]
    exact hx f hf

/-- A finite chart is a choice of seven distinct rows of the fixed indexed
equation family and seven distinct coordinate columns. -/
structure IntegralDepthSevenJacobianChartIndex
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) where
  rows : Fin 7 → Fin equations.card
  cols : Fin 7 → Fin 13
  rows_injective : Function.Injective rows
  cols_injective : Function.Injective cols

instance (equations : Finset (MvPolynomial (Fin 13) ℤ)) :
    Finite (IntegralDepthSevenJacobianChartIndex equations) := by
  let ι : IntegralDepthSevenJacobianChartIndex equations →
      (Fin 7 → Fin equations.card) × (Fin 7 → Fin 13) :=
    fun C ↦ (C.rows, C.cols)
  exact Finite.of_injective ι (by
    intro C D h
    rcases C with ⟨rows, cols, hrows, hcols⟩
    rcases D with ⟨rows', cols', hrows', hcols'⟩
    change (rows, cols) = (rows', cols') at h
    injection h with hrow hcol
    subst rows'
    subst cols'
    rfl)

noncomputable instance
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) :
    Fintype (IntegralDepthSevenJacobianChartIndex equations) :=
  Fintype.ofFinite _

/-- The fixed polynomial minor attached to an integral chart. -/
def IntegralDepthSevenJacobianChartIndex.determinant
    {equations : Finset (MvPolynomial (Fin 13) ℤ)}
    (C : IntegralDepthSevenJacobianChartIndex equations) :
    MvPolynomial (Fin 13) ℤ :=
  integralJacobianMinorPolynomial
    (indexedFinsetFamily equations) C.rows C.cols

/-- Every literal rank-seven integral point belongs to at least one of the
finitely many determinant principal opens. -/
theorem exists_integralDepthSevenJacobianChartIndex_of_regular
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (x : IntVector 13) (hx : IsDepthSevenJacobianRegularAt equations x) :
    ∃ C : IntegralDepthSevenJacobianChartIndex equations,
      MvPolynomial.eval x C.determinant ≠ 0 := by
  obtain ⟨rows, cols, hrows, hcols, hminor⟩ :=
    exists_nonzero_integralJacobianMinor_of_rank_ge
      (indexedFinsetFamily equations) x hx
  refine ⟨⟨rows, cols, hrows, hcols⟩, ?_⟩
  rw [IntegralDepthSevenJacobianChartIndex.determinant,
    eval_integralJacobianMinorPolynomial]
  exact hminor

/-- A static choice of one nonzero chart at a rank-seven point. -/
def selectedIntegralDepthSevenJacobianChart
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (x : IntVector 13) (hx : IsDepthSevenJacobianRegularAt equations x) :
    IntegralDepthSevenJacobianChartIndex equations :=
  Classical.choose
    (exists_integralDepthSevenJacobianChartIndex_of_regular equations x hx)

theorem eval_selectedIntegralDepthSevenJacobianChart_determinant_ne_zero
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (x : IntVector 13) (hx : IsDepthSevenJacobianRegularAt equations x) :
    MvPolynomial.eval x
      (selectedIntegralDepthSevenJacobianChart equations x hx).determinant ≠ 0 :=
  Classical.choose_spec
    (exists_integralDepthSevenJacobianChartIndex_of_regular equations x hx)

/-- The finite normalized subset on the explicit rank-at-most-six equation
family. -/
def depthSevenNormalizedRankAtMostSixFinset
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ) :
    Finset (IntVector 13) := by
  classical
  exact (depthSevenNormalizedDisplacementFinset p x₀ equations CF).filter
    fun z ↦ IntegralCommonZero
      (normalizedDepthSevenRankAtMostSixEquationFinset x₀ p.m equations) z

@[simp]
theorem mem_depthSevenNormalizedRankAtMostSixFinset_iff
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (z : IntVector 13) :
    z ∈ depthSevenNormalizedRankAtMostSixFinset p x₀ equations CF ↔
      z ∈ depthSevenNormalizedDisplacementFinset p x₀ equations CF ∧
      ¬ IsDepthSevenJacobianRegularAt equations
        (integralAffineMap x₀ z p.m) := by
  classical
  rw [depthSevenNormalizedRankAtMostSixFinset, Finset.mem_filter,
    integralCommonZero_normalizedDepthSevenRankAtMostSixEquationFinset_iff,
    integralCommonZero_depthSevenRankAtMostSixEquationFinset_iff]
  constructor
  · rintro ⟨hz, _hzero, hrank⟩
    exact ⟨hz, hrank⟩
  · rintro ⟨hz, hrank⟩
    exact ⟨hz, depthSevenNormalized_integralCommonZero
      p x₀ equations CF hz, hrank⟩

/-- The point label is `none` on the explicit rank-at-most-six locus and is
one selected nonzero chart on its complement. -/
def normalizedDepthSevenJacobianChartLabel
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (z : IntVector 13) :
    Option (IntegralDepthSevenJacobianChartIndex equations) := by
  classical
  exact if h : IsDepthSevenJacobianRegularAt equations
        (integralAffineMap x₀ z p.m) then
      some (selectedIntegralDepthSevenJacobianChart equations
        (integralAffineMap x₀ z p.m) h)
    else none

@[simp]
theorem normalizedDepthSevenJacobianChartLabel_eq_none_iff
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (z : IntVector 13) :
    normalizedDepthSevenJacobianChartLabel p x₀ equations z = none ↔
      ¬ IsDepthSevenJacobianRegularAt equations
        (integralAffineMap x₀ z p.m) := by
  simp [normalizedDepthSevenJacobianChartLabel]

/-- A chart cell is a literal fibre of the static chart label inside the
normalized point set. -/
def depthSevenNormalizedJacobianChartCell
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations) :
    Finset (IntVector 13) := by
  classical
  exact (depthSevenNormalizedDisplacementFinset p x₀ equations CF).filter
    fun z ↦ normalizedDepthSevenJacobianChartLabel p x₀ equations z = some C

@[simp]
theorem mem_depthSevenNormalizedJacobianChartCell_iff
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (z : IntVector 13) :
    z ∈ depthSevenNormalizedJacobianChartCell p x₀ equations CF C ↔
      z ∈ depthSevenNormalizedDisplacementFinset p x₀ equations CF ∧
      normalizedDepthSevenJacobianChartLabel p x₀ equations z = some C := by
  classical
  simp [depthSevenNormalizedJacobianChartCell]

/-- Every point assigned to a chart lies on that chart's nonzero determinant
principal open. -/
theorem eval_chart_determinant_ne_zero_of_mem_normalizedChartCell
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    {z : IntVector 13}
    (hz : z ∈ depthSevenNormalizedJacobianChartCell p x₀ equations CF C) :
    MvPolynomial.eval (integralAffineMap x₀ z p.m) C.determinant ≠ 0 := by
  have hlabel :=
    (mem_depthSevenNormalizedJacobianChartCell_iff
      p x₀ equations CF C z).mp hz |>.2
  unfold normalizedDepthSevenJacobianChartLabel at hlabel
  split at hlabel
  next hregular =>
    simp only [Option.some.injEq] at hlabel
    subst C
    exact eval_selectedIntegralDepthSevenJacobianChart_determinant_ne_zero
      equations (integralAffineMap x₀ z p.m) hregular
  next hnot => simp at hlabel

/-- Each normalized point is either on the explicit rank-at-most-six locus,
or belongs to exactly one selected rank-seven chart cell. -/
theorem mem_rankAtMostSix_or_existsUnique_normalizedJacobianChartCell
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {z : IntVector 13}
    (hz : z ∈ depthSevenNormalizedDisplacementFinset p x₀ equations CF) :
    z ∈ depthSevenNormalizedRankAtMostSixFinset p x₀ equations CF ∨
      ∃! C : IntegralDepthSevenJacobianChartIndex equations,
        z ∈ depthSevenNormalizedJacobianChartCell p x₀ equations CF C := by
  by_cases hregular : IsDepthSevenJacobianRegularAt equations
      (integralAffineMap x₀ z p.m)
  · right
    let C := selectedIntegralDepthSevenJacobianChart equations
      (integralAffineMap x₀ z p.m) hregular
    refine ⟨C, ?_, ?_⟩
    · apply (mem_depthSevenNormalizedJacobianChartCell_iff
        p x₀ equations CF C z).mpr
      refine ⟨hz, ?_⟩
      simp [normalizedDepthSevenJacobianChartLabel, hregular, C]
    · intro D hD
      have hC := (mem_depthSevenNormalizedJacobianChartCell_iff
        p x₀ equations CF C z).mp
        ((mem_depthSevenNormalizedJacobianChartCell_iff
          p x₀ equations CF C z).mpr ⟨hz, by
            simp [normalizedDepthSevenJacobianChartLabel, hregular, C]⟩) |>.2
      have hDlabel := (mem_depthSevenNormalizedJacobianChartCell_iff
        p x₀ equations CF D z).mp hD |>.2
      exact Option.some.inj (hDlabel.symm.trans hC)
  · left
    exact (mem_depthSevenNormalizedRankAtMostSixFinset_iff
      p x₀ equations CF z).mpr ⟨hz, hregular⟩

/-- The rank-at-most-six cell is disjoint from every selected rank-seven
chart cell. -/
theorem depthSevenNormalizedRankAtMostSix_disjoint_jacobianChartCell
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations) :
    Disjoint
      (depthSevenNormalizedRankAtMostSixFinset p x₀ equations CF)
      (depthSevenNormalizedJacobianChartCell p x₀ equations CF C) := by
  classical
  rw [Finset.disjoint_left]
  intro z hzrank hzchart
  have hnone : normalizedDepthSevenJacobianChartLabel p x₀ equations z = none :=
    (normalizedDepthSevenJacobianChartLabel_eq_none_iff
      p x₀ equations z).mpr
      ((mem_depthSevenNormalizedRankAtMostSixFinset_iff
        p x₀ equations CF z).mp hzrank).2
  have hsome : normalizedDepthSevenJacobianChartLabel p x₀ equations z = some C :=
    ((mem_depthSevenNormalizedJacobianChartCell_iff
      p x₀ equations CF C z).mp hzchart).2
  rw [hnone] at hsome
  simp at hsome

/-- Distinct chart-label fibres are disjoint. -/
theorem depthSevenNormalizedJacobianChartCell_disjoint
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {C D : IntegralDepthSevenJacobianChartIndex equations} (hCD : C ≠ D) :
    Disjoint
      (depthSevenNormalizedJacobianChartCell p x₀ equations CF C)
      (depthSevenNormalizedJacobianChartCell p x₀ equations CF D) := by
  classical
  rw [Finset.disjoint_left]
  intro z hzC hzD
  have hC := ((mem_depthSevenNormalizedJacobianChartCell_iff
    p x₀ equations CF C z).mp hzC).2
  have hD := ((mem_depthSevenNormalizedJacobianChartCell_iff
    p x₀ equations CF D z).mp hzD).2
  exact hCD (Option.some.inj (hC.symm.trans hD))

/-- The normalized point set is literally the union of the explicit
rank-at-most-six cell and the finitely many selected rank-seven chart
cells. -/
theorem depthSevenNormalizedDisplacementFinset_eq_rankAtMostSix_union_chartCells
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ) :
    depthSevenNormalizedDisplacementFinset p x₀ equations CF =
      depthSevenNormalizedRankAtMostSixFinset p x₀ equations CF ∪
        Finset.univ.biUnion
          (depthSevenNormalizedJacobianChartCell p x₀ equations CF) := by
  classical
  ext z
  constructor
  · intro hz
    rcases mem_rankAtMostSix_or_existsUnique_normalizedJacobianChartCell
      p x₀ equations CF hz with hzrank | ⟨C, hzC, _hunique⟩
    · exact Finset.mem_union_left _ hzrank
    · exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨C, Finset.mem_univ C, hzC⟩)
  · intro hz
    rcases Finset.mem_union.mp hz with hzrank | hzchart
    · exact ((mem_depthSevenNormalizedRankAtMostSixFinset_iff
        p x₀ equations CF z).mp hzrank).1
    · obtain ⟨C, _hC, hzC⟩ := Finset.mem_biUnion.mp hzchart
      exact ((mem_depthSevenNormalizedJacobianChartCell_iff
        p x₀ equations CF C z).mp hzC).1

/-- Exact cardinality form of the finite disjoint partition. -/
theorem card_depthSevenNormalizedDisplacementFinset_eq_rankAtMostSix_add_chartCells
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ) :
    (depthSevenNormalizedDisplacementFinset p x₀ equations CF).card =
      (depthSevenNormalizedRankAtMostSixFinset p x₀ equations CF).card +
        ∑ C : IntegralDepthSevenJacobianChartIndex equations,
          (depthSevenNormalizedJacobianChartCell
            p x₀ equations CF C).card := by
  classical
  let low := depthSevenNormalizedRankAtMostSixFinset p x₀ equations CF
  let cells := depthSevenNormalizedJacobianChartCell p x₀ equations CF
  let allCells := Finset.univ.biUnion cells
  have hlow : Disjoint low allCells := by
    rw [Finset.disjoint_biUnion_right]
    intro C _hC
    exact depthSevenNormalizedRankAtMostSix_disjoint_jacobianChartCell
      p x₀ equations CF C
  have hpairs : ((Finset.univ :
      Finset (IntegralDepthSevenJacobianChartIndex equations)) :
        Set (IntegralDepthSevenJacobianChartIndex equations)).PairwiseDisjoint cells := by
    intro C _hC D _hD hCD
    exact depthSevenNormalizedJacobianChartCell_disjoint
      p x₀ equations CF hCD
  have hallCard : allCells.card =
      ∑ C : IntegralDepthSevenJacobianChartIndex equations, (cells C).card := by
    simpa using Finset.card_biUnion hpairs
  calc
    (depthSevenNormalizedDisplacementFinset p x₀ equations CF).card =
        (low ∪ allCells).card := by
      congr 1
      exact depthSevenNormalizedDisplacementFinset_eq_rankAtMostSix_union_chartCells
        p x₀ equations CF
    _ = low.card + allCells.card := Finset.card_union_of_disjoint hlow
    _ = low.card + ∑ C : IntegralDepthSevenJacobianChartIndex equations,
          (cells C).card := by
      rw [hallCard]
    _ = _ := rfl

end

end TranslatedDepthSeven
