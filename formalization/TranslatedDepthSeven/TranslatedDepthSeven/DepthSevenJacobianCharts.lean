import TranslatedDepthSeven.EquationFamilyTangentBaseChange
import TranslatedDepthSeven.JacobianMinorStandardSmoothChart
import TranslatedDepthSeven.MinimalComponentIsolation
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Finite depth-seven Jacobian charts

Let `equations` be a literal finite family of polynomials in `N` variables.
This file defines its rank-at-most-six locus by the simultaneous vanishing of
all displayed `7 × 7` Jacobian minors.  Away from this locus, seven actual
members of the family and seven actual coordinate columns have a nonzero
minor.  The possible choices form a finite type.

The final two statements isolate exactly the commutative-algebra input needed
to turn such a choice into a chart of a fixed height-seven prime component.
If the selected seven-equation ideal has height at least seven, Krull height
comparison makes that prime a minimal component, and the standard finite
minimal-prime argument supplies one separator depending only on the selected
equations, not on a point where the minor is nonzero.

No smooth-locus, component, or rank predicate is left implicit: the only
rank condition below is simultaneous vanishing or nonvanishing of the
displayed determinants.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

set_option maxRecDepth 2000

universe u

variable {k : Type u} [Field k]

/-- The evaluated Jacobian row belonging to one member of a finite equation
family. -/
def finiteEquationJacobianRowAt {N : ℕ}
    (equations : Finset (MvPolynomial (Fin N) k)) (z : Fin N → k)
    (f : {f // f ∈ equations}) : Fin N → k :=
  fun j ↦ MvPolynomial.aeval z (MvPolynomial.pderiv j f.1)

/-- A literal square Jacobian matrix, before evaluation. -/
def finiteEquationJacobianMinorMatrix {N r : ℕ}
    (equations : Finset (MvPolynomial (Fin N) k))
    (rows : Fin r → {f // f ∈ equations}) (cols : Fin r → Fin N) :
    Matrix (Fin r) (Fin r) (MvPolynomial (Fin N) k) :=
  Matrix.of fun i j ↦
    MvPolynomial.pderiv (cols j) (rows i).1

/-- A literal square Jacobian minor, before evaluation.  Repetitions in
`rows` or `cols` are allowed; the corresponding determinant is then zero. -/
def finiteEquationJacobianMinor {N r : ℕ}
    (equations : Finset (MvPolynomial (Fin N) k))
    (rows : Fin r → {f // f ∈ equations}) (cols : Fin r → Fin N) :
    MvPolynomial (Fin N) k :=
  (finiteEquationJacobianMinorMatrix equations rows cols).det

/-- The same displayed determinant after applying evaluation entrywise. -/
def finiteEquationJacobianMinorAt {N r : ℕ}
    (equations : Finset (MvPolynomial (Fin N) k)) (z : Fin N → k)
    (rows : Fin r → {f // f ∈ equations}) (cols : Fin r → Fin N) : k :=
  ((MvPolynomial.aeval z).mapMatrix
    (finiteEquationJacobianMinorMatrix equations rows cols)).det

/-- Evaluation commutes with formation of the displayed Jacobian
determinant. -/
theorem aeval_finiteEquationJacobianMinor {N r : ℕ}
    (equations : Finset (MvPolynomial (Fin N) k)) (z : Fin N → k)
    (rows : Fin r → {f // f ∈ equations}) (cols : Fin r → Fin N) :
    MvPolynomial.aeval z (finiteEquationJacobianMinor equations rows cols) =
      finiteEquationJacobianMinorAt equations z rows cols := by
  exact (MvPolynomial.aeval z).map_det
    (finiteEquationJacobianMinorMatrix equations rows cols)

/-- If the Jacobian row span has dimension below `r`, every displayed
`r × r` minor vanishes after evaluation. -/
theorem aeval_finiteEquationJacobianMinor_eq_zero_of_finrank_lt {N r : ℕ}
    (equations : Finset (MvPolynomial (Fin N) k)) (z : Fin N → k)
    (h : Module.finrank k
      (Submodule.span k
        (Set.range (finiteEquationJacobianRowAt equations z))) < r)
    (rows : Fin r → {f // f ∈ equations}) (cols : Fin r → Fin N) :
    MvPolynomial.aeval z (finiteEquationJacobianMinor equations rows cols) = 0 := by
  rw [aeval_finiteEquationJacobianMinor]
  change Matrix.det (Matrix.of fun i j ↦
    finiteEquationJacobianRowAt equations z (rows i) (cols j)) = 0
  apply TangentBaseChange.selectedMinor_eq_zero_of_rank_lt
    (A := Matrix.of fun f j ↦ finiteEquationJacobianRowAt equations z f j)
  rw [Matrix.rank_eq_finrank_span_row]
  have hrow :
      (Matrix.of fun f j ↦ finiteEquationJacobianRowAt equations z f j).row =
        finiteEquationJacobianRowAt equations z := by
    rfl
  rwa [hrow]

/-- If all displayed `r × r` polynomial minors vanish at a point, its
Jacobian row span has dimension below `r`. -/
theorem finrank_lt_of_all_aeval_finiteEquationJacobianMinor_eq_zero {N r : ℕ}
    (equations : Finset (MvPolynomial (Fin N) k)) (z : Fin N → k)
    (h : ∀ (rows : Fin r → {f // f ∈ equations}) (cols : Fin r → Fin N),
      MvPolynomial.aeval z
        (finiteEquationJacobianMinor equations rows cols) = 0) :
    Module.finrank k
      (Submodule.span k
        (Set.range (finiteEquationJacobianRowAt equations z))) < r := by
  apply TangentBaseChange.finrank_span_lt_of_all_minors_zero
  intro rows cols
  change finiteEquationJacobianMinorAt equations z rows cols = 0
  exact (aeval_finiteEquationJacobianMinor equations z rows cols).symm.trans
    (h rows cols)

/-- A row-span lower bound selects actual equation rows and coordinate
columns with a nonzero evaluated polynomial minor. -/
theorem exists_aeval_finiteEquationJacobianMinor_ne_zero_of_finrank_ge
    {N r : ℕ} (equations : Finset (MvPolynomial (Fin N) k)) (z : Fin N → k)
    (h : r ≤ Module.finrank k
      (Submodule.span k
        (Set.range (finiteEquationJacobianRowAt equations z)))) :
    ∃ rows : Fin r → {f // f ∈ equations}, ∃ cols : Fin r → Fin N,
      Function.Injective rows ∧ Function.Injective cols ∧
      MvPolynomial.aeval z
        (finiteEquationJacobianMinor equations rows cols) ≠ 0 := by
  obtain ⟨rows, cols, hrows, hcols, hdet⟩ :=
    TangentBaseChange.exists_nonzero_minor_of_finrank_span_ge
      (finiteEquationJacobianRowAt equations z) h
  refine ⟨rows, cols, hrows, hcols, ?_⟩
  intro hzero
  apply hdet
  change finiteEquationJacobianMinorAt equations z rows cols = 0
  exact (aeval_finiteEquationJacobianMinor equations z rows cols).symm.trans hzero

/-- The complementary rank locus, defined classically by all `7 × 7`
minors rather than by an abstract rank condition. -/
def IsDepthSevenJacobianRankAtMostSix {N : ℕ}
    (equations : Finset (MvPolynomial (Fin N) k)) (z : Fin N → k) : Prop :=
  ∀ (rows : Fin 7 → {f // f ∈ equations}) (cols : Fin 7 → Fin N),
    MvPolynomial.aeval z (finiteEquationJacobianMinor equations rows cols) = 0

/-- The all-minors definition is equivalent to the expected row-span
dimension bound. -/
theorem isDepthSevenJacobianRankAtMostSix_iff_finrank_le {N : ℕ}
    (equations : Finset (MvPolynomial (Fin N) k)) (z : Fin N → k) :
    IsDepthSevenJacobianRankAtMostSix equations z ↔
      Module.finrank k
        (Submodule.span k
          (Set.range (finiteEquationJacobianRowAt equations z))) ≤ 6 := by
  constructor
  · intro h
    have hlt :=
      finrank_lt_of_all_aeval_finiteEquationJacobianMinor_eq_zero
        equations z h
    omega
  · intro h rows cols
    apply aeval_finiteEquationJacobianMinor_eq_zero_of_finrank_lt
    omega

/-- A depth-seven chart is a choice of seven distinct displayed equations
and seven distinct coordinate columns.  Since the equation family and the
coordinate set are finite, so is the set of all such choices. -/
structure DepthSevenJacobianChartIndex {N : ℕ}
    (equations : Finset (MvPolynomial (Fin N) k)) where
  rows : Fin 7 → {f // f ∈ equations}
  cols : Fin 7 → Fin N
  rows_injective : Function.Injective rows
  cols_injective : Function.Injective cols

instance {N : ℕ} (equations : Finset (MvPolynomial (Fin N) k)) :
    Finite (DepthSevenJacobianChartIndex equations) := by
  let ι : DepthSevenJacobianChartIndex equations →
      (Fin 7 → {f // f ∈ equations}) × (Fin 7 → Fin N) :=
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

noncomputable instance {N : ℕ}
    (equations : Finset (MvPolynomial (Fin N) k)) :
    Fintype (DepthSevenJacobianChartIndex equations) :=
  Fintype.ofFinite _

/-- The seven actual equations attached to a chart. -/
def DepthSevenJacobianChartIndex.equations {N : ℕ}
    {equations : Finset (MvPolynomial (Fin N) k)}
    (C : DepthSevenJacobianChartIndex equations) :
    Fin 7 → MvPolynomial (Fin N) k :=
  fun i ↦ (C.rows i).1

/-- The ideal generated by the seven actual equations of a chart. -/
def DepthSevenJacobianChartIndex.ideal {N : ℕ}
    {equations : Finset (MvPolynomial (Fin N) k)}
    (C : DepthSevenJacobianChartIndex equations) :
    Ideal (MvPolynomial (Fin N) k) :=
  Ideal.span (Set.range C.equations)

/-- The fixed determinant polynomial attached to a chart. -/
def DepthSevenJacobianChartIndex.determinant {N : ℕ}
    {equations : Finset (MvPolynomial (Fin N) k)}
    (C : DepthSevenJacobianChartIndex equations) :
    MvPolynomial (Fin N) k :=
  finiteEquationJacobianMinor equations C.rows C.cols

/-- Every point outside the explicitly defined rank-at-most-six locus lies
in one of the finitely many determinant principal opens. -/
theorem exists_depthSevenJacobianChartIndex_of_not_rankAtMostSix {N : ℕ}
    (equations : Finset (MvPolynomial (Fin N) k)) (z : Fin N → k)
    (hz : ¬ IsDepthSevenJacobianRankAtMostSix equations z) :
    ∃ C : DepthSevenJacobianChartIndex equations,
      MvPolynomial.aeval z C.determinant ≠ 0 := by
  have hlarge : 7 ≤ Module.finrank k
      (Submodule.span k
        (Set.range (finiteEquationJacobianRowAt equations z))) := by
    rw [isDepthSevenJacobianRankAtMostSix_iff_finrank_le] at hz
    omega
  obtain ⟨rows, cols, hrows, hcols, hdet⟩ :=
    exists_aeval_finiteEquationJacobianMinor_ne_zero_of_finrank_ge
      equations z hlarge
  let C : DepthSevenJacobianChartIndex equations :=
    ⟨rows, cols, hrows, hcols⟩
  refine ⟨C, ?_⟩
  exact hdet

/-- If the whole displayed family generates an ideal `P`, each selected
seven-equation chart ideal is contained in `P`. -/
theorem DepthSevenJacobianChartIndex.ideal_le_of_span_eq {N : ℕ}
    {equations : Finset (MvPolynomial (Fin N) k)}
    (C : DepthSevenJacobianChartIndex equations)
    (P : Ideal (MvPolynomial (Fin N) k))
    (hP : Ideal.span (equations : Set (MvPolynomial (Fin N) k)) = P) :
    C.ideal ≤ P := by
  rw [← hP]
  apply Ideal.span_mono
  rintro f ⟨i, rfl⟩
  exact (C.rows i).2

/-- Height comparison turns a selected depth-seven complete-intersection
ideal into the fixed height-seven prime component.  The lower bound on the
selected ideal is stated literally because it is the exact missing
Jacobian-height implication in the current Mathlib API. -/
theorem DepthSevenJacobianChartIndex.mem_minimalPrimes_of_height_lower_bound
    {N : ℕ} {equations : Finset (MvPolynomial (Fin N) k)}
    (C : DepthSevenJacobianChartIndex equations)
    (P : Ideal (MvPolynomial (Fin N) k)) [P.IsPrime]
    (hP : Ideal.span (equations : Set (MvPolynomial (Fin N) k)) = P)
    (hPheight : P.height = 7) (hheight : 7 ≤ C.ideal.height) :
    P ∈ C.ideal.minimalPrimes := by
  letI : P.FiniteHeight := ⟨Or.inr (by simp [hPheight])⟩
  apply Ideal.mem_minimalPrimes_of_height_eq (C.ideal_le_of_span_eq P hP)
  simpa [hPheight] using hheight

/-- Once the literal height comparison is available, a single polynomial
chosen from the finite minimal-prime list isolates the selected component.
It depends only on `C` and `P`, never on the point used to detect the
nonzero Jacobian minor. -/
theorem DepthSevenJacobianChartIndex.exists_fixed_component_separator
    {N : ℕ} {equations : Finset (MvPolynomial (Fin N) k)}
    (C : DepthSevenJacobianChartIndex equations)
    (P : Ideal (MvPolynomial (Fin N) k)) [P.IsPrime]
    (hP : Ideal.span (equations : Set (MvPolynomial (Fin N) k)) = P)
    (hPheight : P.height = 7) (hheight : 7 ≤ C.ideal.height) :
    ∃ u : MvPolynomial (Fin N) k, u ∉ P ∧
      ∀ f ∈ P, u * f ∈ C.ideal.radical := by
  exact exists_minimalComponent_separator C.ideal P
    (C.mem_minimalPrimes_of_height_lower_bound P hP hPheight hheight)

end

end TranslatedDepthSeven
