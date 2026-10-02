import CubicTenVariables.ExponentialSums
import CubicTenVariables.SymmetricPresentation
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Explicit literature statements about actual cubic singular series

The two propositions below are separate named arguments to the application
theorems, not global axioms. Davenport's proposition is now inhabited in
`CubicTenVariables.UnconditionalDavenport`; Bernert's remains an explicit
literature premise. The historical conditional adapters are retained here.

* `Bernert2025Theorem1`: C. Bernert, *The singular series of a cubic form in
  many variables and a new proof of Davenport's Shrinking Lemma*, Bull. London
  Math. Soc. 57 (2025), 681–691, Theorem 1, DOI 10.1112/blms.13221.
  The statement and its normalization were checked in arXiv:2310.02036,
  printed pp. 1–3. No irreducibility or nonsingularity premise occurs there.
* `DavenportGeometricDichotomy`: Theorem A on printed p. 2 of the same paper,
  explicitly attributed there to Davenport. Bernert's displayed statement
  was inspected; the original Davenport proof was not inspected for this
  module. This is a distinct literature assumption, not Bernert's Theorem 1.
  The original reference is H. Davenport, *Cubic forms in sixteen variables*,
  Proc. Roy. Soc. London Ser. A 272 (1963), 285–303.

The input cubic is literally the ordered-triple polynomial attached to a
symmetric integral tensor. The rank is that of Bernert's matrix M, over Q.
The counts, complete sums, absolute convergence and real positive series value
all refer to explicit mathematical objects. There is no rational-zero theorem
or counting asymptotic hidden in `Bernert2025Theorem1`.
-/

noncomputable section
namespace CubicTenVariables
namespace Literature
open MvPolynomial Filter
open scoped BigOperators Topology

/-- The Q-rank of the actual integral matrix M(x) in Bernert's definition. -/
def tensorMatrixRank {n : ℕ} (C : SymmetricIntegerCubicTensor n)
    (x : Fin n → ℤ) : ℕ :=
  (show Matrix (Fin n) (Fin n) ℚ from fun j k => (C.matrix x j k : ℚ)).rank

/-- The literal integer-vector count in Davenport's geometric condition. -/
def tensorRankCount {n : ℕ} (C : SymmetricIntegerCubicTensor n)
    (B r : ℕ) : ℕ := by
  classical
  exact ((integerBox n B).filter fun x => tensorMatrixRank C x = r).card

/-- Davenport's condition (1.2) for the tensor's actual matrix M(x).
The constants may depend on the fixed tensor, epsilon and rank. Positive
integer radii encode the equivalent real-radius condition by rounding down.
The paper's sufficiently-small-positive-epsilon convention implies the
displayed all-positive-epsilon version by monotonicity for B ≥ 1. -/
def TensorDavenportGood {n : ℕ} (C : SymmetricIntegerCubicTensor n) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ r : ℕ, r ≤ n →
    ∃ A : ℝ, 0 < A ∧ ∀ B : ℕ, 1 ≤ B →
      (tensorRankCount C B r : ℝ) ≤ A * (B : ℝ) ^ ((r : ℝ) + ε)

/-- The paper's small-epsilon convention gives precisely the same condition;
the extension to larger epsilon does not add a literature hypothesis. -/
theorem tensorDavenportGood_iff_small_epsilon {n : ℕ}
    (C : SymmetricIntegerCubicTensor n) (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    TensorDavenportGood C ↔
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ r : ℕ, r ≤ n →
        ∃ A : ℝ, 0 < A ∧ ∀ B : ℕ, 1 ≤ B →
          (tensorRankCount C B r : ℝ) ≤ A * (B : ℝ) ^ ((r : ℝ) + ε) := by
  constructor
  · intro h ε hε _ r hr
    exact h ε hε r hr
  · intro h ε hε r hr
    have hmin : 0 < min ε (ε₀ / 2) := lt_min hε (by positivity)
    have hlt : min ε (ε₀ / 2) < ε₀ :=
      lt_of_le_of_lt (min_le_right _ _) (by linarith)
    obtain ⟨A, hA, hb⟩ := h _ hmin hlt r hr
    refine ⟨A, hA, fun B hB => (hb B hB).trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ hA.le
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hB)
      (by linarith [min_le_left ε (ε₀ / 2)])

/-- Rounding a real radius down produces the same integer box and preserves
the power bound, so integer radii suffice for the real-radius formulation. -/
theorem tensorDavenportGood_iff_real_radii {n : ℕ}
    (C : SymmetricIntegerCubicTensor n) :
    TensorDavenportGood C ↔
      ∀ ε : ℝ, 0 < ε → ∀ r : ℕ, r ≤ n →
        ∃ A : ℝ, 0 < A ∧ ∀ P : ℝ, 1 ≤ P →
          (tensorRankCount C ⌊P⌋₊ r : ℝ) ≤ A * P ^ ((r : ℝ) + ε) := by
  constructor
  · intro h ε hε r hr
    obtain ⟨A, hA, hb⟩ := h ε hε r hr
    refine ⟨A, hA, fun P hP => ?_⟩
    have hfloor : 1 ≤ ⌊P⌋₊ := (Nat.le_floor_iff' (by decide)).mpr (by simpa)
    apply (hb _ hfloor).trans
    apply mul_le_mul_of_nonneg_left _ hA.le
    exact Real.rpow_le_rpow (by positivity) (Nat.floor_le (by linarith))
      (by positivity)
  · intro h ε hε r hr
    obtain ⟨A, hA, hp⟩ := h ε hε r hr
    refine ⟨A, hA, fun B hB => ?_⟩
    simpa only [Nat.floor_natCast] using hp (B : ℝ) (by exact_mod_cast hB)

/-- Strict positivity includes reality: the complex series equals an actual
strictly positive real number. This is stronger than merely positive real part. -/
def PositiveRealSingularSeries {n : ℕ} (F : MvPolynomial (Fin n) ℤ) : Prop :=
  ∃ S : ℝ, 0 < S ∧ singularSeries F = (S : ℂ)

/-- The precise independent literature input from Bernert's Theorem 1.
No proof or instance of this proposition is supplied here. -/
def Bernert2025Theorem1 : Prop :=
  ∀ (n : ℕ) (C : SymmetricIntegerCubicTensor n), 10 ≤ n →
    TensorDavenportGood C →
      SingularSeriesAbsolutelyConvergent C.polynomial ∧
        PositiveRealSingularSeries C.polynomial

/-- The separate classical dichotomy, quoted as Theorem A in Bernert.
It has no lower bound on n. The precise point count is exposed above. -/
def DavenportGeometricDichotomy : Prop :=
  ∀ (n : ℕ) (C : SymmetricIntegerCubicTensor n),
    ¬ TensorDavenportGood C → HasIntegerZero C.polynomial

/-- The actual geometric condition follows in the anisotropic branch,
conditional on the separately stated Davenport dichotomy. -/
theorem tensorDavenportGood_of_no_integer_zero
    (davenport : DavenportGeometricDichotomy) {n : ℕ}
    (C : SymmetricIntegerCubicTensor n) (hC : ¬ HasIntegerZero C.polynomial) :
    TensorDavenportGood C := by
  by_contra h
  exact hC (davenport n C h)

/-- A usable series conclusion in the no-integer-zero branch. Both literature
inputs remain explicit; the conclusion does not contradict that branch alone. -/
theorem bernert_of_no_integer_zero
    (davenport : DavenportGeometricDichotomy) (bernert : Bernert2025Theorem1)
    {n : ℕ} (C : SymmetricIntegerCubicTensor n) (hn : 10 ≤ n)
    (hC : ¬ HasIntegerZero C.polynomial) :
    SingularSeriesAbsolutelyConvergent C.polynomial ∧
      PositiveRealSingularSeries C.polynomial :=
  bernert n C hn (tensorDavenportGood_of_no_integer_zero davenport C hC)

/-- An elementary transport lemma: equality of the actual ranks identifies
the literal finite counts, not just their asymptotic exponents. -/
theorem tensorRankCount_eq_hessianRankCount {n : ℕ}
    (C : SymmetricIntegerCubicTensor n) (F : MvPolynomial (Fin n) ℤ)
    (h : ∀ x, tensorMatrixRank C x = integerHessianRank F x) (B r : ℕ) :
    tensorRankCount C B r = hessianRankCount F B r := by
  simp only [tensorRankCount, hessianRankCount, h]

theorem tensorDavenportGood_iff_davenportGood {n : ℕ}
    (C : SymmetricIntegerCubicTensor n) (F : MvPolynomial (Fin n) ℤ)
    (h : ∀ x, tensorMatrixRank C x = integerHessianRank F x) :
    TensorDavenportGood C ↔ DavenportGood F := by
  simp only [TensorDavenportGood, DavenportGood,
    tensorRankCount_eq_hessianRankCount C F h]

/-- For the canonical tensor representing 6F, Bernert's M is the Hessian of
F, so the two ranks agree exactly, including at exceptional points. -/
theorem canonicalTensor_rank_eq {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (x : Fin n → ℤ) :
    tensorMatrixRank (symmetricTensorOfCubic F) x = integerHessianRank F x := by
  unfold tensorMatrixRank integerHessianRank
  rw [symmetricTensorOfCubic_matrix_rat F hF x]

theorem canonicalTensor_good_iff {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) :
    TensorDavenportGood (symmetricTensorOfCubic F) ↔ DavenportGood F :=
  tensorDavenportGood_iff_davenportGood _ F (canonicalTensor_rank_eq F hF)

/-- The independent Davenport input gives the original cubic's Hessian
count condition; multiplying by six does not alter its nonzero zeros. -/
theorem davenportGood_of_no_integer_zero
    (davenport : DavenportGeometricDichotomy) {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hzero : ¬ HasIntegerZero F) : DavenportGood F := by
  apply (canonicalTensor_good_iff F hF).mp
  apply tensorDavenportGood_of_no_integer_zero davenport
  intro h
  exact hzero ((symmetricTensorOfCubic_hasIntegerZero_iff F hF).mp h)

/-- Bernert's actual series theorem applied to the integrally normalized 6F.
No assertion that the series of F and 6F coincide is made or required. -/
theorem bernert_six_mul (bernert : Bernert2025Theorem1) {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hn : 10 ≤ n) (hgood : DavenportGood F) :
    SingularSeriesAbsolutelyConvergent (C 6 * F) ∧
      PositiveRealSingularSeries (C 6 * F) := by
  have h := bernert n (symmetricTensorOfCubic F) hn
    ((canonicalTensor_good_iff F hF).mpr hgood)
  simpa only [symmetricTensorOfCubic_polynomial F hF] using h

/-- Absolute convergence supplies ordinary convergence of these complex terms. -/
theorem summable_singularSeriesTerm {n : ℕ} {F : MvPolynomial (Fin n) ℤ}
    (h : SingularSeriesAbsolutelyConvergent F) : Summable (singularSeriesTerm F) :=
  h.of_norm

/-- The artificial zero index contributes nothing: this is exactly the
series over q = 1,2,3,..., under the required convergence hypothesis. -/
theorem singularSeries_eq_tsum_positive {n : ℕ} {F : MvPolynomial (Fin n) ℤ}
    (h : SingularSeriesAbsolutelyConvergent F) :
    singularSeries F = ∑' q : ℕ+, singularSeriesTerm F q := by
  have hs := tsum_zero_pnat_eq_tsum_nat (summable_singularSeriesTerm h)
  simpa only [singularSeriesTerm_zero, zero_add, singularSeries] using hs.symm

/-- The corresponding explicit absolute convergence over positive moduli. -/
theorem summable_norm_singularSeriesTerm_positive {n : ℕ}
    {F : MvPolynomial (Fin n) ℤ} (h : SingularSeriesAbsolutelyConvergent F) :
    Summable (fun q : ℕ+ => ‖singularSeriesTerm F q‖) := by
  apply (summable_pnat_iff_summable_succ
    (f := fun q : ℕ => ‖singularSeriesTerm F q‖)).mpr
  exact (summable_nat_add_iff (f := fun q : ℕ => ‖singularSeriesTerm F q‖) 1).mpr h

theorem singularSeries_im_eq_zero {n : ℕ} {F : MvPolynomial (Fin n) ℤ}
    (h : PositiveRealSingularSeries F) : (singularSeries F).im = 0 := by
  obtain ⟨S, _, hS⟩ := h
  simp [hS]

theorem singularSeries_re_pos {n : ℕ} {F : MvPolynomial (Fin n) ℤ}
    (h : PositiveRealSingularSeries F) : 0 < (singularSeries F).re := by
  obtain ⟨S, hpos, hS⟩ := h
  simpa only [hS, Complex.ofReal_re] using hpos

/-- The concrete partial sum through Q equals the natural partial sum through
Q+1 because the added zero term vanishes. -/
theorem singularSeriesPartial_eq_sum_range {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (Q : ℕ) :
    singularSeriesPartial F Q = ∑ q ∈ Finset.range (Q + 1), singularSeriesTerm F q := by
  induction Q with
  | zero => simp
  | succ Q ih =>
      conv_rhs => rw [Finset.sum_range_succ]
      rw [singularSeriesPartial, Finset.sum_Icc_succ_top (by omega)]
      exact congrArg (fun z => z + singularSeriesTerm F (Q + 1)) ih

/-- Absolute convergence justifies the literal Q-truncations' limit. -/
theorem singularSeriesPartial_tendsto {n : ℕ} {F : MvPolynomial (Fin n) ℤ}
    (h : SingularSeriesAbsolutelyConvergent F) :
    Tendsto (singularSeriesPartial F) atTop (𝓝 (singularSeries F)) := by
  have heq : singularSeriesPartial F =
      fun Q => ∑ q ∈ Finset.range (Q + 1), singularSeriesTerm F q :=
    funext (singularSeriesPartial_eq_sum_range F)
  rw [heq]
  exact
    (summable_singularSeriesTerm h).hasSum.tendsto_sum_nat.comp
      (tendsto_add_atTop_nat 1)

/-- Bernert's input gives a positive real limit of the actual complex partial
series, with reality and convergence both visible in the conclusion. -/
theorem bernert_positive_partial_limit (bernert : Bernert2025Theorem1)
    {n : ℕ} (C : SymmetricIntegerCubicTensor n) (hn : 10 ≤ n)
    (hC : TensorDavenportGood C) :
    ∃ S : ℝ, 0 < S ∧
      Tendsto (singularSeriesPartial C.polynomial) atTop (𝓝 (S : ℂ)) := by
  obtain ⟨habs, S, hpos, hS⟩ := bernert n C hn hC
  exact ⟨S, hpos, hS ▸ singularSeriesPartial_tendsto habs⟩

end Literature
end CubicTenVariables
