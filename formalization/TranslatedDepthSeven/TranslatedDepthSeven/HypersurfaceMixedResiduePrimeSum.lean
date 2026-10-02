import TranslatedDepthSeven.HypersurfaceMixedResidueExponentBound
import TranslatedDepthSeven.HypersurfaceBadReductionIncidence

/-!
# Prime sums for the actual mixed hypersurface residue exponent

The class-count constant in this file is real.  Thus a point-count bound of
the form `(1 + η) * p^2` can be used without replacing `1 + η` by an integer
ceiling.  The discarded columns are exactly those at which all three actual
affine partial derivatives vanish modulo `p`.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial
open scoped BigOperators

set_option maxHeartbeats 1500000

local instance hypersurfaceMixedResiduePrimeSum_decidableProp
    (P : Prop) : Decidable P := Classical.propDecidable P

/-- The finite-class Hölder estimate with an arbitrary positive real upper
bound for the number of classes. -/
theorem sum_smoothSurfaceJetExponent_lower_bound_real
    {ι : Type*} (a : Finset ι) (n : ι → ℕ) (M : ℝ)
    (hM : 0 < M) (hcard : (a.card : ℝ) ≤ M) :
    (2 * Real.sqrt 2 / 3) * ((∑ i ∈ a, n i : ℕ) : ℝ) ^ (3 / 2 : ℝ) /
        Real.sqrt M - 2 * (∑ i ∈ a, n i : ℕ) ≤
      ((∑ i ∈ a, smoothSurfaceJetExponent (n i) : ℕ) : ℝ) := by
  let c : ℝ := 2 * Real.sqrt 2 / 3
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hloc : c * (∑ i ∈ a, (n i : ℝ) ^ (3 / 2 : ℝ)) ≤
      ∑ i ∈ a, ((smoothSurfaceJetExponent (n i) : ℝ) + 2 * n i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => by
      have h := smoothSurfaceJetExponent_lower_bound (n i)
      dsimp [c]
      linarith
  have hholder := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
    (s := a) (f := fun i => (n i : ℝ)) (p := (3 / 2 : ℝ)) (by norm_num)
    (fun i hi => Nat.cast_nonneg _)
  norm_num only [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num] at hholder
  rw [← Real.sqrt_eq_rpow] at hholder
  have hsqrtcard : Real.sqrt (a.card : ℝ) ≤ Real.sqrt M := by
    exact Real.sqrt_le_sqrt hcard
  have hholderM : (∑ i ∈ a, (n i : ℝ)) ^ (3 / 2 : ℝ) ≤
      Real.sqrt M * ∑ i ∈ a, (n i : ℝ) ^ (3 / 2 : ℝ) :=
    hholder.trans (mul_le_mul_of_nonneg_right hsqrtcard (by positivity))
  have htotal : c * (∑ i ∈ a, (n i : ℝ)) ^ (3 / 2 : ℝ) ≤
      Real.sqrt M *
        ((∑ i ∈ a, (smoothSurfaceJetExponent (n i) : ℝ)) +
          2 * ∑ i ∈ a, (n i : ℝ)) := by
    have h₁ := mul_le_mul_of_nonneg_left hholderM hc
    have h₂ := mul_le_mul_of_nonneg_left hloc (Real.sqrt_nonneg M)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h₂
    nlinarith
  have hsqrtM : 0 < Real.sqrt M := Real.sqrt_pos.2 hM
  have hdiv : c * (∑ i ∈ a, (n i : ℝ)) ^ (3 / 2 : ℝ) / Real.sqrt M ≤
      (∑ i ∈ a, (smoothSurfaceJetExponent (n i) : ℝ)) +
        2 * ∑ i ∈ a, (n i : ℝ) := by
    apply (div_le_iff₀ hsqrtM).2
    simpa only [mul_comm (Real.sqrt M)] using htotal
  push_cast
  dsimp [c] at hdiv
  linarith

/-- Real-class-bound version of the sharp discard estimate. -/
theorem sum_smoothSurfaceJetExponent_lower_bound_discard_real
    {ι : Type*} (a : Finset ι) (n : ι → ℕ) (M : ℝ) (s b : ℕ)
    (hM : 0 < M) (hcard : (a.card : ℝ) ≤ M) (hb : b ≤ s)
    (hrows : (∑ i ∈ a, n i) = s - b) :
    (2 * Real.sqrt 2 / 3) * (s : ℝ) ^ (3 / 2 : ℝ) / Real.sqrt M -
        Real.sqrt 2 * b * Real.sqrt (s : ℝ) / Real.sqrt M - 2 * s ≤
      ((∑ i ∈ a, smoothSurfaceJetExponent (n i) : ℕ) : ℝ) := by
  have hlocal := sum_smoothSurfaceJetExponent_lower_bound_real a n M hM hcard
  rw [hrows] at hlocal
  have htangent := rpow_three_halves_discard_lower_bound (s : ℝ) ((s - b : ℕ) : ℝ)
    (by positivity) (by positivity)
  rw [Nat.cast_sub hb] at hlocal htangent
  have hc : 0 ≤ 2 * Real.sqrt 2 / 3 / Real.sqrt M := by positivity
  have hmul := mul_le_mul_of_nonneg_left htangent hc
  have hmul' : (2 * Real.sqrt 2 / 3) * (s : ℝ) ^ (3 / 2 : ℝ) /
        Real.sqrt M - Real.sqrt 2 * b * Real.sqrt (s : ℝ) / Real.sqrt M ≤
      (2 * Real.sqrt 2 / 3) * ((s : ℝ) - b) ^ (3 / 2 : ℝ) /
        Real.sqrt M := by
    convert hmul using 1 <;> ring
  linarith

/-- The actual mixed-residue exponent under a positive real bound for the
number of occupied smooth residue classes. -/
theorem hypersurfaceSmoothResidueExponent_lower_bound_real
    {ι : Type*} [Fintype ι]
    (p : ℕ) (F : MvPolynomial (Fin 3) ℤ) (y : ι → Fin 3 → ℤ)
    (M : ℝ) (hM : 0 < M)
    (hclasses : (Fintype.card (SurfaceOccupiedSmoothResidueClass p F y) : ℝ) ≤ M) :
    (2 * Real.sqrt 2 / 3) * (Fintype.card ι : ℝ) ^ (3 / 2 : ℝ) /
          Real.sqrt M -
        Real.sqrt 2 *
          (Fintype.card {j : ι //
            ¬ surfaceGradientNonzeroMod p F (y j)} : ℝ) *
          Real.sqrt (Fintype.card ι : ℝ) / Real.sqrt M -
        2 * Fintype.card ι ≤
      (hypersurfaceSmoothResidueExponent p F y : ℝ) := by
  classical
  let a : Finset (SurfaceOccupiedSmoothResidueClass p F y) := Finset.univ
  let n : SurfaceOccupiedSmoothResidueClass p F y → ℕ := fun c =>
    Fintype.card {j : SmoothSurfaceColumn p F y //
      smoothSurfacePointResidueClass p F y j = c}
  let s : ℕ := Fintype.card ι
  let b : ℕ := Fintype.card {j : ι //
    ¬ surfaceGradientNonzeroMod p F (y j)}
  have hb : b ≤ s := by
    dsimp [b, s]
    exact Fintype.card_subtype_le _
  have hrows : (∑ c ∈ a, n c) = s - b := by
    simp only [a, n, s, b]
    rw [sum_card_smoothSurfacePointResidueClass_fibers p F y,
      card_smoothSurfaceColumn_eq_card_sub_bad p F y]
  have hcard : (a.card : ℝ) ≤ M := by
    simpa only [a, Finset.card_univ, Nat.cast_le] using hclasses
  have hbound := sum_smoothSurfaceJetExponent_lower_bound_discard_real
    a n M s b hM hcard hb hrows
  simpa only [a, n, s, b, Finset.sum_const_zero, Finset.sum_filter,
    Finset.mem_univ, if_true, hypersurfaceSmoothResidueExponent] using hbound

/-- The bad-column predicate in the exponent is literally the affine-gradient
bad-reduction predicate for the first chart. -/
theorem not_surfaceGradientNonzeroMod_firstChart_iff_badReduction
    (F : MvPolynomial (Fin 4) ℤ) (x : Fin 3 → ℤ) (p : ℕ) :
    (¬ surfaceGradientNonzeroMod p
        (surfaceHypersurfaceFirstChartDehomogenize F) x) ↔
      hypersurfaceAffineGradientBadReduction F x p := by
  simp only [surfaceGradientNonzeroMod, hypersurfaceAffineGradientBadReduction,
    not_exists, not_ne_iff]

/-- Sum the sharp local exponent bounds over an arbitrary finite prime set.
The bad-column loss is still stated using the literal complement of the
actual affine-gradient predicate. -/
theorem hypersurfaceSmoothResidueExponent_primeSum_lower_bound_of_badReduction
    {ι : Type*} [Fintype ι]
    (P : Finset ℕ) (F : MvPolynomial (Fin 3) ℤ) (y : ι → Fin 3 → ℤ)
    (K A : ℝ) (hK : 0 < K)
    (hP : ∀ p ∈ P, p.Prime)
    (hclasses : ∀ p ∈ P,
      (Fintype.card (SurfaceOccupiedSmoothResidueClass p F y) : ℝ) ≤
        K * (p : ℝ) ^ 2)
    (hbad :
      (∑ p ∈ P,
        (Real.sqrt 2 *
          (Fintype.card {j : ι //
            ¬ surfaceGradientNonzeroMod p F (y j)} : ℝ) *
          Real.sqrt (Fintype.card ι : ℝ) / (p : ℝ)) *
            Real.log (p : ℝ)) ≤
        Real.sqrt 2 * A *
          ((Fintype.card ι : ℝ) * Real.sqrt (Fintype.card ι : ℝ))) :
    (2 * Real.sqrt 2 / 3) / Real.sqrt K *
          (Fintype.card ι : ℝ) ^ (3 / 2 : ℝ) *
          (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) -
        (Real.sqrt 2 * A / Real.sqrt K) *
          ((Fintype.card ι : ℝ) * Real.sqrt (Fintype.card ι : ℝ)) -
        2 * Fintype.card ι * (∑ p ∈ P, Real.log (p : ℝ)) ≤
      ∑ p ∈ P,
        (hypersurfaceSmoothResidueExponent p F y : ℝ) * Real.log (p : ℝ) := by
  classical
  have hsqrtK : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
  have hpoint (p : ℕ) (hp : p ∈ P) :
      ((2 * Real.sqrt 2 / 3) / Real.sqrt K *
          (Fintype.card ι : ℝ) ^ (3 / 2 : ℝ)) *
            (Real.log (p : ℝ) / (p : ℝ)) -
        (1 / Real.sqrt K) *
          ((Real.sqrt 2 *
            (Fintype.card {j : ι //
              ¬ surfaceGradientNonzeroMod p F (y j)} : ℝ) *
            Real.sqrt (Fintype.card ι : ℝ) / (p : ℝ)) *
              Real.log (p : ℝ)) -
        (2 * Fintype.card ι) * Real.log (p : ℝ) ≤
          (hypersurfaceSmoothResidueExponent p F y : ℝ) *
            Real.log (p : ℝ) := by
    have hpPrime := hP p hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    have hM : 0 < K * (p : ℝ) ^ 2 := mul_pos hK (sq_pos_of_pos hpR)
    have hlocal := hypersurfaceSmoothResidueExponent_lower_bound_real
      p F y (K * (p : ℝ) ^ 2) hM (hclasses p hp)
    have hsqrt : Real.sqrt (K * (p : ℝ) ^ 2) = Real.sqrt K * (p : ℝ) := by
      rw [Real.sqrt_mul hK.le, Real.sqrt_sq hpR.le]
    rw [hsqrt] at hlocal
    have hlog : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hpPrime.one_le)
    have hmul := mul_le_mul_of_nonneg_right hlocal hlog
    convert hmul using 1
    all_goals field_simp
  have hsum := Finset.sum_le_sum hpoint
  have hsum' :
      ((2 * Real.sqrt 2 / 3) / Real.sqrt K *
          (Fintype.card ι : ℝ) ^ (3 / 2 : ℝ)) *
            (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) -
        (1 / Real.sqrt K) *
          (∑ p ∈ P,
            (Real.sqrt 2 *
              (Fintype.card {j : ι //
                ¬ surfaceGradientNonzeroMod p F (y j)} : ℝ) *
              Real.sqrt (Fintype.card ι : ℝ) / (p : ℝ)) *
                Real.log (p : ℝ)) -
        (2 * Fintype.card ι) * (∑ p ∈ P, Real.log (p : ℝ)) ≤
      ∑ p ∈ P,
        (hypersurfaceSmoothResidueExponent p F y : ℝ) * Real.log (p : ℝ) := by
    simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum] using hsum
  have hbadScaled := mul_le_mul_of_nonneg_left hbad
    (show 0 ≤ 1 / Real.sqrt K by positivity)
  have hbadScaled' :
      (1 / Real.sqrt K) *
          (∑ p ∈ P,
            (Real.sqrt 2 *
              (Fintype.card {j : ι //
                ¬ surfaceGradientNonzeroMod p F (y j)} : ℝ) *
              Real.sqrt (Fintype.card ι : ℝ) / (p : ℝ)) *
                Real.log (p : ℝ)) ≤
        (Real.sqrt 2 * A / Real.sqrt K) *
          ((Fintype.card ι : ℝ) * Real.sqrt (Fintype.card ι : ℝ)) := by
    convert hbadScaled using 1
    all_goals ring
  calc
    _ ≤ ((2 * Real.sqrt 2 / 3) / Real.sqrt K *
          (Fintype.card ι : ℝ) ^ (3 / 2 : ℝ)) *
            (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) -
        (1 / Real.sqrt K) *
          (∑ p ∈ P,
            (Real.sqrt 2 *
              (Fintype.card {j : ι //
                ¬ surfaceGradientNonzeroMod p F (y j)} : ℝ) *
              Real.sqrt (Fintype.card ι : ℝ) / (p : ℝ)) *
                Real.log (p : ℝ)) -
        (2 * Fintype.card ι) * (∑ p ∈ P, Real.log (p : ℝ)) := by
      linarith
    _ ≤ _ := hsum'

/-- The logarithm of a finite product of positive prime powers is the
weighted prime-log sum.  This is kept separate from determinant bounds so it
can also be used by the natural-number auxiliary-form threshold. -/
theorem log_primePowerProduct_eq
    (P : Finset ℕ) (E : ℕ → ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Real.log (((∏ p ∈ P, p ^ E p : ℕ) : ℕ) : ℝ) =
      ∑ p ∈ P, (E p : ℝ) * Real.log (p : ℝ) := by
  rw [Nat.cast_prod]
  rw [Real.log_prod]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    exact_mod_cast pow_ne_zero (E p) (hP p hp).ne_zero

/-- A nonzero integer divisible by the displayed prime-power product has
logarithmic size at least the weighted prime-log sum. -/
theorem primePower_log_sum_le_log_natAbs_of_dvd
    (P : Finset ℕ) (E : ℕ → ℕ) (hP : ∀ p ∈ P, p.Prime)
    (D : ℤ) (hD : D ≠ 0)
    (hdiv : ((∏ p ∈ P, p ^ E p : ℕ) : ℤ) ∣ D) :
    (∑ p ∈ P, (E p : ℝ) * Real.log (p : ℝ)) ≤
      Real.log (D.natAbs : ℝ) := by
  let Q : ℕ := ∏ p ∈ P, p ^ E p
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact Finset.prod_pos fun p hp => pow_pos (hP p hp).pos _
  have hdivNat : Q ∣ D.natAbs := Int.natCast_dvd.mp hdiv
  have hle : Q ≤ D.natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hD) hdivNat
  have hlog : Real.log (Q : ℝ) ≤ Real.log (D.natAbs : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast hQpos
    · exact_mod_cast hle
  rw [show Real.log (Q : ℝ) =
      ∑ p ∈ P, (E p : ℝ) * Real.log (p : ℝ) by
        exact log_primePowerProduct_eq P E hP] at hlog
  exact hlog

/-- Logarithmic upper bound furnished by the literal mixed-residue
determinant divisor. -/
theorem hypersurfaceSmoothResidueExponent_primeSum_le_log_det
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (F : MvPolynomial (Fin 3) ℤ) (y : ι → Fin 3 → ℤ)
    (hF : ∀ j, MvPolynomial.eval (y j) F = 0)
    (G : ι → MvPolynomial (Fin 3) ℤ)
    (hdet : (Matrix.of (fun i j => MvPolynomial.eval (y j) (G i))).det ≠ 0) :
    (∑ p ∈ P,
      (hypersurfaceSmoothResidueExponent p F y : ℝ) * Real.log (p : ℝ)) ≤
      Real.log
        ((Matrix.of (fun i j => MvPolynomial.eval (y j) (G i))).det.natAbs : ℝ) := by
  apply primePower_log_sum_le_log_natAbs_of_dvd P
    (fun p => hypersurfaceSmoothResidueExponent p F y) hP _ hdet
  simpa only [Nat.cast_prod, Nat.cast_pow] using
    hypersurfaceMixedResidue_primeProduct_det_dvd P hP F y hF G

/-- Direct determinant-log form of the sharp mixed-residue prime-sum bound. -/
theorem hypersurfaceMixedResidue_primeSum_lower_bound_le_log_det
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finset ℕ) (F : MvPolynomial (Fin 3) ℤ) (y : ι → Fin 3 → ℤ)
    (K A : ℝ) (hK : 0 < K)
    (hP : ∀ p ∈ P, p.Prime)
    (hclasses : ∀ p ∈ P,
      (Fintype.card (SurfaceOccupiedSmoothResidueClass p F y) : ℝ) ≤
        K * (p : ℝ) ^ 2)
    (hbad :
      (∑ p ∈ P,
        (Real.sqrt 2 *
          (Fintype.card {j : ι //
            ¬ surfaceGradientNonzeroMod p F (y j)} : ℝ) *
          Real.sqrt (Fintype.card ι : ℝ) / (p : ℝ)) *
            Real.log (p : ℝ)) ≤
        Real.sqrt 2 * A *
          ((Fintype.card ι : ℝ) * Real.sqrt (Fintype.card ι : ℝ)))
    (hF : ∀ j, MvPolynomial.eval (y j) F = 0)
    (G : ι → MvPolynomial (Fin 3) ℤ)
    (hdet : (Matrix.of (fun i j => MvPolynomial.eval (y j) (G i))).det ≠ 0) :
    (2 * Real.sqrt 2 / 3) / Real.sqrt K *
          (Fintype.card ι : ℝ) ^ (3 / 2 : ℝ) *
          (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) -
        (Real.sqrt 2 * A / Real.sqrt K) *
          ((Fintype.card ι : ℝ) * Real.sqrt (Fintype.card ι : ℝ)) -
        2 * Fintype.card ι * (∑ p ∈ P, Real.log (p : ℝ)) ≤
      Real.log
        ((Matrix.of (fun i j => MvPolynomial.eval (y j) (G i))).det.natAbs : ℝ) := by
  exact (hypersurfaceSmoothResidueExponent_primeSum_lower_bound_of_badReduction
    P F y K A hK hP hclasses hbad).trans
      (hypersurfaceSmoothResidueExponent_primeSum_le_log_det
        P hP F y hF G hdet)

/-- Fixed-equation form: the height exponent and threshold are selected
before the box, prime family, column type, and columns.  The only point-count
input is the literal real constant `K` in the occupied-class estimate. -/
theorem exists_hypersurface_mixedResidue_log_lower_bound
    (F : MvPolynomial (Fin 4) ℤ) (K : ℝ) (hK : 0 < K) :
    ∃ A H₀ : ℕ, 2 ≤ A ∧ 2 ≤ H₀ ∧
      ∀ H : ℕ, H₀ ≤ H → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, Real.log (H : ℝ) ≤ (p : ℝ)) →
      ∀ (ι : Type*) [Fintype ι] (y : ι → Fin 3 → ℤ),
      (∀ j i, (y j i).natAbs ≤ H) →
      (∀ j, ∃ v, MvPolynomial.eval (y j)
        (MvPolynomial.pderiv v
          (surfaceHypersurfaceFirstChartDehomogenize F)) ≠ 0) →
      (∀ p ∈ P,
        (Fintype.card (SurfaceOccupiedSmoothResidueClass p
          (surfaceHypersurfaceFirstChartDehomogenize F) y) : ℝ) ≤
            K * (p : ℝ) ^ 2) →
      (2 * Real.sqrt 2 / 3) / Real.sqrt K *
            (Fintype.card ι : ℝ) ^ (3 / 2 : ℝ) *
            (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) -
          (Real.sqrt 2 * A / Real.sqrt K) *
            ((Fintype.card ι : ℝ) * Real.sqrt (Fintype.card ι : ℝ)) -
          2 * Fintype.card ι * (∑ p ∈ P, Real.log (p : ℝ)) ≤
        ∑ p ∈ P,
          (hypersurfaceSmoothResidueExponent p
            (surfaceHypersurfaceFirstChartDehomogenize F) y : ℝ) *
              Real.log (p : ℝ) := by
  classical
  obtain ⟨A, H₀, hA, hH₀, hcolumn⟩ :=
    exists_hypersurface_badReduction_column_bound F
  refine ⟨A, H₀, hA, hH₀, ?_⟩
  intro H hH P hP hlarge ι inst y hbox hgrad hclasses
  obtain ⟨_hproducts, _hincidence, hdiscard⟩ :=
    hcolumn H hH P hP hlarge ι y hbox hgrad
  have hbadCard (p : ℕ) :
      Fintype.card {j : ι //
        ¬ surfaceGradientNonzeroMod p
          (surfaceHypersurfaceFirstChartDehomogenize F) (y j)} =
        (Finset.univ.filter fun j =>
          hypersurfaceAffineGradientBadReduction F (y j) p).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      not_surfaceGradientNonzeroMod_firstChart_iff_badReduction]
  have hbad :
      (∑ p ∈ P,
        (Real.sqrt 2 *
          (Fintype.card {j : ι //
            ¬ surfaceGradientNonzeroMod p
              (surfaceHypersurfaceFirstChartDehomogenize F) (y j)} : ℝ) *
          Real.sqrt (Fintype.card ι : ℝ) / (p : ℝ)) *
            Real.log (p : ℝ)) ≤
        Real.sqrt 2 * A *
          ((Fintype.card ι : ℝ) * Real.sqrt (Fintype.card ι : ℝ)) := by
    simpa only [hbadCard] using hdiscard
  exact hypersurfaceSmoothResidueExponent_primeSum_lower_bound_of_badReduction
    P (surfaceHypersurfaceFirstChartDehomogenize F) y K A hK hP hclasses hbad

end
end TranslatedDepthSeven
