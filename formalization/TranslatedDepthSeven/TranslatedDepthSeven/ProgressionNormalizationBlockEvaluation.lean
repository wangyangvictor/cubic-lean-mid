import TranslatedDepthSeven.HomogeneousLinearNormalizationBoxCount
import TranslatedDepthSeven.IntegralSurfaceNormalizationBlock
import TranslatedDepthSeven.SurfaceNormalizationResidueDisc

/-! Integral numerator columns for normalized progression blocks, and the
exact prime-to-modulus cancellation in their evaluation determinants. -/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000

def progressionHomogeneousCenter {N : ℕ} (u : Fin N → ℤ) : Fin (N + 1) → ℤ :=
  Fin.cases 1 u

def progressionHomogeneousDirection {N : ℕ} (y : Fin N → ℤ) : Fin (N + 1) → ℤ :=
  Fin.cases 0 y

def progressionHomogeneousPoint {N : ℕ} (u : Fin N → ℤ) (m : ℕ) (y : Fin N → ℤ) :
    Fin (N + 1) → ℤ :=
  Fin.cases 1 (fun i => u i + (m : ℤ) * y i)

def progressionNumeratorParameters {N : ℕ}
    (L : Fin 3 → MvPolynomial (Fin (N + 1)) ℤ) (u : Fin N → ℤ) :
    Fin 3 → MvPolynomial (Fin (N + 1)) ℤ :=
  ![L 0, L 1 - C (MvPolynomial.eval (progressionHomogeneousCenter u) (L 1)) * L 0,
    L 2 - C (MvPolynomial.eval (progressionHomogeneousCenter u) (L 2)) * L 0]

def progressionParameterValues {N : ℕ}
    (L : Fin 3 → MvPolynomial (Fin (N + 1)) ℤ) (y : Fin N → ℤ) : Fin 2 → ℤ :=
  fun i => MvPolynomial.eval (progressionHomogeneousDirection y) (L i.succ)

theorem eval_progressionHomogeneousPoint_linear {N : ℕ}
    (L : MvPolynomial (Fin (N + 1)) ℤ) (hL : L.IsHomogeneous 1)
    (u y : Fin N → ℤ) (m : ℕ) :
    MvPolynomial.eval (progressionHomogeneousPoint u m y) L =
      MvPolynomial.eval (progressionHomogeneousCenter u) L +
        (m : ℤ) * MvPolynomial.eval (progressionHomogeneousDirection y) L := by
  have hp : progressionHomogeneousPoint u m y = fun i =>
      progressionHomogeneousCenter u i + (m : ℤ) * progressionHomogeneousDirection y i := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [progressionHomogeneousPoint, progressionHomogeneousCenter,
        progressionHomogeneousDirection]
  rw [hp]
  exact eval_add_smul_of_isHomogeneous_one L hL _ _ _

theorem eval_progressionNumeratorParameters {N : ℕ}
    (L : Fin 3 → MvPolynomial (Fin (N + 1)) ℤ)
    (hL : ∀ i, (L i).IsHomogeneous 1) (hL0 : L 0 = X 0)
    (u y : Fin N → ℤ) (m : ℕ) :
    (fun i => MvPolynomial.eval (progressionHomogeneousPoint u m y)
      (progressionNumeratorParameters L u i)) =
        ![1, (m : ℤ) * progressionParameterValues L y 0,
          (m : ℤ) * progressionParameterValues L y 1] := by
  funext i
  fin_cases i
  · simp [progressionNumeratorParameters, hL0, progressionHomogeneousPoint]
  · change MvPolynomial.eval (progressionHomogeneousPoint u m y)
        (L 1 - C (MvPolynomial.eval (progressionHomogeneousCenter u) (L 1)) * L 0) = _
    simp only [map_sub, map_mul, eval_C, hL0, eval_X]
    rw [eval_progressionHomogeneousPoint_linear (L 1) (hL 1)]
    simp [progressionHomogeneousPoint, progressionParameterValues]
  · change MvPolynomial.eval (progressionHomogeneousPoint u m y)
        (L 2 - C (MvPolynomial.eval (progressionHomogeneousCenter u) (L 2)) * L 0) = _
    simp only [map_sub, map_mul, eval_C, hL0, eval_X]
    rw [eval_progressionHomogeneousPoint_linear (L 2) (hL 2)]
    simp [progressionHomogeneousPoint, progressionParameterValues]

/-- The normalized columns are actual integers; no division operation on
integers is used in their definition. -/
def progressionNormalizationBlockEntry {N d : ℕ}
    (L : Fin 3 → MvPolynomial (Fin (N + 1)) ℤ)
    (G : Fin d → MvPolynomial (Fin (N + 1)) ℤ)
    (u : Fin N → ℤ) (m k : ℕ) (y : Fin N → ℤ)
    (p : Fin d × AffinePlaneMonomialIndex k) : ℤ :=
  MvPolynomial.eval (progressionHomogeneousPoint u m y) (G p.1) *
    progressionParameterValues L y 0 ^ p.2.2.1 *
      progressionParameterValues L y 1 ^ (p.2.1.1 - p.2.2.1)

theorem eval_progressionNumeratorBlock {N d : ℕ}
    (L : Fin 3 → MvPolynomial (Fin (N + 1)) ℤ)
    (hL : ∀ i, (L i).IsHomogeneous 1) (hL0 : L 0 = X 0)
    (G : Fin d → MvPolynomial (Fin (N + 1)) ℤ)
    (u : Fin N → ℤ) (m k : ℕ) (y : Fin N → ℤ)
    (p : Fin d × AffinePlaneMonomialIndex k) :
    MvPolynomial.eval (progressionHomogeneousPoint u m y)
      (normalizationSurfaceBlockForm (progressionNumeratorParameters L u) G k p) =
        (m : ℤ) ^ affinePlaneMonomialIndexWeight p.2 *
          progressionNormalizationBlockEntry L G u m k y p := by
  rw [normalizationSurfaceBlockForm, map_mul,
    eval_aeval_affinePlaneHomogeneousMonomial]
  have he := eval_progressionNumeratorParameters L hL hL0 u y m
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have h2 := congrFun he 2
  simp at h0 h1 h2
  rw [h0, h1, h2, one_pow, one_mul, mul_pow, mul_pow]
  have hsum : p.2.2.1 + (p.2.1.1 - p.2.2.1) = affinePlaneMonomialIndexWeight p.2 := by
    have := p.2.2.2
    dsimp [affinePlaneMonomialIndexWeight]
    omega
  rw [← hsum, pow_add]
  unfold progressionNormalizationBlockEntry
  ring

theorem primePower_dvd_det_of_column_scaling
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A C : Matrix ι ι ℤ) (m p E : ℕ) (w : ι → ℕ)
    (hp : p.Prime) (hpm : ¬ p ∣ m)
    (hcolumns : ∀ i j, C i j = (m : ℤ) ^ w j * A i j)
    (hdiv : (p : ℤ) ^ E ∣ C.det) : (p : ℤ) ^ E ∣ A.det := by
  have he : C = Matrix.of (fun i j => (m : ℤ) ^ w j * A i j) := by
    ext i j
    exact hcolumns i j
  rw [he, Matrix.det_mul_row, Finset.prod_pow_eq_pow_sum] at hdiv
  have hcop : IsCoprime (p : ℤ) (m : ℤ) :=
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm).isCoprime
  exact (hcop.pow : IsCoprime ((p : ℤ) ^ E) ((m : ℤ) ^ (∑ j, w j))).dvd_of_dvd_mul_left hdiv

/-- An actual residue disc for the original points supplies divisibility of
the normalized integer matrix after prime-to-`m` cancellation. -/
theorem progressionNormalizationBlock_det_dvd_of_residueDisc
    {N d : ℕ} (k t s p m : ℕ)
    (hp : p.Prime) (hpm : ¬ p ∣ m)
    (hcard : Fintype.card (Fin d × AffinePlaneMonomialIndex k) = affinePlaneMonomialCount t + s)
    (hE : 0 < affinePlaneMonomialWeight t + (t + 1) * s)
    (L : Fin 3 → MvPolynomial (Fin (N + 1)) ℤ)
    (hL : ∀ i, (L i).IsHomogeneous 1) (hL0 : L 0 = X 0)
    (G : Fin d → MvPolynomial (Fin (N + 1)) ℤ)
    (u : Fin N → ℤ) (y : Fin d × AffinePlaneMonomialIndex k → Fin N → ℤ)
    (disc : SurfaceNormalizationResidueDisc (Fin (N + 1))
      (Fin d × AffinePlaneMonomialIndex k) p
      (affinePlaneMonomialWeight t + (t + 1) * s) hE
      (fun j => progressionHomogeneousPoint u m (y j))) :
    (p : ℤ) ^ (affinePlaneMonomialWeight t + (t + 1) * s) ∣
      (Matrix.of (fun j i => progressionNormalizationBlockEntry L G u m k (y j) i)).det := by
  classical
  let C : Matrix (Fin d × AffinePlaneMonomialIndex k)
      (Fin d × AffinePlaneMonomialIndex k) ℤ := Matrix.of (fun j i =>
    MvPolynomial.eval (progressionHomogeneousPoint u m (y j))
      (normalizationSurfaceBlockForm (progressionNumeratorParameters L u) G k i))
  apply primePower_dvd_det_of_column_scaling _ C m p _
    (fun i => affinePlaneMonomialIndexWeight i.2) hp hpm
  · intro j i
    exact eval_progressionNumeratorBlock L hL hL0 G u m k (y j) i
  · have h := disc.det_dvd t s hcard hE p _
      (normalizationSurfaceBlockForm (progressionNumeratorParameters L u) G k)
    change (p : ℤ) ^ _ ∣ C.transpose.det at h
    simpa only [Matrix.det_transpose] using h

theorem progressionNormalizationBlockEntry_natAbs_le {N d : ℕ}
    (L : Fin 3 → MvPolynomial (Fin (N + 1)) ℤ)
    (G : Fin d → MvPolynomial (Fin (N + 1)) ℤ)
    (u : Fin N → ℤ) (m k D H b R : ℕ) (y : Fin N → ℤ)
    (hG : ∀ i, (MvPolynomial.eval (progressionHomogeneousPoint u m y) (G i)).natAbs ≤ D * H ^ b)
    (hL : ∀ i, (progressionParameterValues L y i).natAbs ≤ R)
    (p : Fin d × AffinePlaneMonomialIndex k) :
    (progressionNormalizationBlockEntry L G u m k y p).natAbs ≤
      (D * H ^ b) * R ^ affinePlaneMonomialIndexWeight p.2 := by
  simp only [progressionNormalizationBlockEntry, Int.natAbs_mul, Int.natAbs_pow]
  calc
    _ ≤ (D * H ^ b) * R ^ p.2.2.1 * R ^ (p.2.1.1 - p.2.2.1) := by
      gcongr
      · exact hG p.1
      · exact hL 0
      · exact hL 1
    _ = _ := by
      rw [mul_assoc, ← pow_add]
      congr 2
      have := p.2.2.2
      dsimp [affinePlaneMonomialIndexWeight]
      omega

/-- The source radius `H` only affects the fixed auxiliary degree `b`;
the complete growing monomial block uses the progression radius `R`. -/
theorem progressionNormalizationBlock_det_natAbs_le {N d : ℕ}
    (L : Fin 3 → MvPolynomial (Fin (N + 1)) ℤ)
    (G : Fin d → MvPolynomial (Fin (N + 1)) ℤ)
    (u : Fin N → ℤ) (m k D H b R : ℕ)
    (y : Fin d × AffinePlaneMonomialIndex k → Fin N → ℤ)
    (hG : ∀ j i, (MvPolynomial.eval (progressionHomogeneousPoint u m (y j)) (G i)).natAbs ≤ D * H ^ b)
    (hL : ∀ j i, (progressionParameterValues L (y j) i).natAbs ≤ R) :
    (Matrix.of (fun j i => progressionNormalizationBlockEntry L G u m k (y j) i)).det.natAbs ≤
      (d * affinePlaneMonomialCount k).factorial *
        (D * H ^ b) ^ (d * affinePlaneMonomialCount k) * R ^ (d * affinePlaneMonomialWeight k) := by
  classical
  have h := det_natAbs_le_factorial_mul_prod_column_bounds
    (Matrix.of (fun j i => progressionNormalizationBlockEntry L G u m k (y j) i))
    (fun i => (D * H ^ b) * R ^ affinePlaneMonomialIndexWeight i.2)
    (fun j i => progressionNormalizationBlockEntry_natAbs_le L G u m k D H b R
      (y j) (hG j) (hL j) i)
  rw [prod_normalizationSurfaceBlock_bounds (fun _ : Fin d => D * H ^ b) R k] at h
  simpa only [Fintype.card_prod, Fintype.card_fin, card_affinePlaneMonomialIndex,
    Finset.prod_const, Finset.card_univ, ← pow_mul, mul_assoc] using h

end
end TranslatedDepthSeven
