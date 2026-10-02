import TranslatedDepthSeven.ProgressionNormalizationBlockAuxiliary
import TranslatedDepthSeven.HypersurfaceMixedResidueDeterminant

/-!
# Auxiliary forms from mixed residue classes in a progression

The local exponent counts the actual smooth residue classes of the original
points `(1,u+m*y)`. Columns with singular reduction remain in the determinant.
For primes not dividing `m`, numerator scaling cancels without changing this
exponent. A sufficiently large product of these gains kills every evaluation
minor and supplies a proper homogeneous cut in the original surface ideal.

The numerical product threshold is explicit; this file does not claim the
prime summation or the final Salberger estimate.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000

/-- The literal mixed-residue exponent at the original progression points. -/
abbrev progressionHypersurfaceSmoothResidueExponent
    {ι : Type*} [Fintype ι] (p : ℕ) (F : MvPolynomial (Fin 4) ℤ)
    (u : Fin 3 → ℤ) (m : ℕ) (y : ι → Fin 3 → ℤ) : ℕ :=
  hypersurfaceSmoothResidueExponent p (surfaceHypersurfaceFirstChartDehomogenize F)
    (fun j i => u i + (m : ℤ) * y j i)

theorem progressionNormalizationBlock_mixedPrime_det_dvd
    {d : ℕ} (k p m : ℕ) (hp : p.Prime) (hpm : ¬ p ∣ m)
    (L : Fin 3 → MvPolynomial (Fin 4) ℤ)
    (hL : ∀ i, (L i).IsHomogeneous 1) (hL0 : L 0 = X 0)
    (G : Fin d → MvPolynomial (Fin 4) ℤ)
    (F : MvPolynomial (Fin 4) ℤ) (u : Fin 3 → ℤ)
    (y : Fin d × AffinePlaneMonomialIndex k → Fin 3 → ℤ)
    (hyF : ∀ j, MvPolynomial.eval (progressionHomogeneousPoint u m (y j)) F = 0) :
    (p : ℤ) ^ progressionHypersurfaceSmoothResidueExponent p F u m y ∣
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
  · let x := fun j i => u i + (m : ℤ) * y j i
    have hx : ∀ j, MvPolynomial.eval (x j)
        (surfaceHypersurfaceFirstChartDehomogenize F) = 0 := by
      intro j
      rw [surfaceHypersurfaceFirstChart_eval]
      exact hyF j
    have hdiv := hypersurfaceMixedResidue_det_dvd p hp
      (surfaceHypersurfaceFirstChartDehomogenize F) x hx
      (fun i => surfaceHypersurfaceFirstChartDehomogenize
        (normalizationSurfaceBlockForm (progressionNumeratorParameters L u) G k i))
    have heq : (Matrix.of (fun i j => MvPolynomial.eval (x j)
        (surfaceHypersurfaceFirstChartDehomogenize
          (normalizationSurfaceBlockForm (progressionNumeratorParameters L u) G k i)))) =
        C.transpose := by
      ext i j
      exact surfaceHypersurfaceFirstChart_eval (x j) _
    rw [heq, Matrix.det_transpose] at hdiv
    exact hdiv

theorem progressionNormalizationBlock_mixedPrimeProduct_det_dvd
    {d : ℕ} (k m : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hPm : ∀ p ∈ P, ¬ p ∣ m)
    (L : Fin 3 → MvPolynomial (Fin 4) ℤ)
    (hL : ∀ i, (L i).IsHomogeneous 1) (hL0 : L 0 = X 0)
    (G : Fin d → MvPolynomial (Fin 4) ℤ)
    (F : MvPolynomial (Fin 4) ℤ) (u : Fin 3 → ℤ)
    (y : Fin d × AffinePlaneMonomialIndex k → Fin 3 → ℤ)
    (hyF : ∀ j, MvPolynomial.eval (progressionHomogeneousPoint u m (y j)) F = 0) :
    (∏ p ∈ P, (p : ℤ) ^ progressionHypersurfaceSmoothResidueExponent p F u m y) ∣
      (Matrix.of (fun j i => progressionNormalizationBlockEntry L G u m k (y j) i)).det := by
  apply primePowerProduct_dvd_of_local_divisibility P _ _ hP
  intro p hp
  exact progressionNormalizationBlock_mixedPrime_det_dvd k p m (hP p hp) (hPm p hp)
    L hL hL0 G F u y hyF

theorem progressionNormalizationBlock_det_eq_zero_of_mixedResidues
    {d : ℕ} (b k D H R m : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hPm : ∀ p ∈ P, ¬ p ∣ m)
    (L : Fin 3 → MvPolynomial (Fin 4) ℤ)
    (hL : ∀ i, (L i).IsHomogeneous 1) (hL0 : L 0 = X 0)
    (G : Fin d → MvPolynomial (Fin 4) ℤ)
    (F : MvPolynomial (Fin 4) ℤ) (u : Fin 3 → ℤ)
    (y : Fin d × AffinePlaneMonomialIndex k → Fin 3 → ℤ)
    (hyF : ∀ j, MvPolynomial.eval (progressionHomogeneousPoint u m (y j)) F = 0)
    (hG : ∀ j i, (MvPolynomial.eval (progressionHomogeneousPoint u m (y j)) (G i)).natAbs ≤ D * H ^ b)
    (hparams : ∀ j i, (progressionParameterValues L (y j) i).natAbs ≤ R)
    (hlarge : (d * affinePlaneMonomialCount k).factorial *
      (D * H ^ b) ^ (d * affinePlaneMonomialCount k) *
        R ^ (d * affinePlaneMonomialWeight k) <
          ∏ p ∈ P, p ^ progressionHypersurfaceSmoothResidueExponent p F u m y) :
    (Matrix.of (fun j i => progressionNormalizationBlockEntry L G u m k (y j) i)).det = 0 := by
  have hdiv := progressionNormalizationBlock_mixedPrimeProduct_det_dvd k m P hP hPm
    L hL hL0 G F u y hyF
  apply TangentMinors.eq_zero_of_dvd_of_natAbs_lt hdiv
  simpa only [← Nat.cast_pow, ← Nat.cast_prod, Int.natAbs_natCast] using
    (progressionNormalizationBlock_det_natAbs_le L G u m k D H b R y hG hparams).trans_lt hlarge

/-- A proper cut through the entire finite packet, using the actual mixed
exponents of each selected minor. The packet may occupy several residue
classes and may have singular reductions at any of the auxiliary primes. -/
theorem exists_progression_auxiliary_of_mixedResidue_minors
    {d : ℕ} (b k D H R m S : ℕ) (hm : m ≠ 0)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPm : ∀ p ∈ P, ¬ p ∣ m)
    (I : Ideal (MvPolynomial (Fin 4) ℚ))
    (L : Fin 3 → MvPolynomial (Fin 4) ℤ)
    (hL : ∀ i, (L i).IsHomogeneous 1) (hL0 : L 0 = X 0)
    (G : Fin d → MvPolynomial (Fin 4) ℤ) (hGhom : ∀ i, (G i).IsHomogeneous b)
    (hLI : LinearIndependent ℚ (fun p : Fin d × AffinePlaneMonomialIndex k =>
      Ideal.Quotient.mk I (MvPolynomial.map (Int.castRingHom ℚ)
        (normalizationSurfaceBlockForm L G k p))))
    (F : MvPolynomial (Fin 4) ℤ) (u : Fin 3 → ℤ) (y : Fin S → Fin 3 → ℤ)
    (hyF : ∀ j, MvPolynomial.eval (progressionHomogeneousPoint u m (y j)) F = 0)
    (hG : ∀ j i, (MvPolynomial.eval (progressionHomogeneousPoint u m (y j)) (G i)).natAbs ≤ D * H ^ b)
    (hparams : ∀ j i, (progressionParameterValues L (y j) i).natAbs ≤ R)
    (hlarge : ∀ select : Fin d × AffinePlaneMonomialIndex k → Fin S,
      Function.Injective select →
      (d * affinePlaneMonomialCount k).factorial *
        (D * H ^ b) ^ (d * affinePlaneMonomialCount k) *
          R ^ (d * affinePlaneMonomialWeight k) <
            ∏ p ∈ P, p ^ progressionHypersurfaceSmoothResidueExponent p F u m (y ∘ select)) :
    ∃ Q : MvPolynomial (Fin 4) ℚ, Q.IsHomogeneous (b + k) ∧ Q ∉ I ∧
      ∀ j, MvPolynomial.eval (fun i => (progressionHomogeneousPoint u m (y j) i : ℚ)) Q = 0 := by
  classical
  let ι := Fin d × AffinePlaneMonomialIndex k
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let FQ : Fin (Fintype.card ι) → MvPolynomial (Fin 4) ℚ :=
    fun i => progressionRationalBlockForm L G u m k (e.symm i)
  apply exists_auxiliaryHomogeneousPolynomial_of_all_evaluation_minors_eq_zero
    I FQ (fun j i => (progressionHomogeneousPoint u m (y j) i : ℚ))
  · exact (linearIndependent_progressionRationalBlockForm I L G u m k hm hLI).comp
      e.symm e.symm.injective
  · intro i
    exact progressionRationalBlockForm_isHomogeneous L hL G hGhom u m k (e.symm i)
  · intro cols hcols
    let select : ι → Fin S := fun i => cols (e i)
    have hselect : Function.Injective select := hcols.comp e.injective
    have hz := progressionNormalizationBlock_det_eq_zero_of_mixedResidues b k D H R m
      P hP hPm L hL hL0 G F u (y ∘ select) (fun j => hyF (select j))
      (fun j i => hG (select j) i) (fun j i => hparams (select j) i)
      (hlarge select hselect)
    let Z : Matrix ι ι ℤ := Matrix.of (fun i j =>
      progressionNormalizationBlockEntry L G u m k (y (select j)) i)
    have hZ : Z.det = 0 := by
      change Z.transpose.det = 0 at hz
      simpa only [Matrix.det_transpose] using hz
    let Q : Matrix ι ι ℚ := Matrix.of (fun i j =>
      MvPolynomial.eval (fun a => (progressionHomogeneousPoint u m (y (select j)) a : ℚ))
        (progressionRationalBlockForm L G u m k i))
    have hQmap : Q = (Int.castRingHom ℚ).mapMatrix Z := by
      ext i j
      exact eval_progressionRationalBlockForm L hL hL0 G u m k hm (y (select j)) i
    have hQ : Q.det = 0 := by
      rw [hQmap, ← (Int.castRingHom ℚ).map_det, hZ, map_zero]
    have hreindex := (Matrix.det_submatrix_equiv_self e.symm Q).trans hQ
    simpa only [Q, FQ, Matrix.submatrix, Matrix.of_apply, select,
      Equiv.apply_symm_apply, id_eq] using hreindex

end
end TranslatedDepthSeven
