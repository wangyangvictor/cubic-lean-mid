import TranslatedDepthSeven.ProgressionNormalizationMixedAuxiliary

/-!
# Simultaneous common-packet and mixed-prime determinant gains

The squarefree packet modulus `q` supplies the common smooth-residue
exponent. The additional prime set contributes the actual mixed-residue
exponents, and its primes are required not to divide `q`. Both contributions
are taken on the same normalized integer evaluation determinant after
cancelling powers of the progression scale `m` at primes not dividing `m`.
The scale `m` is not assumed prime. No numerical prime-selection or final
Salberger threshold is asserted.
-/

namespace TranslatedDepthSeven

noncomputable section
open MvPolynomial
open scoped BigOperators

set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000

/-- The common smooth-residue certificates give the full squarefree packet
gain on the normalized integer determinant. -/
theorem progressionNormalizationBlock_packet_det_dvd
    {d : ℕ} (hd : 0 < d) (k t s q m : ℕ)
    (hcard : Fintype.card (Fin d × AffinePlaneMonomialIndex k) = affinePlaneMonomialCount t + s)
    (hE : 0 < affinePlaneMonomialWeight t + (t + 1) * s)
    (L : Fin 3 → MvPolynomial (Fin 4) ℤ)
    (hL : ∀ i, (L i).IsHomogeneous 1) (hL0 : L 0 = X 0)
    (G : Fin d → MvPolynomial (Fin 4) ℤ)
    (F : MvPolynomial (Fin 4) ℤ) (u : Fin 3 → ℤ)
    (y : Fin d × AffinePlaneMonomialIndex k → Fin 3 → ℤ)
    (hyF : ∀ j, eval (progressionHomogeneousPoint u m (y j)) F = 0)
    (hq : Squarefree q)
    (hlocal : ∀ p, p.Prime → p ∣ q → ¬ p ∣ m ∧
      ∃ (z : Fin 3 → ℤ) (v : Fin 3),
        (∀ j i, (p : ℤ) ∣ y j i - z i) ∧
        (eval (fun i => u i + (m : ℤ) * z i)
          (pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0) :
    (q : ℤ) ^ (affinePlaneMonomialWeight t + (t + 1) * s) ∣
      (Matrix.of (fun j i => progressionNormalizationBlockEntry L G u m k (y j) i)).det := by
  apply squarefreePower_dvd_of_primePower_dvd hq
  intro p hp hpq
  obtain ⟨hpm, z, v, hyz, hzJ⟩ := hlocal p hp hpq
  exact progressionNormalizationBlock_det_dvd_of_hypersurface hd k t s p m hp hpm
    hcard hE L hL hL0 G F u y z hyF hyz v hzJ

/-- The common-packet gain and mixed-residue gains multiply when the
additional primes avoid the packet modulus. This prevents double counting
the same prime while retaining every actual singular-reduction column. -/
theorem progressionNormalizationBlock_packet_mixedPrimeProduct_det_dvd
    {d : ℕ} (hd : 0 < d) (k t s q m : ℕ)
    (hcard : Fintype.card (Fin d × AffinePlaneMonomialIndex k) = affinePlaneMonomialCount t + s)
    (hE : 0 < affinePlaneMonomialWeight t + (t + 1) * s)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hPm : ∀ p ∈ P, ¬ p ∣ m) (hPq : ∀ p ∈ P, ¬ p ∣ q)
    (L : Fin 3 → MvPolynomial (Fin 4) ℤ)
    (hL : ∀ i, (L i).IsHomogeneous 1) (hL0 : L 0 = X 0)
    (G : Fin d → MvPolynomial (Fin 4) ℤ)
    (F : MvPolynomial (Fin 4) ℤ) (u : Fin 3 → ℤ)
    (y : Fin d × AffinePlaneMonomialIndex k → Fin 3 → ℤ)
    (hyF : ∀ j, eval (progressionHomogeneousPoint u m (y j)) F = 0)
    (hq : Squarefree q)
    (hlocal : ∀ p, p.Prime → p ∣ q → ¬ p ∣ m ∧
      ∃ (z : Fin 3 → ℤ) (v : Fin 3),
        (∀ j i, (p : ℤ) ∣ y j i - z i) ∧
        (eval (fun i => u i + (m : ℤ) * z i)
          (pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0) :
    (q : ℤ) ^ (affinePlaneMonomialWeight t + (t + 1) * s) *
        (∏ p ∈ P, (p : ℤ) ^ progressionHypersurfaceSmoothResidueExponent p F u m y) ∣
      (Matrix.of (fun j i => progressionNormalizationBlockEntry L G u m k (y j) i)).det := by
  have hpacket := progressionNormalizationBlock_packet_det_dvd hd k t s q m
    hcard hE L hL hL0 G F u y hyF hq hlocal
  have hmixed := progressionNormalizationBlock_mixedPrimeProduct_det_dvd k m P hP hPm
    L hL hL0 G F u y hyF
  have hcop : IsCoprime
      ((q : ℤ) ^ (affinePlaneMonomialWeight t + (t + 1) * s))
      (∏ p ∈ P, (p : ℤ) ^ progressionHypersurfaceSmoothResidueExponent p F u m y) := by
    apply IsCoprime.prod_right
    intro p hp
    have hqp : Nat.Coprime q p :=
      ((Nat.Prime.coprime_iff_not_dvd (hP p hp)).mpr (hPq p hp)).symm
    exact (Nat.Coprime.pow (affinePlaneMonomialWeight t + (t + 1) * s)
      (progressionHypersurfaceSmoothResidueExponent p F u m y) hqp).isCoprime
  exact hcop.mul_dvd hpacket hmixed

/-- The simultaneous arithmetic gains exceed the same two-radius
archimedean determinant bound used by each construction separately. -/
theorem progressionNormalizationBlock_det_eq_zero_of_packet_mixedResidues
    {d : ℕ} (hd : 0 < d) (b k t s q m D H R : ℕ)
    (hcard : Fintype.card (Fin d × AffinePlaneMonomialIndex k) = affinePlaneMonomialCount t + s)
    (hE : 0 < affinePlaneMonomialWeight t + (t + 1) * s)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hPm : ∀ p ∈ P, ¬ p ∣ m) (hPq : ∀ p ∈ P, ¬ p ∣ q)
    (L : Fin 3 → MvPolynomial (Fin 4) ℤ)
    (hL : ∀ i, (L i).IsHomogeneous 1) (hL0 : L 0 = X 0)
    (G : Fin d → MvPolynomial (Fin 4) ℤ)
    (F : MvPolynomial (Fin 4) ℤ) (u : Fin 3 → ℤ)
    (y : Fin d × AffinePlaneMonomialIndex k → Fin 3 → ℤ)
    (hyF : ∀ j, eval (progressionHomogeneousPoint u m (y j)) F = 0)
    (hq : Squarefree q)
    (hlocal : ∀ p, p.Prime → p ∣ q → ¬ p ∣ m ∧
      ∃ (z : Fin 3 → ℤ) (v : Fin 3),
        (∀ j i, (p : ℤ) ∣ y j i - z i) ∧
        (eval (fun i => u i + (m : ℤ) * z i)
          (pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0)
    (hG : ∀ j i, (eval (progressionHomogeneousPoint u m (y j)) (G i)).natAbs ≤ D * H ^ b)
    (hparams : ∀ j i, (progressionParameterValues L (y j) i).natAbs ≤ R)
    (hlarge : (d * affinePlaneMonomialCount k).factorial *
        (D * H ^ b) ^ (d * affinePlaneMonomialCount k) *
          R ^ (d * affinePlaneMonomialWeight k) <
      q ^ (affinePlaneMonomialWeight t + (t + 1) * s) *
        (∏ p ∈ P, p ^ progressionHypersurfaceSmoothResidueExponent p F u m y)) :
    (Matrix.of (fun j i => progressionNormalizationBlockEntry L G u m k (y j) i)).det = 0 := by
  have hdiv := progressionNormalizationBlock_packet_mixedPrimeProduct_det_dvd hd k t s q m
    hcard hE P hP hPm hPq L hL hL0 G F u y hyF hq hlocal
  apply TangentMinors.eq_zero_of_dvd_of_natAbs_lt hdiv
  simpa only [← Nat.cast_pow, ← Nat.cast_prod, ← Nat.cast_mul, Int.natAbs_natCast] using
    (progressionNormalizationBlock_det_natAbs_le L G u m k D H b R y hG hparams).trans_lt hlarge

/-- A proper auxiliary for an actual common packet, using also the global
mixed-prime gains of every selected minor. The forms remain outside the
original rational surface ideal, and vanish at `(1,u+m*y)`.
All prime disjointness and prime-to-scale conditions are explicit. -/
theorem exists_progression_auxiliary_of_packet_mixedResidue_minors
    {d : ℕ} (hd : 0 < d) (b k t s D H R q m S : ℕ) (hm : m ≠ 0)
    (hcard : Fintype.card (Fin d × AffinePlaneMonomialIndex k) = affinePlaneMonomialCount t + s)
    (hE : 0 < affinePlaneMonomialWeight t + (t + 1) * s)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hPm : ∀ p ∈ P, ¬ p ∣ m) (hPq : ∀ p ∈ P, ¬ p ∣ q)
    (I : Ideal (MvPolynomial (Fin 4) ℚ))
    (L : Fin 3 → MvPolynomial (Fin 4) ℤ)
    (hL : ∀ i, (L i).IsHomogeneous 1) (hL0 : L 0 = X 0)
    (G : Fin d → MvPolynomial (Fin 4) ℤ) (hGhom : ∀ i, (G i).IsHomogeneous b)
    (hLI : LinearIndependent ℚ (fun p : Fin d × AffinePlaneMonomialIndex k =>
      Ideal.Quotient.mk I (MvPolynomial.map (Int.castRingHom ℚ)
        (normalizationSurfaceBlockForm L G k p))))
    (F : MvPolynomial (Fin 4) ℤ) (u : Fin 3 → ℤ) (y : Fin S → Fin 3 → ℤ)
    (hyF : ∀ j, eval (progressionHomogeneousPoint u m (y j)) F = 0)
    (hq : Squarefree q)
    (hlocal : ∀ p, p.Prime → p ∣ q → ¬ p ∣ m ∧
      ∃ (z : Fin 3 → ℤ) (v : Fin 3),
        (∀ j i, (p : ℤ) ∣ y j i - z i) ∧
        (eval (fun i => u i + (m : ℤ) * z i)
          (pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0)
    (hG : ∀ j i, (eval (progressionHomogeneousPoint u m (y j)) (G i)).natAbs ≤ D * H ^ b)
    (hparams : ∀ j i, (progressionParameterValues L (y j) i).natAbs ≤ R)
    (hlarge : ∀ select : Fin d × AffinePlaneMonomialIndex k → Fin S,
      Function.Injective select →
      (d * affinePlaneMonomialCount k).factorial *
          (D * H ^ b) ^ (d * affinePlaneMonomialCount k) *
            R ^ (d * affinePlaneMonomialWeight k) <
        q ^ (affinePlaneMonomialWeight t + (t + 1) * s) *
          (∏ p ∈ P, p ^ progressionHypersurfaceSmoothResidueExponent p F u m (y ∘ select))) :
    ∃ Q : MvPolynomial (Fin 4) ℚ, Q.IsHomogeneous (b + k) ∧ Q ∉ I ∧
      ∀ j, eval (fun i => (progressionHomogeneousPoint u m (y j) i : ℚ)) Q = 0 := by
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
    have hselected : ∀ p, p.Prime → p ∣ q → ¬ p ∣ m ∧
        ∃ (z : Fin 3 → ℤ) (v : Fin 3),
          (∀ j i, (p : ℤ) ∣ y (select j) i - z i) ∧
          (eval (fun i => u i + (m : ℤ) * z i)
            (pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0 := by
      intro p hp hpq
      obtain ⟨hpm, z, v, hyz, hzJ⟩ := hlocal p hp hpq
      exact ⟨hpm, z, v, fun j i => hyz (select j) i, hzJ⟩
    have hz := progressionNormalizationBlock_det_eq_zero_of_packet_mixedResidues hd b k t s q m D H R
      hcard hE P hP hPm hPq L hL hL0 G F u (y ∘ select) (fun j => hyF (select j))
      hq hselected (fun j i => hG (select j) i) (fun j i => hparams (select j) i)
      (hlarge select hselect)
    let Z : Matrix ι ι ℤ := Matrix.of (fun i j =>
      progressionNormalizationBlockEntry L G u m k (y (select j)) i)
    have hZ : Z.det = 0 := by
      change Z.transpose.det = 0 at hz
      simpa only [Matrix.det_transpose] using hz
    let Q : Matrix ι ι ℚ := Matrix.of (fun i j =>
      eval (fun a => (progressionHomogeneousPoint u m (y (select j)) a : ℚ))
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
