import TranslatedDepthSeven.HomogeneousNormalizationRankDegreeEqualityInternal
import TranslatedDepthSeven.NormalizationSurfaceBlockEvaluation
import TranslatedDepthSeven.IntegralHomogeneousIdealModel
import TranslatedDepthSeven.CharacteristicPolynomialHeight

/-!
# Actual integral forms in a full surface normalization block

The generic-rank lattice is lifted to homogeneous rational polynomials and
its denominators are cleared.  The resulting fixed integral forms have
explicit coefficient constants and yield independent blocks in every degree.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

theorem map_normalizationSurfaceBlockForm_intCast
    {σ : Type*} {d : ℕ} (L : Fin 3 → MvPolynomial σ ℤ)
    (G : Fin d → MvPolynomial σ ℤ) (k : ℕ)
    (p : Fin d × AffinePlaneMonomialIndex k) :
    MvPolynomial.map (Int.castRingHom ℚ) (normalizationSurfaceBlockForm L G k p) =
      normalizationSurfaceBlockForm
        (fun i => MvPolynomial.map (Int.castRingHom ℚ) (L i))
        (fun i => MvPolynomial.map (Int.castRingHom ℚ) (G i)) k p := by
  unfold normalizationSurfaceBlockForm
  rw [map_mul]
  congr 1
  unfold affinePlaneHomogeneousMonomial
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
  simp [Finsupp.prod]

theorem linearIndependent_quotient_normalizationSurfaceBlock
    {σ : Type*} (I : Ideal (MvPolynomial σ ℚ)) {d : ℕ}
    (L : Fin 3 → MvPolynomial σ ℚ) (G : Fin d → MvPolynomial σ ℚ)
    (hG : letI : Algebra (MvPolynomial (Fin 3) ℚ) (MvPolynomial σ ℚ ⧸ I) :=
      (linearNormalizationHomFin ℚ σ I L).toRingHom.toAlgebra
      LinearIndependent (MvPolynomial (Fin 3) ℚ) (fun i => Ideal.Quotient.mk I (G i)))
    (k : ℕ) :
    LinearIndependent ℚ (fun p : Fin d × AffinePlaneMonomialIndex k =>
      Ideal.Quotient.mk I (normalizationSurfaceBlockForm L G k p)) := by
  let B := MvPolynomial (Fin 3) ℚ
  let A := MvPolynomial σ ℚ ⧸ I
  letI : Algebra B A := (linearNormalizationHomFin ℚ σ I L).toRingHom.toAlgebra
  have h := linearIndependent_normalizationSurfaceBlock ℚ A (Fin d)
    (fun i => Ideal.Quotient.mk I (G i)) hG k
  convert h using 1
  funext p
  change Ideal.Quotient.mk I (G p.1 * MvPolynomial.aeval L _) =
    Ideal.Quotient.mk I (MvPolynomial.aeval L _) * Ideal.Quotient.mk I (G p.1)
  rw [map_mul, mul_comm]

/-- Clearing denominators of homogeneous representatives preserves the
independence of every complete block. -/
theorem linearIndependent_cleared_normalizationSurfaceBlock
    {σ : Type*} (I : Ideal (MvPolynomial σ ℚ)) {d : ℕ}
    (L : Fin 3 → MvPolynomial σ ℤ) (G : Fin d → MvPolynomial σ ℚ)
    (hG : letI : Algebra (MvPolynomial (Fin 3) ℚ) (MvPolynomial σ ℚ ⧸ I) :=
      (linearNormalizationHomFin ℚ σ I
        (fun i => MvPolynomial.map (Int.castRingHom ℚ) (L i))).toRingHom.toAlgebra
      LinearIndependent (MvPolynomial (Fin 3) ℚ) (fun i => Ideal.Quotient.mk I (G i)))
    (k : ℕ) :
    LinearIndependent ℚ (fun p : Fin d × AffinePlaneMonomialIndex k =>
      Ideal.Quotient.mk I (MvPolynomial.map (Int.castRingHom ℚ)
        (normalizationSurfaceBlockForm L (fun i => clearRationalMvPolynomial (G i)) k p))) := by
  have h := linearIndependent_quotient_normalizationSurfaceBlock I
    (fun i => MvPolynomial.map (Int.castRingHom ℚ) (L i)) G hG k
  have hs := linearIndependent_smul_of_ne_zero h
    (fun p : Fin d × AffinePlaneMonomialIndex k =>
      (mvPolynomialRationalCommonDenominator (G p.1) : ℚ))
    (fun p => by
      dsimp only
      exact_mod_cast (mvPolynomialRationalCommonDenominator_pos (G p.1)).ne')
  convert hs using 1
  funext p
  rw [map_normalizationSurfaceBlockForm_intCast]
  simp only [normalizationSurfaceBlockForm, map_clearRationalMvPolynomial,
    map_mul]
  simp [Algebra.smul_def, mul_assoc]

/-- One fixed coefficient constant works at all integer points and box sizes. -/
theorem exists_uniform_integral_homogeneous_family_height
    {σ : Type*} {d b : ℕ} (G : Fin d → MvPolynomial σ ℤ)
    (hG : ∀ i, (G i).IsHomogeneous b) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ (B : ℕ), 1 ≤ B → ∀ (y : σ → ℤ),
      (∀ j, (y j).natAbs ≤ B) → ∀ i, (MvPolynomial.eval y (G i)).natAbs ≤ D * B ^ b := by
  classical
  let D := max 1 (Finset.univ.sup fun i =>
    (G i).support.card * mvPolynomialCoefficientNatAbsMax (G i))
  refine ⟨D, Nat.le_max_left _ _, ?_⟩
  intro B hB y hy i
  have he := eval_natAbs_le_support_mul_coeff_mul_pow_generic (G i) y
    (fun m hm => coeff_natAbs_le_mvPolynomialCoefficientNatAbsMax (G i) hm)
    (hG i).totalDegree_le hy
  rw [max_eq_right hB] at he
  exact he.trans (Nat.mul_le_mul_right (B ^ b)
    ((Finset.le_sup (f := fun i =>
      (G i).support.card * mvPolynomialCoefficientNatAbsMax (G i))
        (Finset.mem_univ i)).trans (Nat.le_max_right _ _)))

/-- A finite injective integral linear normalization of a rational projective
surface produces actual integral independent blocks with exactly `d` rows.
The forms and height constant are chosen before every block degree and box. -/
theorem exists_integral_surfaceNormalizationBlock
    {N d : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ ℚ))
    (hdegree : HasProjectiveDimensionDegree I 2 d)
    (L : Fin 3 → MvPolynomial (Fin (N + 1)) ℤ)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (hinj : Function.Injective (linearNormalizationHomFin ℚ (Fin (N + 1)) I
      (fun i => MvPolynomial.map (Int.castRingHom ℚ) (L i))))
    (hfinite : (linearNormalizationHomFin ℚ (Fin (N + 1)) I
      (fun i => MvPolynomial.map (Int.castRingHom ℚ) (L i))).Finite) :
    ∃ b D : ℕ, 1 ≤ D ∧ ∃ G : Fin d → MvPolynomial (Fin (N + 1)) ℤ,
      (∀ i, (G i).IsHomogeneous b) ∧
      (∀ k, LinearIndependent ℚ (fun p : Fin d × AffinePlaneMonomialIndex k =>
        Ideal.Quotient.mk I (MvPolynomial.map (Int.castRingHom ℚ)
          (normalizationSurfaceBlockForm L G k p)))) ∧
      (∀ B : ℕ, 1 ≤ B → ∀ y : Fin (N + 1) → ℤ,
        (∀ j, (y j).natAbs ≤ B) → ∀ i,
          (MvPolynomial.eval y (G i)).natAbs ≤ D * B ^ b) := by
  classical
  let LQ := fun i => MvPolynomial.map (Int.castRingHom ℚ) (L i)
  have hLQ : ∀ i, (LQ i).IsHomogeneous 1 := fun i => (hL i).map _
  let norm : HomogeneousLinearNormalizationData I := {
    parameterCount := 3
    forms := LQ
    forms_isHomogeneous := hLQ
    injective := hinj
    finite := hfinite }
  let B := MvPolynomial (Fin 3) ℚ
  let A := MvPolynomial (Fin (N + 1)) ℚ ⧸ I
  letI : Algebra B A := (linearNormalizationHomFin ℚ (Fin (N + 1)) I LQ).toRingHom.toAlgebra
  have hrank : Module.finrank (FractionRing B)
      (LocalizedModule (nonZeroDivisors B) A) = d :=
    (homogeneousLinearNormalization_genericRank_eq_projectiveDegree
      I hprime hhom norm hdegree).2
  obtain ⟨M, t, degree, ht, hspan⟩ :=
    exists_homogeneous_generators_of_finite_linearNormalization_fin
      ℚ (Fin (N + 1)) I LQ hfinite
  have hx := exists_equalDegree_genericRank_lattice_sandwich_fin
    ℚ (Fin (N + 1)) I LQ hLQ hfinite t degree ht hspan
  dsimp only at hx
  change Module.finrank (FractionRing (MvPolynomial (Fin 3) ℚ))
    (LocalizedModule (nonZeroDivisors (MvPolynomial (Fin 3) ℚ))
      (MvPolynomial (Fin (N + 1)) ℚ ⧸ I)) = d at hrank
  rw [hrank] at hx
  obtain ⟨b, c, x, _hc, hxLI, hxhom, _hspan⟩ := hx
  have hreps (i : Fin d) : ∃ g : MvPolynomial (Fin (N + 1)) ℚ,
      g.IsHomogeneous b ∧ Ideal.Quotient.mk I g = x i := by
    obtain ⟨g, hg, he⟩ := Submodule.mem_map.mp (hxhom i)
    exact ⟨g, hg, he⟩
  choose G hGhom hGeq using hreps
  have hGLI : LinearIndependent B (fun i => Ideal.Quotient.mk I (G i)) := by
    simpa only [hGeq] using hxLI
  let GZ := fun i => clearRationalMvPolynomial (G i)
  have hGZ : ∀ i, (GZ i).IsHomogeneous b :=
    fun i => clearRationalMvPolynomial_isHomogeneous (hGhom i)
  obtain ⟨D, hD, hheight⟩ := exists_uniform_integral_homogeneous_family_height GZ hGZ
  exact ⟨b, D, hD, GZ, hGZ,
    fun k => linearIndependent_cleared_normalizationSurfaceBlock I L G hGLI k, hheight⟩

end
end TranslatedDepthSeven
