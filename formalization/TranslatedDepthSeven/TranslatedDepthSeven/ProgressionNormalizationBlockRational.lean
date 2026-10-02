import TranslatedDepthSeven.ProgressionNormalizationBlockIndependence
import TranslatedDepthSeven.ProgressionNormalizationBlockEvaluation

/-! Rational normalized forms and their exact integral evaluations on a
fixed progression.  All quotient independence remains modulo the original
ideal; the auxiliary forms are unchanged. -/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000

def progressionRationalParameters {N : ℕ}
    (L : Fin 3 → MvPolynomial (Fin (N + 1)) ℤ) (u : Fin N → ℤ) (m : ℕ) :
    Fin 3 → MvPolynomial (Fin (N + 1)) ℚ :=
  ![MvPolynomial.map (Int.castRingHom ℚ) (L 0),
    C (m : ℚ)⁻¹ * MvPolynomial.map (Int.castRingHom ℚ) (progressionNumeratorParameters L u 1),
    C (m : ℚ)⁻¹ * MvPolynomial.map (Int.castRingHom ℚ) (progressionNumeratorParameters L u 2)]

def progressionRationalBlockForm {N d : ℕ}
    (L : Fin 3 → MvPolynomial (Fin (N + 1)) ℤ)
    (G : Fin d → MvPolynomial (Fin (N + 1)) ℤ)
    (u : Fin N → ℤ) (m k : ℕ) (p : Fin d × AffinePlaneMonomialIndex k) :
    MvPolynomial (Fin (N + 1)) ℚ :=
  normalizationSurfaceBlockForm (progressionRationalParameters L u m)
    (fun i => MvPolynomial.map (Int.castRingHom ℚ) (G i)) k p

private theorem progression_eval_map_intCast {σ : Type*}
    (x : σ → ℤ) (P : MvPolynomial σ ℤ) :
    MvPolynomial.eval (fun i => (x i : ℚ)) (MvPolynomial.map (Int.castRingHom ℚ) P) =
      (MvPolynomial.eval x P : ℚ) := by
  rw [MvPolynomial.eval_map]
  exact (MvPolynomial.eval₂_comp (Int.castRingHom ℚ) x P).symm

theorem eval_progressionRationalParameters {N : ℕ}
    (L : Fin 3 → MvPolynomial (Fin (N + 1)) ℤ)
    (hL : ∀ i, (L i).IsHomogeneous 1) (hL0 : L 0 = X 0)
    (u y : Fin N → ℤ) (m : ℕ) (hm : m ≠ 0) :
    (fun i => MvPolynomial.eval (fun a => (progressionHomogeneousPoint u m y a : ℚ))
      (progressionRationalParameters L u m i)) =
        ![1, (progressionParameterValues L y 0 : ℚ),
          (progressionParameterValues L y 1 : ℚ)] := by
  have he := eval_progressionNumeratorParameters L hL hL0 u y m
  have h1 := congrFun he 1
  have h2 := congrFun he 2
  simp at h1 h2
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  funext i
  fin_cases i
  · simp [progressionRationalParameters, hL0, progressionHomogeneousPoint]
  · change MvPolynomial.eval _ (C (m : ℚ)⁻¹ *
        MvPolynomial.map (Int.castRingHom ℚ) (progressionNumeratorParameters L u 1)) = _
    rw [map_mul, eval_C, progression_eval_map_intCast, h1]
    simp [hmQ, ← mul_assoc]
  · change MvPolynomial.eval _ (C (m : ℚ)⁻¹ *
        MvPolynomial.map (Int.castRingHom ℚ) (progressionNumeratorParameters L u 2)) = _
    rw [map_mul, eval_C, progression_eval_map_intCast, h2]
    simp [hmQ, ← mul_assoc]

private theorem eval_aeval_affinePlaneHomogeneousMonomial_rat
    {σ : Type*} (L : Fin 3 → MvPolynomial σ ℚ)
    (y : σ → ℚ) (k : ℕ) (u : AffinePlaneMonomialIndex k) :
    MvPolynomial.eval y
        (MvPolynomial.aeval L (affinePlaneHomogeneousMonomial ℚ k u)) =
      MvPolynomial.eval y (L 0) ^ (k - u.1.1) *
        MvPolynomial.eval y (L 1) ^ u.2.1 *
          MvPolynomial.eval y (L 2) ^ (u.1.1 - u.2.1) := by
  rw [affinePlaneHomogeneousMonomial, MvPolynomial.aeval_monomial]
  simp only [map_one, one_mul]
  rw [Finsupp.prod_fintype]
  · rw [Fin.prod_univ_three]
    have hzero : (affinePlaneMonomialExponent k u) 0 = k - u.1.1 := by
      simp [affinePlaneMonomialExponent]
    have hone : (affinePlaneMonomialExponent k u) 1 = u.2.1 := by
      simp [affinePlaneMonomialExponent]
    have htwo : (affinePlaneMonomialExponent k u) 2 = u.1.1 - u.2.1 := by
      simp [affinePlaneMonomialExponent]
    rw [hzero, hone, htwo]
    simp
  · intro i
    simp

/-- The rational polynomial evaluates to the displayed integer, with no
rounding or divisibility assumption on the auxiliary forms. -/
theorem eval_progressionRationalBlockForm {N d : ℕ}
    (L : Fin 3 → MvPolynomial (Fin (N + 1)) ℤ)
    (hL : ∀ i, (L i).IsHomogeneous 1) (hL0 : L 0 = X 0)
    (G : Fin d → MvPolynomial (Fin (N + 1)) ℤ)
    (u : Fin N → ℤ) (m k : ℕ) (hm : m ≠ 0) (y : Fin N → ℤ)
    (p : Fin d × AffinePlaneMonomialIndex k) :
    MvPolynomial.eval (fun a => (progressionHomogeneousPoint u m y a : ℚ))
      (progressionRationalBlockForm L G u m k p) =
        (progressionNormalizationBlockEntry L G u m k y p : ℚ) := by
  rw [progressionRationalBlockForm, normalizationSurfaceBlockForm, map_mul,
    eval_aeval_affinePlaneHomogeneousMonomial_rat]
  have he := eval_progressionRationalParameters L hL hL0 u y m hm
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have h2 := congrFun he 2
  simp at h0 h1 h2
  rw [h0, h1, h2, progression_eval_map_intCast]
  simp [progressionNormalizationBlockEntry, mul_assoc]

theorem progressionRationalParameters_isHomogeneous {N : ℕ}
    (L : Fin 3 → MvPolynomial (Fin (N + 1)) ℤ)
    (hL : ∀ i, (L i).IsHomogeneous 1) (u : Fin N → ℤ) (m : ℕ) :
    ∀ i, (progressionRationalParameters L u m i).IsHomogeneous 1 := by
  intro i
  fin_cases i
  · exact (hL 0).map _
  · exact (((hL 1).sub ((hL 0).C_mul _)).map _).C_mul _
  · exact (((hL 2).sub ((hL 0).C_mul _)).map _).C_mul _

theorem progressionRationalBlockForm_isHomogeneous {N d b : ℕ}
    (L : Fin 3 → MvPolynomial (Fin (N + 1)) ℤ)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (G : Fin d → MvPolynomial (Fin (N + 1)) ℤ) (hG : ∀ i, (G i).IsHomogeneous b)
    (u : Fin N → ℤ) (m k : ℕ) (p : Fin d × AffinePlaneMonomialIndex k) :
    (progressionRationalBlockForm L G u m k p).IsHomogeneous (b + k) :=
  normalizationSurfaceBlockForm_isHomogeneous _ _ b k
    (progressionRationalParameters_isHomogeneous L hL u m) (fun i => (hG i).map _) p

/-- The exact rational forms used in the evaluation identity remain
independent modulo the fixed original ideal. -/
theorem linearIndependent_progressionRationalBlockForm {N d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (L : Fin 3 → MvPolynomial (Fin (N + 1)) ℤ)
    (G : Fin d → MvPolynomial (Fin (N + 1)) ℤ)
    (u : Fin N → ℤ) (m k : ℕ) (hm : m ≠ 0)
    (hLI : LinearIndependent ℚ (fun p : Fin d × AffinePlaneMonomialIndex k =>
      Ideal.Quotient.mk I (MvPolynomial.map (Int.castRingHom ℚ)
        (normalizationSurfaceBlockForm L G k p)))) :
    LinearIndependent ℚ (fun p : Fin d × AffinePlaneMonomialIndex k =>
      Ideal.Quotient.mk I (progressionRationalBlockForm L G u m k p)) := by
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  simp_rw [map_normalizationSurfaceBlockForm_intCast] at hLI
  have h := linearIndependent_normalizedProgressionBlock I
    (fun i => MvPolynomial.map (Int.castRingHom ℚ) (L i))
    (fun i => MvPolynomial.map (Int.castRingHom ℚ) (G i))
    (fun i : Fin 2 => (MvPolynomial.eval (progressionHomogeneousCenter u) (L i.succ) : ℚ))
    (m : ℚ) hmQ k hLI
  have hforms : progressionRationalParameters L u m =
      ![MvPolynomial.map (Int.castRingHom ℚ) (L 0),
        C (m : ℚ)⁻¹ * (MvPolynomial.map (Int.castRingHom ℚ) (L 1) -
          C (MvPolynomial.eval (progressionHomogeneousCenter u) (L 1) : ℚ) *
            MvPolynomial.map (Int.castRingHom ℚ) (L 0)),
        C (m : ℚ)⁻¹ * (MvPolynomial.map (Int.castRingHom ℚ) (L 2) -
          C (MvPolynomial.eval (progressionHomogeneousCenter u) (L 2) : ℚ) *
            MvPolynomial.map (Int.castRingHom ℚ) (L 0))] := by
    funext i
    fin_cases i <;> simp [progressionRationalParameters, progressionNumeratorParameters]
  simpa only [progressionRationalBlockForm, hforms] using h

end
end TranslatedDepthSeven
