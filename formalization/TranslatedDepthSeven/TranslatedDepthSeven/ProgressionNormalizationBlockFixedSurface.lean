import TranslatedDepthSeven.ProgressionNormalizationBlockRational
import TranslatedDepthSeven.IntegralSurfaceNormalizationBlockExistence

/-! All normalization data and coefficient constants are chosen from one
fixed surface before the center, progression modulus, degree and boxes. -/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000

/-- The two-radius determinant estimate from literal coordinate bounds.
The bound for the linear forms is needed on the direction vector `(0,y)`,
so it is independent of both the center and the progression modulus. -/
theorem progressionNormalizationBlock_det_natAbs_le_of_box_bounds {N d b D C : ℕ}
    (L : Fin 3 → MvPolynomial (Fin (N + 1)) ℤ)
    (G : Fin d → MvPolynomial (Fin (N + 1)) ℤ)
    (hGheight : ∀ B : ℕ, 1 ≤ B → ∀ x : Fin (N + 1) → ℤ,
      (∀ i, (x i).natAbs ≤ B) → ∀ a, (MvPolynomial.eval x (G a)).natAbs ≤ D * B ^ b)
    (hLheight : ∀ (B : ℕ) (x : Fin (N + 1) → ℤ),
      (∀ i, (x i).natAbs ≤ B) → ∀ a, (MvPolynomial.eval x (L a)).natAbs ≤ C * B)
    (u : Fin N → ℤ) (m k H B : ℕ)
    (y : Fin d × AffinePlaneMonomialIndex k → Fin N → ℤ)
    (hH : 1 ≤ H)
    (hsource : ∀ j i, (progressionHomogeneousPoint u m (y j) i).natAbs ≤ H)
    (hdisplacement : ∀ j i, (y j i).natAbs ≤ B) :
    (Matrix.of (fun j i => progressionNormalizationBlockEntry L G u m k (y j) i)).det.natAbs ≤
      (d * affinePlaneMonomialCount k).factorial *
        (D * H ^ b) ^ (d * affinePlaneMonomialCount k) *
          (C * B) ^ (d * affinePlaneMonomialWeight k) := by
  apply progressionNormalizationBlock_det_natAbs_le L G u m k D H b (C * B) y
  · exact fun j i => hGheight H hH _ (hsource j) i
  · intro j i
    apply hLheight B (progressionHomogeneousDirection (y j))
    intro a
    refine Fin.cases ?_ (fun a => ?_) a
    · simp [progressionHomogeneousDirection]
    · exact hdisplacement j a

/-- Actual fixed integral normalization forms and auxiliary forms exist
with independent rational progression blocks for every center and every
nonzero modulus.  The height constants precede all those quantifiers. -/
theorem exists_fixed_progressionNormalizationBlock
    {N d : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ ℚ))
    (hX : MvPolynomial.X 0 ∉ I)
    (hdegree : HasProjectiveDimensionDegree I 2 d) :
    ∃ b D : ℕ, ∃ L : Fin 3 → MvPolynomial (Fin (N + 1)) ℤ,
      ∃ G : Fin d → MvPolynomial (Fin (N + 1)) ℤ,
      1 ≤ D ∧ L 0 = MvPolynomial.X 0 ∧
      (∀ i, (L i).IsHomogeneous 1) ∧ (∀ i, (G i).IsHomogeneous b) ∧
      (∀ (u : Fin N → ℤ) (m : ℕ), m ≠ 0 → ∀ k,
        LinearIndependent ℚ (fun p : Fin d × AffinePlaneMonomialIndex k =>
          Ideal.Quotient.mk I (progressionRationalBlockForm L G u m k p))) ∧
      (∀ B : ℕ, 1 ≤ B → ∀ y : Fin (N + 1) → ℤ,
        (∀ j, (y j).natAbs ≤ B) → ∀ i,
          (MvPolynomial.eval y (G i)).natAbs ≤ D * B ^ b) ∧
      (∀ (B : ℕ) (y : Fin (N + 1) → ℤ),
        (∀ j, (y j).natAbs ≤ B) → ∀ i,
          (MvPolynomial.eval y (L i)).natAbs ≤ (d + 1) ^ N * B) := by
  obtain ⟨b, D, L, G, hD, hL0, hL, hG, hLI, hGheight, hLheight⟩ :=
    exists_fixed_integral_surfaceNormalizationBlock I hprime hhom hX hdegree
  exact ⟨b, D, L, G, hD, hL0, hL, hG,
    fun u m hm k => linearIndependent_progressionRationalBlockForm I L G u m k hm (hLI k),
    hGheight, hLheight⟩

end
end TranslatedDepthSeven
