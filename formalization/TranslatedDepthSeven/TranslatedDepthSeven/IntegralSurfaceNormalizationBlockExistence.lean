import TranslatedDepthSeven.IntegralSurfaceNormalizationBlock
import TranslatedDepthSeven.BoundedIntegralDistinguishedNormalizationInternal

/-!
# Independent integral blocks chosen from a fixed projective surface

Only a literal homogeneous prime ideal, its dimension/degree certificate,
and the nonempty first chart are inputs. The normalization and all block
forms are constructed before any box, point family, modulus or block degree.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

def integralSurfaceNormalizationForms {n : ℕ}
    (A : Matrix (Fin 3) (Fin n) ℤ) (i : Fin 3) : MvPolynomial (Fin n) ℤ :=
  ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j

theorem integralSurfaceNormalizationForms_map {n : ℕ}
    (A : Matrix (Fin 3) (Fin n) ℤ) (i : Fin 3) :
    MvPolynomial.map (Int.castRingHom ℚ) (integralSurfaceNormalizationForms A i) =
      indexedMatrixRowLinearPolynomial (A.map (Int.castRingHom ℚ)) i := by
  simp [integralSurfaceNormalizationForms, indexedMatrixRowLinearPolynomial,
    Matrix.map_apply]

theorem integralSurfaceNormalizationForms_isHomogeneous {n : ℕ}
    (A : Matrix (Fin 3) (Fin n) ℤ) (i : Fin 3) :
    (integralSurfaceNormalizationForms A i).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum Finset.univ _ 1
  intro j _hj
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

theorem integralSurfaceNormalizationForms_first {N : ℕ}
    (A : Matrix (Fin 3) (Fin (N + 1)) ℤ)
    (hfirst : ∀ j, A 0 j = if j = 0 then 1 else 0) :
    integralSurfaceNormalizationForms A 0 = MvPolynomial.X 0 := by
  simp [integralSurfaceNormalizationForms, hfirst]

theorem integralSurfaceNormalizationForms_eval_natAbs_le {n C B : ℕ}
    (A : Matrix (Fin 3) (Fin n) ℤ)
    (hA : ∀ i, ∑ j, (A i j).natAbs ≤ C)
    (y : Fin n → ℤ) (hy : ∀ j, (y j).natAbs ≤ B) (i : Fin 3) :
    (MvPolynomial.eval y (integralSurfaceNormalizationForms A i)).natAbs ≤ C * B := by
  simp only [integralSurfaceNormalizationForms, map_sum, map_mul, eval_C, eval_X]
  calc
    (∑ j, A i j * y j).natAbs ≤ ∑ j, (A i j * y j).natAbs :=
      int_natAbs_sum_le_sum_natAbs _ _
    _ = ∑ j, (A i j).natAbs * (y j).natAbs := by simp only [Int.natAbs_mul]
    _ ≤ ∑ j, (A i j).natAbs * B := by
      exact Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_left _ (hy j))
    _ = (∑ j, (A i j).natAbs) * B := by rw [Finset.sum_mul]
    _ ≤ C * B := Nat.mul_le_mul_right B (hA i)

/-- The degree-many independent integral forms and their fixed height
constant are produced from the surface, not supplied as assumptions. -/
theorem exists_fixed_integral_surfaceNormalizationBlock
    {N d : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ ℚ))
    (hX : MvPolynomial.X 0 ∉ I)
    (hdegree : HasProjectiveDimensionDegree I 2 d) :
    ∃ b D : ℕ, ∃ L : Fin 3 → MvPolynomial (Fin (N + 1)) ℤ,
      ∃ G : Fin d → MvPolynomial (Fin (N + 1)) ℤ,
      1 ≤ D ∧ L 0 = MvPolynomial.X 0 ∧
      (∀ i, (L i).IsHomogeneous 1) ∧ (∀ i, (G i).IsHomogeneous b) ∧
      (∀ k, LinearIndependent ℚ (fun p : Fin d × AffinePlaneMonomialIndex k =>
        Ideal.Quotient.mk I (MvPolynomial.map (Int.castRingHom ℚ)
          (normalizationSurfaceBlockForm L G k p)))) ∧
      (∀ B : ℕ, 1 ≤ B → ∀ y : Fin (N + 1) → ℤ,
        (∀ j, (y j).natAbs ≤ B) → ∀ i,
          (MvPolynomial.eval y (G i)).natAbs ≤ D * B ^ b) ∧
      (∀ (B : ℕ) (y : Fin (N + 1) → ℤ),
        (∀ j, (y j).natAbs ≤ B) → ∀ i,
          (MvPolynomial.eval y (L i)).natAbs ≤ (d + 1) ^ N * B) := by
  obtain ⟨A, hA, hfirst, hinj, hfinite⟩ :=
    exists_boundedIntegralDistinguishedNormalization N I hprime hhom hX hdegree (le_refl d)
  let L := integralSurfaceNormalizationForms A
  have hL : ∀ i, (L i).IsHomogeneous 1 :=
    integralSurfaceNormalizationForms_isHomogeneous A
  have hmap : (fun i => MvPolynomial.map (Int.castRingHom ℚ) (L i)) =
      indexedMatrixRowLinearPolynomial (A.map (Int.castRingHom ℚ)) :=
    funext (integralSurfaceNormalizationForms_map A)
  have hinj' : Function.Injective (linearNormalizationHomFin ℚ (Fin (N + 1)) I
      (fun i => MvPolynomial.map (Int.castRingHom ℚ) (L i))) := by
    rw [hmap]
    exact hinj
  have hfinite' : (linearNormalizationHomFin ℚ (Fin (N + 1)) I
      (fun i => MvPolynomial.map (Int.castRingHom ℚ) (L i))).Finite := by
    rw [hmap]
    exact hfinite
  obtain ⟨b, D, hD, G, hG, hLI, hheight⟩ :=
    exists_integral_surfaceNormalizationBlock I hprime hhom hdegree L hL hinj' hfinite'
  exact ⟨b, D, L, G, hD, integralSurfaceNormalizationForms_first A hfirst,
    hL, hG, hLI, hheight,
    fun B y hy i => integralSurfaceNormalizationForms_eval_natAbs_le A hA y hy i⟩

end
end TranslatedDepthSeven
