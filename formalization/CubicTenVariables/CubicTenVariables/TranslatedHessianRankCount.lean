import CubicTenVariables.UniformHomogeneousPerturbationCount
import CubicTenVariables.TranslatedHessianLeadingGeometry

/-!
# Uniform translated Hessian rank counts in ten variables

The fixed leading minors, their proved rational dimensions, and the uniform
lower-degree perturbation theorem give the manuscript's translated rank
estimate. One constant precedes every prime, arbitrary matrix shift and rank.
The counted points are not restricted to the cubic. No literature proposition
or finite-field point-count estimate is assumed.
-/

noncomputable section
namespace CubicTenVariables.TranslatedHessianRankCount
open MvPolynomial HessianTheorem11 TranslatedHessianMinors TranslatedHessianLeadingGeometry
open scoped BigOperators

/-- Actual points of the translated rank-at-most locus, including points
off the cubic and nonsymmetric matrix translations. -/
def count (F : MvPolynomial (Fin 10) ℤ) (p : ℕ) [Fact p.Prime]
    (T : Matrix (Fin 10) (Fin 10) (ZMod p)) (r : ℕ) : ℕ :=
  Nat.card {x : Fin 10 → ZMod p //
    (T + hessian (map (Int.castRingHom (ZMod p)) F) x).rank ≤ r}

/-- For one rank label, the constant precedes both the prime and every
matrix translation over its prime field. -/
theorem exists_fixed_rank_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F)) (r : ℕ) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      ∀ T : Matrix (Fin 10) (Fin 10) (ZMod p), count F p T r ≤ C*p^(tauNat r) := by
  classical
  let f : MinorIndex 10 r → MvPolynomial (Fin 10) ℤ := equation (hessianPolynomial F)
  have hhom : ∀ i, (f i).IsHomogeneous (degree i) :=
    equation_isHomogeneous _ (hessian_entries_isHomogeneous F hF)
  have heq : Ideal.span (Set.range (fun i => map (Int.castRingHom ℚ) (f i))) =
      rationalIdeal F r := by
    simp only [f, map_hessian_equation, rationalIdeal]
  obtain ⟨C, hC, hc⟩ := UniformHomogeneousPerturbationCount.exists_uniform_bound
    f degree hhom (heq.symm ▸ rationalIdeal_ne_top F hF r)
    (heq.symm ▸ quotient_dimension_le F hF hA r)
  refine ⟨C, hC, ?_⟩
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  intro T
  let f' : MinorIndex 10 r → MvPolynomial (Fin 10) (ZMod p) :=
    translatedEquation (hessianPolynomial (map (Int.castRingHom (ZMod p)) F)) T
  have hpert : ∀ i, (f' i - map (Int.castRingHom (ZMod p)) (f i)).totalDegree < degree i :=
    specialized_hessian_lower_degree (Int.castRingHom (ZMod p)) F hF T
  have hcount : count F p T r =
      Nat.card {x : Fin 10 → ZMod p // ∀ i, eval x (f' i) = 0} := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro x
    exact (specialized_hessian_zero_iff (Int.castRingHom (ZMod p)) F T r x).symm
  rw [hcount]
  exact hc p hp f' hpert

/-- The exact source endpoint, uniform in every prime, matrix and rank.
Ranks at least ten are included with the ambient exponent ten. -/
theorem exists_uniform_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      ∀ (T : Matrix (Fin 10) (Fin 10) (ZMod p)) (r : ℕ),
        count F p T r ≤ C*p^(tauNat r) := by
  classical
  choose C hC hc using fun r : Fin 10 => exists_fixed_rank_bound F hF hA r.val
  let A : ℕ := 1 + ∑ r, C r
  refine ⟨A, by dsimp [A]; omega, ?_⟩
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  intro T r
  by_cases hr : r < 10
  · have hle : C ⟨r, hr⟩ ≤ A := by
      have hsum : C ⟨r, hr⟩ ≤ ∑ j, C j :=
        Finset.single_le_sum (fun j _ => Nat.zero_le (C j))
          (Finset.mem_univ (⟨r, hr⟩ : Fin 10))
      dsimp [A]
      omega
    exact (hc ⟨r, hr⟩ p hp T).trans (Nat.mul_le_mul_right _ hle)
  · have hτ : tauNat r = 10 := by simp [tauNat, hr, show r ≠ 0 by omega]
    rw [hτ]
    calc
      count F p T r ≤ Nat.card (Fin 10 → ZMod p) :=
        Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      _ = p^10 := by rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
      _ ≤ A*p^10 := Nat.le_mul_of_pos_left _ (by dsimp [A]; omega)

/-- The same result with every Hessian entry and every counted point
displayed explicitly, and the source exponent written as a natural number. -/
theorem exists_literal_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      ∀ (T : Matrix (Fin 10) (Fin 10) (ZMod p)) (r : ℕ),
        Nat.card {x : Fin 10 → ZMod p //
          Matrix.rank (fun (i j : Fin 10) => T i j + eval₂ (Int.castRingHom (ZMod p)) x
            (pderiv j (pderiv i F))) ≤ r} ≤
          C*p^(if r = 0 then 0 else if r < 10 then min (r+2) 9 else 10) := by
  obtain ⟨C, hC, hc⟩ := exists_uniform_bound F hF hA
  refine ⟨C, hC, ?_⟩
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  intro T r
  have hm (x : Fin 10 → ZMod p) :
      T + hessian (map (Int.castRingHom (ZMod p)) F) x =
        fun (i j : Fin 10) => T i j + eval₂ (Int.castRingHom (ZMod p)) x
          (pderiv j (pderiv i F)) := by
    ext i j
    simp [hessian, hessianPolynomial, pderiv_map, eval_map]
  simpa only [count, hm, tauNat] using hc p hp T r

end CubicTenVariables.TranslatedHessianRankCount
