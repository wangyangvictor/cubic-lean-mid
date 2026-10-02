import CubicTenVariables.PrimeSumAdapter
import CubicTenVariables.PolynomialSingularLifts

/-! Exact lower-level zero counts among all higher-level representatives.
The right side counts literal residue roots; no analytic estimate is used. -/

noncomputable section
namespace CubicTenVariables.PrimePowerRootReduction
open MvPolynomial PrimePowerFibers
open scoped BigOperators

/-- A divisibility condition on integer representatives is the actual
lower-level polynomial equation after the canonical reduction map. -/
theorem dvd_eval_iff_reduced_zero {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (p : ℕ) [Fact p.Prime] {s t : ℕ} (hts : t ≤ s)
    (x : Fin n → Fin (p^s)) :
    ((p^t : ℕ) : ℤ) ∣ eval (fun i => ((x i).val : ℤ)) F ↔
      eval₂ (Int.castRingHom (ZMod (p^t)))
        (fun i => reduction p hts (PrimeSumAdapter.vectorResidueEquiv (p^s) n x i)) F = 0 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, SmoothResidueLifting.cast_eval_int]
  have hv (i : Fin n) : (((x i).val : ℤ) : ZMod (p^t)) =
      reduction p hts (PrimeSumAdapter.vectorResidueEquiv (p^s) n x i) := by
    simp only [PrimeSumAdapter.vectorResidueEquiv_apply, Int.cast_natCast, map_natCast]
  simp only [hv]

/-- Counting lower-level roots in the full set of higher-level integer
representatives supplies exactly p^((s-t)n) copies of each root. -/
theorem sum_dvd_eval_eq {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (p : ℕ) [Fact p.Prime] {s t : ℕ} (hts : t ≤ s) :
    (∑ x : Fin n → Fin (p^s),
      if ((p^t : ℕ) : ℤ) ∣ eval (fun i => ((x i).val : ℤ)) F then (1 : ℂ) else 0) =
      (p : ℂ)^((s-t)*n) *
        ((Finset.univ.filter fun z : Fin n → ZMod (p^t) =>
          eval₂ (Int.castRingHom (ZMod (p^t))) z F = 0).card : ℂ) := by
  classical
  calc
    _ = ∑ x : Fin n → ZMod (p^s),
        if eval₂ (Int.castRingHom (ZMod (p^t)))
          (fun i => reduction p hts (x i)) F = 0 then (1 : ℂ) else 0 := by
      apply Fintype.sum_equiv (PrimeSumAdapter.vectorResidueEquiv (p^s) n)
      intro x
      simp only [dvd_eval_iff_reduced_zero F p hts]
    _ = ((Finset.univ.filter fun x : Fin n → ZMod (p^s) =>
        eval₂ (Int.castRingHom (ZMod (p^t)))
          (fun i => reduction p hts (x i)) F = 0).card : ℂ) := by
      simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = _ := by
      exact_mod_cast PolynomialSingularLifts.card_reduction_preimage p hts
        (fun z : Fin n → ZMod (p^t) => eval₂ (Int.castRingHom (ZMod (p^t))) z F = 0)

/-- At modulus one the unrestricted polynomial root space is literally
one point, for every polynomial and every number of variables. -/
theorem card_roots_level_zero {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (p : ℕ) [Fact p.Prime] :
    (Finset.univ.filter fun z : Fin n → ZMod (p^0) =>
      eval₂ (Int.castRingHom (ZMod (p^0))) z F = 0).card = 1 := by
  haveI : Subsingleton (ZMod (p^0)) := by simpa using (inferInstance : Subsingleton (ZMod 1))
  have hz (z : Fin n → ZMod (p^0)) : eval₂ (Int.castRingHom (ZMod (p^0))) z F = 0 :=
    Subsingleton.elim _ _
  simp only [hz, Finset.filter_true, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, ZMod.card, pow_zero, one_pow]

end CubicTenVariables.PrimePowerRootReduction
