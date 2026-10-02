import HessianTheorem11.UnconditionalWeightActive
import HessianTheorem11.UnconditionalWeightRationalLinear

/-! Rationality of the actual fixed-support optimizer, deduced from its
tight equations and the proved normal equations. No polyhedral or GIT
rationality theorem is assumed. -/
noncomputable section
namespace HessianTheorem11.UnconditionalWeightOptimization
open MvPolynomial
variable {n : ℕ}

theorem minimumNorm_rational {S : Finset (Fin n →₀ ℕ)} {w : WeightSpace n}
    (hw : MinimumNorm S w) : ∃ u : Fin n → ℚ, ∀ j, (u j : ℝ) = w j := by
  classical
  let Tight := {e : Fin n →₀ ℕ // e ∈ S ∧ realMonomialWeight e w = 1}
  have hfinite : Set.Finite {e : Fin n →₀ ℕ | e ∈ S ∧ realMonomialWeight e w = 1} :=
    S.finite_toSet.subset (fun _ h => h.1)
  letI : Fintype Tight := hfinite.fintype
  let A : Matrix (Option Tight) (Fin n) ℚ := fun i j =>
    match i with
    | none => 1
    | some e => (e.val j : ℚ)
  let b : Option Tight → ℚ := fun i => match i with
    | none => 0
    | some _ => 1
  apply UnconditionalWeightRationalLinear.rational_of_normal_solution A b (fun j => w j)
  · intro i
    cases i with
    | none => simpa [A,b,weightSum] using hw.1.1
    | some e => simpa [A,b,realMonomialWeight] using e.property.2
  · intro v hv
    have hsum : weightSum (WithLp.toLp 2 v) = 0 := by
      simpa [A,weightSum] using hv none
    have htight : ∀ e ∈ S, realMonomialWeight e w = 1 →
        realMonomialWeight e (WithLp.toLp 2 v) = 0 := by
      intro e he ht
      simpa [A,realMonomialWeight] using hv (some (⟨e,he,ht⟩ : Tight))
    have h := minimumNorm_orthogonal_tight_direction hw (WithLp.toLp 2 v) hsum htight
    simpa only [PiLp.inner_apply,RCLike.inner_apply',conj_trivial] using h

/-- A positive feasible support has an actual rational optimal ray. -/
theorem exists_rational_minimumNorm (S : Finset (Fin n →₀ ℕ))
    (hne : (feasible S).Nonempty) :
    ∃ u : Fin n → ℚ, MinimumNorm S (WithLp.toLp 2 (fun j => (u j : ℝ))) := by
  obtain ⟨w,hw,_⟩ := exists_unique_minimumNorm S hne
  obtain ⟨u,hu⟩ := minimumNorm_rational hw
  refine ⟨u,?_⟩
  have he : WithLp.toLp 2 (fun j => (u j : ℝ)) = w := by ext j; exact hu j
  rwa [he]

end HessianTheorem11.UnconditionalWeightOptimization
