import CubicTenVariables.CubicFactorCharts
import CubicTenVariables.IntegerEquationEmptyReduction
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Uniform good-characteristic integrality of a homogeneous cubic family
on a prescribed parameter principal open. The actual finite equations for
a normalized linear factor are flattened together with the parameter
variables, and `u * h - 1` enforces that prescribed open. Their geometric
emptiness is spread by the already proved integer-equation theorem.

The final statement does not assume preservation of degree in the special
fiber: a zero specialization has a polynomial-ring quotient, and a nonzero
specialization is still homogeneous of degree three. -/

set_option autoImplicit false
set_option maxHeartbeats 1500000

noncomputable section
namespace CubicTenVariables.CubicPrincipalOpenIntegrality

open MvPolynomial CubicFactorCharts
open scoped BigOperators

abbrev AugmentedVar (σ : Type*) (n : ℕ) := Option (FactorVar n ⊕ σ)

/-- The original factor equations, together with the equation making `h`
invertible; every coefficient is an integer. -/
def augmentedEquations {σ : Type*} {n : ℕ}
    (F : MvPolynomial (Fin n) (MvPolynomial σ ℤ))
    (h : MvPolynomial σ ℤ) (i : Fin n) :
    Option (EquationIndex n) → MvPolynomial (AugmentedVar σ n) ℤ
  | none => X none * rename (fun s ↦ some (Sum.inr s)) h - 1
  | some e => rename Option.some (iterToSum ℤ (FactorVar n) σ (equations F i e))

/-- Flattening coefficient variables preserves their literal evaluation. -/
theorem eval_iterToSum
    {R K α β : Type*} [CommRing R] [CommRing K]
    (ρ : R →+* K) (x : α ⊕ β → K)
    (P : MvPolynomial α (MvPolynomial β R)) :
    eval₂Hom ρ x (iterToSum R α β P) =
      eval₂Hom (eval₂Hom ρ (fun b ↦ x (.inr b))) (fun a ↦ x (.inl a)) P := by
  have heq : (eval₂Hom ρ x).comp (iterToSum R α β) =
      eval₂Hom (eval₂Hom ρ (fun b ↦ x (.inr b))) (fun a ↦ x (.inl a)) := by
    apply MvPolynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro r
        simp
      · intro b
        simp
    · intro a
      simp
  exact RingHom.congr_fun heq P

@[simp] theorem eval_augmented_none {σ : Type*} {n : ℕ}
    (F : MvPolynomial (Fin n) (MvPolynomial σ ℤ))
    (h : MvPolynomial σ ℤ) (i : Fin n)
    {K : Type*} [CommRing K] (x : AugmentedVar σ n → K) :
    eval₂Hom (Int.castRingHom K) x (augmentedEquations F h i none) =
      x none * eval₂Hom (Int.castRingHom K) (fun s ↦ x (some (.inr s))) h - 1 := by
  simp [augmentedEquations, eval₂_rename, Function.comp_def]

@[simp] theorem eval_augmented_some {σ : Type*} {n : ℕ}
    (F : MvPolynomial (Fin n) (MvPolynomial σ ℤ))
    (h : MvPolynomial σ ℤ) (i : Fin n) (e : EquationIndex n)
    {K : Type*} [CommRing K] (x : AugmentedVar σ n → K) :
    eval₂Hom (Int.castRingHom K) x (augmentedEquations F h i (some e)) =
      eval₂Hom (eval₂Hom (Int.castRingHom K) (fun s ↦ x (some (.inr s))))
        (fun a ↦ x (some (.inl a))) (equations F i e) := by
  rw [augmentedEquations, eval₂Hom_rename, eval_iterToSum]
  rfl

/-- One positive integer excludes all bad characteristics for the entire
prescribed parameter open and every target field. No specialized degree
assumption appears in the conclusion. -/
theorem exists_good_characteristic
    {σ : Type*} [Finite σ] {n : ℕ}
    (F : MvPolynomial (Fin n) (MvPolynomial σ ℤ))
    (hF : F.IsHomogeneous 3) (h : MvPolynomial σ ℤ)
    (hgeneric : ∀ v : σ → AlgebraicClosure ℚ,
      eval₂Hom (Int.castRingHom (AlgebraicClosure ℚ)) v h ≠ 0 →
        (map (eval₂Hom (Int.castRingHom (AlgebraicClosure ℚ)) v) F).totalDegree = 3 ∧
        IsDomain (MvPolynomial (Fin n) (AlgebraicClosure ℚ) ⧸
          Ideal.span {map (eval₂Hom (Int.castRingHom (AlgebraicClosure ℚ)) v) F})) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ p : ℕ, ¬ p ∣ D →
      ∀ (K : Type*) [Field K] [CharP K p] (v : σ → K),
        eval₂Hom (Int.castRingHom K) v h ≠ 0 →
        IsDomain (MvPolynomial (Fin n) K ⧸
          Ideal.span {map (eval₂Hom (Int.castRingHom K) v) F}) := by
  classical
  have hempty (i : Fin n) : ¬ ∃ x : AugmentedVar σ n → AlgebraicClosure ℚ,
      ∀ e, eval₂Hom (Int.castRingHom (AlgebraicClosure ℚ)) x
        (augmentedEquations F h i e) = 0 := by
    rintro ⟨x, hx⟩
    have hlocal := hx none
    rw [eval_augmented_none] at hlocal
    have hopen : eval₂Hom (Int.castRingHom (AlgebraicClosure ℚ))
        (fun s ↦ x (some (.inr s))) h ≠ 0 := by
      intro hz
      simp [hz] at hlocal
    obtain ⟨hdegree, hdomain⟩ := hgeneric _ hopen
    apply (isDomain_iff_no_solution
      (eval₂Hom (Int.castRingHom (AlgebraicClosure ℚ)) (fun s ↦ x (some (.inr s))))
      F hdegree).mp hdomain
    refine ⟨i, fun a ↦ x (some (.inl a)), fun e ↦ ?_⟩
    simpa only [eval_augmented_some] using hx (some e)
  have hcharts (i : Fin n) := IntegerEquationEmptyReduction.exists_good_characteristic_finite
    (augmentedEquations F h i) (hempty i)
  choose D hD hgood using hcharts
  refine ⟨∏ i, D i, Finset.one_le_prod' (fun i _ ↦ hD i), ?_⟩
  intro p hp K _ _ v hv
  let ρ := eval₂Hom (Int.castRingHom K) v
  by_cases hzero : map ρ F = 0
  · change IsDomain (MvPolynomial (Fin n) K ⧸ Ideal.span {map ρ F})
    rw [hzero, Ideal.span_singleton_zero]
    exact (Ideal.Quotient.isDomain_iff_prime _).mpr Ideal.bot_prime
  have hdegree : (map ρ F).totalDegree = 3 := (hF.map ρ).totalDegree hzero
  apply (isDomain_iff_no_solution ρ F hdegree).mpr
  rintro ⟨i, x, hx⟩
  have hpi : ¬ p ∣ D i := fun hi ↦ hp (hi.trans
    (Finset.dvd_prod_of_mem D (Finset.mem_univ i)))
  apply hgood i p hpi K
  let z : AugmentedVar σ n → K
    | none => (eval₂Hom (Int.castRingHom K) v h)⁻¹
    | some (.inl a) => x a
    | some (.inr s) => v s
  refine ⟨z, fun e ↦ ?_⟩
  cases e with
  | none =>
      rw [eval_augmented_none]
      change (eval₂Hom (Int.castRingHom K) v h)⁻¹ *
        eval₂Hom (Int.castRingHom K) v h - 1 = 0
      rw [inv_mul_cancel₀ hv, sub_self]
  | some e =>
      rw [eval_augmented_some]
      exact hx e

end CubicTenVariables.CubicPrincipalOpenIntegrality
