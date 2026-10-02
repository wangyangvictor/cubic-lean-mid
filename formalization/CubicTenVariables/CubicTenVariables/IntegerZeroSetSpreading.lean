import CubicTenVariables.IntegerEquationEmptyReduction

/-! Equality of the zero sets of two fixed finite integral equation families
spreads outside one finite set of characteristics. The proof uses the literal
Rabinowitsch equation `u * g - 1` and the existing proved geometric-emptiness
and denominator-clearing theorem. It introduces no spreading assumption. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.IntegerZeroSetSpreading
open MvPolynomial
open scoped BigOperators

/-- A simultaneous zero of this system is a zero of the original equations
at which the additional polynomial is nonzero. -/
def augmentedEquations {σ τ : Type*} (F : τ → MvPolynomial σ ℤ)
    (g : MvPolynomial σ ℤ) : Option τ → MvPolynomial (Option σ) ℤ
  | none => X none * rename Option.some g - 1
  | some i => rename Option.some (F i)

@[simp] theorem eval_augmented_none {σ τ K : Type*} [CommRing K]
    (F : τ → MvPolynomial σ ℤ) (g : MvPolynomial σ ℤ) (x : Option σ → K) :
    eval₂Hom (Int.castRingHom K) x (augmentedEquations F g none) =
      x none * eval₂Hom (Int.castRingHom K) (fun s => x (some s)) g - 1 := by
  simp [augmentedEquations, eval₂_rename, Function.comp_def]

@[simp] theorem eval_augmented_some {σ τ K : Type*} [CommRing K]
    (F : τ → MvPolynomial σ ℤ) (g : MvPolynomial σ ℤ)
    (x : Option σ → K) (i : τ) :
    eval₂Hom (Int.castRingHom K) x (augmentedEquations F g (some i)) =
      eval₂Hom (Int.castRingHom K) (fun s => x (some s)) (F i) := by
  simp [augmentedEquations, eval₂_rename, Function.comp_def]

/-- Vanishing of one polynomial on a fixed geometric integer-equation locus
persists over every field outside finitely many characteristics. -/
theorem exists_good_characteristic_vanishing {σ τ : Type*} [Finite σ] [Finite τ]
    (F : τ → MvPolynomial σ ℤ) (g : MvPolynomial σ ℤ)
    (hgeneric : ∀ v : σ → AlgebraicClosure ℚ,
      (∀ i, eval₂Hom (Int.castRingHom (AlgebraicClosure ℚ)) v (F i) = 0) →
        eval₂Hom (Int.castRingHom (AlgebraicClosure ℚ)) v g = 0) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ p : ℕ, ¬ p ∣ D →
      ∀ (K : Type*) [Field K] [CharP K p] (v : σ → K),
        (∀ i, eval₂Hom (Int.castRingHom K) v (F i) = 0) →
          eval₂Hom (Int.castRingHom K) v g = 0 := by
  have hempty : ¬ ∃ x : Option σ → AlgebraicClosure ℚ,
      ∀ i, eval₂Hom (Int.castRingHom (AlgebraicClosure ℚ)) x
        (augmentedEquations F g i) = 0 := by
    rintro ⟨x, hx⟩
    have hg := hgeneric (fun s => x (some s)) (fun i => by
      simpa only [eval_augmented_some] using hx (some i))
    have hz := hx none
    rw [eval_augmented_none, hg, mul_zero, zero_sub] at hz
    exact neg_ne_zero.mpr one_ne_zero hz
  obtain ⟨D, hD, hgood⟩ := IntegerEquationEmptyReduction.exists_good_characteristic_finite
    (augmentedEquations F g) hempty
  refine ⟨D, hD, ?_⟩
  intro p hp K _ _ v hv
  by_contra hg
  apply hgood p hp K
  let x : Option σ → K
    | none => (eval₂Hom (Int.castRingHom K) v g)⁻¹
    | some s => v s
  refine ⟨x, ?_⟩
  intro i
  cases i with
  | none =>
    rw [eval_augmented_none]
    change (eval₂Hom (Int.castRingHom K) v g)⁻¹ *
      eval₂Hom (Int.castRingHom K) v g - 1 = 0
    rw [inv_mul_cancel₀ hg, sub_self]
  | some i =>
    rw [eval_augmented_some]
    exact hv i

/-- One exceptional integer works simultaneously for the whole finite
inclusion, and is chosen before the target characteristic, field and point. -/
theorem exists_good_characteristic_inclusion
    {σ τ κ : Type*} [Finite σ] [Finite τ] [Finite κ]
    (F : τ → MvPolynomial σ ℤ) (G : κ → MvPolynomial σ ℤ)
    (hgeneric : ∀ v : σ → AlgebraicClosure ℚ,
      (∀ i, eval₂Hom (Int.castRingHom (AlgebraicClosure ℚ)) v (F i) = 0) →
        ∀ j, eval₂Hom (Int.castRingHom (AlgebraicClosure ℚ)) v (G j) = 0) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ p : ℕ, ¬ p ∣ D →
      ∀ (K : Type*) [Field K] [CharP K p] (v : σ → K),
        (∀ i, eval₂Hom (Int.castRingHom K) v (F i) = 0) →
          ∀ j, eval₂Hom (Int.castRingHom K) v (G j) = 0 := by
  classical
  letI : Fintype κ := Fintype.ofFinite κ
  have h (j : κ) := exists_good_characteristic_vanishing F (G j)
    (fun v hv => hgeneric v hv j)
  choose D hD hgood using h
  refine ⟨∏ j, D j, Finset.one_le_prod' (fun j _ => hD j), ?_⟩
  intro p hp K _ _ v hv j
  have hpj : ¬ p ∣ D j := fun hdiv => hp (hdiv.trans
    (Finset.dvd_prod_of_mem D (Finset.mem_univ j)))
  exact hgood j p hpj K v hv

/-- Equal geometric zero sets for two finite integer families have equal
zero sets over every field of every remaining characteristic. No reducedness
of the special fibers is asserted or required. -/
theorem exists_good_characteristic_equivalence
    {σ τ κ : Type*} [Finite σ] [Finite τ] [Finite κ]
    (F : τ → MvPolynomial σ ℤ) (G : κ → MvPolynomial σ ℤ)
    (hgeneric : ∀ v : σ → AlgebraicClosure ℚ,
      (∀ i, eval₂Hom (Int.castRingHom (AlgebraicClosure ℚ)) v (F i) = 0) ↔
        ∀ j, eval₂Hom (Int.castRingHom (AlgebraicClosure ℚ)) v (G j) = 0) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ p : ℕ, ¬ p ∣ D →
      ∀ (K : Type*) [Field K] [CharP K p] (v : σ → K),
        (∀ i, eval₂Hom (Int.castRingHom K) v (F i) = 0) ↔
          ∀ j, eval₂Hom (Int.castRingHom K) v (G j) = 0 := by
  obtain ⟨D₁, hD₁, h₁⟩ := exists_good_characteristic_inclusion F G
    (fun v => (hgeneric v).mp)
  obtain ⟨D₂, hD₂, h₂⟩ := exists_good_characteristic_inclusion G F
    (fun v => (hgeneric v).mpr)
  refine ⟨D₁ * D₂, by simpa using Nat.mul_le_mul hD₁ hD₂, ?_⟩
  intro p hp K _ _ v
  have hp₁ : ¬ p ∣ D₁ := fun h => hp (dvd_mul_of_dvd_left h _)
  have hp₂ : ¬ p ∣ D₂ := fun h => hp (dvd_mul_of_dvd_right h _)
  exact ⟨h₁ p hp₁ K v, h₂ p hp₂ K v⟩

end CubicTenVariables.IntegerZeroSetSpreading
