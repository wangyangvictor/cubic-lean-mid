import CubicTenVariables.FixedEquationDimensionAll
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! A fixed finite family of integer equations with no common zero over
`AlgebraicClosure ℚ` has no common zero over any field outside finitely
many characteristics.  The denominator-clearing theorem is the existing
`FixedEquationDimensionAll.exists_good_characteristic_top`; this file only
supplies its Nullstellensatz hypothesis and finite-index transport.

All variables are treated together.  Thus parameter variables, factor
coefficients and an extra equation `u * h - 1` may be included literally. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace CubicTenVariables.IntegerEquationEmptyReduction

open MvPolynomial FixedEquationNormalization FixedEquationDimensionReduction

/-- Geometric emptiness implies that the actual rational equation ideal
is the unit ideal.  Merely having no rational points would not suffice. -/
theorem rational_equationIdeal_eq_top {N t : ℕ}
    (f : Fin t → MvPolynomial (Fin N) ℤ)
    (hempty : ¬ ∃ x : Fin N → AlgebraicClosure ℚ,
      ∀ i, eval₂Hom (Int.castRingHom (AlgebraicClosure ℚ)) x (f i) = 0) :
    equationIdeal f ℚ = ⊤ := by
  have hzero : zeroLocus (AlgebraicClosure ℚ) (equationIdeal f ℚ) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    apply hempty
    refine ⟨x, fun i ↦ ?_⟩
    have hi := hx (equationsOver f ℚ i) (Ideal.subset_span (Set.mem_range_self i))
    change eval₂ (algebraMap ℚ (AlgebraicClosure ℚ)) x
      (map (Int.castRingHom ℚ) (f i)) = 0 at hi
    rw [eval₂_map] at hi
    have hcomp : (algebraMap ℚ (AlgebraicClosure ℚ)).comp (Int.castRingHom ℚ) =
        Int.castRingHom (AlgebraicClosure ℚ) := RingHom.ext_int _ _
    simpa only [hcomp] using hi
  apply Ideal.radical_eq_top.mp
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := AlgebraicClosure ℚ),
    hzero, vanishingIdeal_empty]

/-- One positive exceptional integer is chosen before the characteristic
and every field of that characteristic.  Primality of the characteristic
does not need to be supplied separately. -/
theorem exists_good_characteristic {N t : ℕ}
    (f : Fin t → MvPolynomial (Fin N) ℤ)
    (hempty : ¬ ∃ x : Fin N → AlgebraicClosure ℚ,
      ∀ i, eval₂Hom (Int.castRingHom (AlgebraicClosure ℚ)) x (f i) = 0) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ p : ℕ, ¬ p ∣ D →
      ∀ (K : Type*) [Field K] [CharP K p],
        equationIdeal f K = ⊤ ∧
          ¬ ∃ x : Fin N → K, ∀ i, eval₂Hom (Int.castRingHom K) x (f i) = 0 := by
  obtain ⟨D, hD, hgood⟩ := FixedEquationDimensionAll.exists_good_characteristic_top
    f (rational_equationIdeal_eq_top f hempty)
  refine ⟨D, hD, fun p hp K _ _ ↦ ?_⟩
  obtain ⟨htop, hzero⟩ := hgood p hp K
  refine ⟨htop, ?_⟩
  rintro ⟨x, hx⟩
  have hmem : x ∈ zeroSet f K := hx
  rw [hzero] at hmem
  exact hmem

/-- The same literal nonexistence statement for arbitrary finite equation
and variable types, useful for combined parameter/factor/localization
variables.  Renaming uses actual equivalences and preserves evaluation. -/
theorem exists_good_characteristic_finite
    {σ τ : Type*} [Finite σ] [Finite τ]
    (f : τ → MvPolynomial σ ℤ)
    (hempty : ¬ ∃ x : σ → AlgebraicClosure ℚ,
      ∀ i, eval₂Hom (Int.castRingHom (AlgebraicClosure ℚ)) x (f i) = 0) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ p : ℕ, ¬ p ∣ D →
      ∀ (K : Type*) [Field K] [CharP K p],
        ¬ ∃ x : σ → K, ∀ i, eval₂Hom (Int.castRingHom K) x (f i) = 0 := by
  classical
  letI : Fintype σ := Fintype.ofFinite σ
  letI : Fintype τ := Fintype.ofFinite τ
  let e := Fintype.equivFin σ
  let a := Fintype.equivFin τ
  let g : Fin (Fintype.card τ) → MvPolynomial (Fin (Fintype.card σ)) ℤ :=
    fun i ↦ rename e (f (a.symm i))
  have hgeneric : ¬ ∃ x : Fin (Fintype.card σ) → AlgebraicClosure ℚ,
      ∀ i, eval₂Hom (Int.castRingHom (AlgebraicClosure ℚ)) x (g i) = 0 := by
    rintro ⟨x, hx⟩
    apply hempty
    refine ⟨x ∘ e, fun i ↦ ?_⟩
    simpa only [g, Equiv.symm_apply_apply, eval₂Hom_rename] using hx (a i)
  obtain ⟨D, hD, hgood⟩ := exists_good_characteristic g hgeneric
  refine ⟨D, hD, fun p hp K _ _ ↦ ?_⟩
  rintro ⟨x, hx⟩
  apply (hgood p hp K).2
  refine ⟨x ∘ e.symm, fun i ↦ ?_⟩
  simpa only [g, eval₂Hom_rename, Function.comp_assoc,
    Equiv.symm_comp_self, Function.comp_id] using hx (a.symm i)

end CubicTenVariables.IntegerEquationEmptyReduction
