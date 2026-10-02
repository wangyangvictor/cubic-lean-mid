import CubicTenVariables.PadicUnitOrbit
import CubicTenVariables.PrimePowerFibers
import CubicTenVariables.PolynomialResidueEvaluation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Set.Card

/-!
# Residue classes of actual local integral zeros

The strong residue set below requires one actual integral zero in the given
set, whose reduction is the full residue tuple. A surjection from a parameter
coset onto such zeros gives a lower bound by choosing a zero above each
parameter residue and using the unchanged deleted coordinates for injectivity.
No descent of an inverse chart to residue classes is assumed or asserted.

The parameter-surjection theorem is an explicit hypothesis of this finite
counting lemma. Its analytic construction is separate. The inclusion into
ordinary modular zeros, monotonicity, and the literal finite coset filter are
proved here, including parameter dimension zero and reduction level zero.
-/

noncomputable section

namespace CubicTenVariables.LocalZeroResidues

open MvPolynomial PadicUnitOrbit PrimePowerFibers

attribute [local instance] Classical.propDecidable

variable (p : ℕ) [Fact p.Prime]

/-- Full residue tuples which have an actual integral zero lift in B. -/
def actualZeroResidues {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (B : Set (Fin n → ℤ_[p])) (s : ℕ) : Set (Fin n → ZMod (p ^ s)) :=
  {v | ∃ z ∈ B, eval₂ (Int.castRingHom ℤ_[p]) z F = 0 ∧
    ∀ j, PadicInt.toZModPow s (z j) = v j}

/-- Ordinary modular zeros admitting an integral lift in B; that lift is
not required to be an exact zero. -/
def modularZeroResidues {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (B : Set (Fin n → ℤ_[p])) (s : ℕ) : Set (Fin n → ZMod (p ^ s)) :=
  {v | eval₂ (Int.castRingHom (ZMod (p ^ s))) v F = 0 ∧
    ∃ z ∈ B, ∀ j, PadicInt.toZModPow s (z j) = v j}

theorem actualZeroResidues_mono {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    {B C : Set (Fin n → ℤ_[p])} (hBC : B ⊆ C) (s : ℕ) :
    actualZeroResidues p F B s ⊆ actualZeroResidues p F C s := by
  rintro v ⟨z, hz, hF, hv⟩
  exact ⟨z, hBC hz, hF, hv⟩

theorem modularZeroResidues_mono {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    {B C : Set (Fin n → ℤ_[p])} (hBC : B ⊆ C) (s : ℕ) :
    modularZeroResidues p F B s ⊆ modularZeroResidues p F C s := by
  rintro v ⟨hF, z, hz, hv⟩
  exact ⟨hF, z, hBC hz, hv⟩

theorem actualZeroResidues_subset_modularZeroResidues {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (B : Set (Fin n → ℤ_[p])) (s : ℕ) :
    actualZeroResidues p F B s ⊆ modularZeroResidues p F B s := by
  rintro v ⟨z, hz, hF, hv⟩
  refine ⟨?_, z, hz, hv⟩
  rw [← PolynomialResidueEvaluation.toZModPow_eval₂_int_of_lift F s z v hv, hF, map_zero]

theorem card_actualZeroResidues_mono {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    {B C : Set (Fin n → ℤ_[p])} (hBC : B ⊆ C) (s : ℕ) :
    Nat.card (actualZeroResidues p F B s) ≤ Nat.card (actualZeroResidues p F C s) :=
  Set.ncard_le_ncard (actualZeroResidues_mono p F hBC s)

theorem card_modularZeroResidues_mono {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    {B C : Set (Fin n → ℤ_[p])} (hBC : B ⊆ C) (s : ℕ) :
    Nat.card (modularZeroResidues p F B s) ≤ Nat.card (modularZeroResidues p F C s) :=
  Set.ncard_le_ncard (modularZeroResidues_mono p F hBC s)

theorem card_actualZeroResidues_le_modularZeroResidues {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (B : Set (Fin n → ℤ_[p])) (s : ℕ) :
    Nat.card (actualZeroResidues p F B s) ≤ Nat.card (modularZeroResidues p F B s) :=
  Set.ncard_le_ncard (actualZeroResidues_subset_modularZeroResidues p F B s)

/-- Every residue tuple in the appropriate reduction fiber has an actual
integral lift in the corresponding literal coset. -/
theorem exists_integral_lift_mem_coset {n : ℕ} (ξ : Fin n → ℤ_[p])
    (K s : ℕ) (hKs : K ≤ s) (v : Fin n → ZMod (p ^ s))
    (hv : ∀ j, reduction p hKs (v j) = PadicInt.toZModPow K (ξ j)) :
    ∃ y ∈ coset p ξ K, ∀ j, PadicInt.toZModPow s (y j) = v j := by
  let y : Fin n → ℤ_[p] := fun j => ZMod.cast (v j)
  have hy (j : Fin n) : PadicInt.toZModPow s (y j) = v j :=
    ZMod.ringHom_map_cast (PadicInt.toZModPow s) (v j)
  refine ⟨y, (mem_coset_iff p ξ y K).mpr (fun j => ?_), hy⟩
  have h := hv j
  rw [← hy j] at h
  simpa only [reduction, ZMod.castHom_apply, PadicInt.cast_toZModPow K s hKs] using h

/-- An actual parameter surjection gives the exact finite lower-bound
exponent. Chosen zero lifts need not depend only on their parameter residues. -/
theorem card_actualZeroResidues_ge_of_parameter_surjection {m : ℕ}
    (F : MvPolynomial (Fin (m + 1)) ℤ) (B : Set (Fin (m + 1) → ℤ_[p]))
    (i : Fin (m + 1)) (ξ : Fin (m + 1) → ℤ_[p]) (K : ℕ)
    (hpatch : ∀ y ∈ coset p (i.removeNth ξ) K,
      ∃ z ∈ B, eval₂ (Int.castRingHom ℤ_[p]) z F = 0 ∧ i.removeNth z = y)
    (s : ℕ) (hKs : K ≤ s) :
    p ^ ((s - K) * m) ≤ Nat.card (actualZeroResidues p F B s) := by
  classical
  let P := {v : Fin m → ZMod (p ^ s) // ∀ j,
    reduction p hKs (v j) = PadicInt.toZModPow K ((i.removeNth ξ) j)}
  have hex (v : P) : ∃ w : actualZeroResidues p F B s,
      ∀ j, w.val (i.succAbove j) = v.val j := by
    obtain ⟨y, hy, hv⟩ := exists_integral_lift_mem_coset p (i.removeNth ξ) K s hKs v.val v.property
    obtain ⟨z, hz, hFz, hzy⟩ := hpatch y hy
    refine ⟨⟨fun j => PadicInt.toZModPow s (z j), z, hz, hFz, fun _ => rfl⟩, fun j => ?_⟩
    change PadicInt.toZModPow s (z (i.succAbove j)) = v.val j
    have hcoord : z (i.succAbove j) = y j := congrFun hzy j
    rw [hcoord]
    exact hv j
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro v w hvw
    apply Subtype.ext
    funext j
    exact (hf v j).symm.trans ((congrArg
      (fun z : actualZeroResidues p F B s => z.val (i.succAbove j)) hvw).trans (hf w j))
  calc
    p ^ ((s - K) * m) = Nat.card P :=
      (card_vector_reduction_fiber p hKs m
        (fun j => PadicInt.toZModPow K ((i.removeNth ξ) j))).symm
    _ ≤ Nat.card (actualZeroResidues p F B s) := Nat.card_le_card_of_injective f hinj

theorem card_modularZeroResidues_ge_of_parameter_surjection {m : ℕ}
    (F : MvPolynomial (Fin (m + 1)) ℤ) (B : Set (Fin (m + 1) → ℤ_[p]))
    (i : Fin (m + 1)) (ξ : Fin (m + 1) → ℤ_[p]) (K : ℕ)
    (hpatch : ∀ y ∈ coset p (i.removeNth ξ) K,
      ∃ z ∈ B, eval₂ (Int.castRingHom ℤ_[p]) z F = 0 ∧ i.removeNth z = y)
    (s : ℕ) (hKs : K ≤ s) :
    p ^ ((s - K) * m) ≤ Nat.card (modularZeroResidues p F B s) :=
  (card_actualZeroResidues_ge_of_parameter_surjection p F B i ξ K hpatch s hKs).trans
    (card_actualZeroResidues_le_modularZeroResidues p F B s)

/-- Over a level-s residue ring, a lift in a level-M coset is exactly the
literal reduction condition, when M ≤ s. -/
theorem modularZeroResidues_coset_eq {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (ξ : Fin n → ℤ_[p]) (M s : ℕ) (hMs : M ≤ s) :
    modularZeroResidues p F (coset p ξ M) s =
      {v | eval₂ (Int.castRingHom (ZMod (p ^ s))) v F = 0 ∧
        ∀ j, reduction p hMs (v j) = PadicInt.toZModPow M (ξ j)} := by
  ext v
  constructor
  · rintro ⟨hF, z, hz, hv⟩
    refine ⟨hF, fun j => ?_⟩
    rw [← hv j]
    simpa only [reduction, ZMod.castHom_apply, PadicInt.cast_toZModPow M s hMs] using
      (mem_coset_iff p ξ z M).mp hz j
  · rintro ⟨hF, hv⟩
    exact ⟨hF, exists_integral_lift_mem_coset p ξ M s hMs v hv⟩

/-- A literal finite modular-zero filter with fixed lower-level coordinate residues. -/
def modularZeroCosetFilter {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (ξ : Fin n → ℤ_[p]) (M s : ℕ) (hMs : M ≤ s) : Finset (Fin n → ZMod (p ^ s)) :=
  Finset.univ.filter (fun v =>
    eval₂ (Int.castRingHom (ZMod (p ^ s))) v F = 0 ∧
      ∀ j, reduction p hMs (v j) = PadicInt.toZModPow M (ξ j))

theorem card_modularZeroCosetFilter_eq {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (ξ : Fin n → ℤ_[p]) (M s : ℕ) (hMs : M ≤ s) :
    (modularZeroCosetFilter p F ξ M s hMs).card =
      Nat.card (modularZeroResidues p F (coset p ξ M) s) := by
  rw [modularZeroResidues_coset_eq p F ξ M s hMs]
  simp only [modularZeroCosetFilter, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Set.mem_setOf_eq]

/-- The parameter-surjection lower bound for the literal finite congruence filter. -/
theorem card_modularZeroCosetFilter_ge_of_parameter_surjection {m : ℕ}
    (F : MvPolynomial (Fin (m + 1)) ℤ) (i : Fin (m + 1))
    (ξ : Fin (m + 1) → ℤ_[p]) (M K : ℕ) (hMK : M ≤ K)
    (hpatch : ∀ y ∈ coset p (i.removeNth ξ) K,
      ∃ z ∈ coset p ξ M, eval₂ (Int.castRingHom ℤ_[p]) z F = 0 ∧ i.removeNth z = y)
    (s : ℕ) (hKs : K ≤ s) :
    p ^ ((s - K) * m) ≤ (modularZeroCosetFilter p F ξ M s (hMK.trans hKs)).card := by
  rw [card_modularZeroCosetFilter_eq]
  exact card_modularZeroResidues_ge_of_parameter_surjection p F (coset p ξ M) i ξ K hpatch s hKs

end CubicTenVariables.LocalZeroResidues
