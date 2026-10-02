import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Data.Finite.Card
import CubicTenVariables.PrimePowerFibers
import CubicTenVariables.PadicResidueNorm

/-!
# Actual residue fibers represented in a local patch

The finite objects counted here are full coordinate tuples modulo p^s,
admitting an actual integral lift in a specified patch with prescribed
selected outputs and untouched coordinate residues. No uniqueness of lifts
or compatibility of an arbitrary supplied output map with reduction is assumed.
-/

noncomputable section

namespace CubicTenVariables.LocalCongruenceFibers

open scoped NNReal

attribute [local instance] Classical.propDecidable

variable (p : ℕ) [Fact p.Prime] {n r : ℕ}

/-- The coordinates not selected by `cols`. -/
abbrev Untouched (cols : Fin r → Fin n) := {j : Fin n // j ∉ Set.range cols}

/-- A literal finite residue fiber with an actual lift in the prescribed patch. -/
def representedFiber (s : ℕ) (U : Set (Fin n → ℤ_[p]))
    (g : (Fin n → ℤ_[p]) → (Fin r → ℤ_[p])) (cols : Fin r → Fin n)
    (b : Untouched cols → ZMod (p ^ s)) (c : Fin r → ZMod (p ^ s)) :
    Set (Fin n → ZMod (p ^ s)) :=
  {v | (∀ j : Untouched cols, v j.1 = b j) ∧
    ∃ z ∈ U, (∀ k, PadicInt.toZModPow s (z k) = v k) ∧
      ∀ a, PadicInt.toZModPow s (g z a) = c a}

/-- With untouched coordinates fixed, the selected coordinates determine a tuple.
Repeated selections are harmless for this implication. -/
theorem selected_injective_on_representedFiber (s : ℕ) (U : Set (Fin n → ℤ_[p]))
    (g : (Fin n → ℤ_[p]) → (Fin r → ℤ_[p])) (cols : Fin r → Fin n)
    (b : Untouched cols → ZMod (p ^ s)) (c : Fin r → ZMod (p ^ s)) :
    Function.Injective (fun v : representedFiber p s U g cols b c =>
      fun a => v.1 (cols a)) := by
  classical
  intro v w hvw
  apply Subtype.ext
  funext k
  by_cases hk : k ∈ Set.range cols
  · obtain ⟨a, rfl⟩ := hk
    exact congrFun hvw a
  · exact (v.2.1 ⟨k, hk⟩).trans (w.2.1 ⟨k, hk⟩).symm

/-- A comparison with a supplied reference lift bounds the full residue fiber
by a selected lower-level reduction fiber. The later uniform theorem chooses
the reference from the actual fiber and handles the empty case separately. -/
theorem card_representedFiber_le_reduction_fiber
    (s t : ℕ) (hts : t ≤ s) (U : Set (Fin n → ℤ_[p]))
    (g : (Fin n → ℤ_[p]) → (Fin r → ℤ_[p])) (cols : Fin r → Fin n)
    (b : Untouched cols → ZMod (p ^ s)) (c : Fin r → ZMod (p ^ s))
    (w : Fin n → ℤ_[p])
    (hwb : ∀ j : Untouched cols, PadicInt.toZModPow s (w j.1) = b j)
    (hwc : ∀ a, PadicInt.toZModPow s (g w a) = c a)
    (hclose : ∀ z ∈ U,
      (∀ j : Untouched cols, PadicInt.toZModPow s (z j.1) =
        PadicInt.toZModPow s (w j.1)) →
      (∀ a, PadicInt.toZModPow s (g z a) = PadicInt.toZModPow s (g w a)) →
      ∀ a, PadicInt.toZModPow t (z (cols a)) = PadicInt.toZModPow t (w (cols a))) :
    Nat.card (representedFiber p s U g cols b c) ≤
      Nat.card {v : Fin r → ZMod (p ^ s) // ∀ a,
        ZMod.castHom (pow_dvd_pow p hts) (ZMod (p ^ t)) (v a) =
          PadicInt.toZModPow t (w (cols a))} := by
  classical
  let target := {v : Fin r → ZMod (p ^ s) // ∀ a,
    ZMod.castHom (pow_dvd_pow p hts) (ZMod (p ^ t)) (v a) =
      PadicInt.toZModPow t (w (cols a))}
  have hmem (v : representedFiber p s U g cols b c) :
      ∀ a, ZMod.castHom (pow_dvd_pow p hts) (ZMod (p ^ t)) (v.1 (cols a)) =
        PadicInt.toZModPow t (w (cols a)) := by
    obtain ⟨hb, z, hz, hv, hc⟩ := v.2
    have ht := hclose z hz (fun j => (hv j.1).trans ((hb j).trans (hwb j).symm))
      (fun a => (hc a).trans (hwc a).symm)
    intro a
    rw [← hv (cols a)]
    simpa only [ZMod.castHom_apply, PadicInt.cast_toZModPow t s hts] using ht a
  let f : representedFiber p s U g cols b c → target :=
    fun v => ⟨fun a => v.1 (cols a), hmem v⟩
  apply Nat.card_le_card_of_injective f
  intro v w h
  apply selected_injective_on_representedFiber p s U g cols b c
  exact congrArg Subtype.val h

/-- Uniform finite fiber bound from a fixed loss of p-adic precision. The
constant `A` is chosen before the modulus and both target residue tuples. -/
theorem card_representedFiber_le_of_local_congruence_control
    (U : Set (Fin n → ℤ_[p]))
    (g : (Fin n → ℤ_[p]) → (Fin r → ℤ_[p])) (cols : Fin r → Fin n) (A : ℕ)
    (hcontrol : ∀ (s : ℕ) (z w : Fin n → ℤ_[p]), z ∈ U → w ∈ U →
      (∀ j : Untouched cols, PadicInt.toZModPow s (z j.1) =
        PadicInt.toZModPow s (w j.1)) →
      (∀ a, PadicInt.toZModPow s (g z a) = PadicInt.toZModPow s (g w a)) →
      ∀ a, PadicInt.toZModPow (s - A) (z (cols a)) =
        PadicInt.toZModPow (s - A) (w (cols a)))
    (s : ℕ) (b : Untouched cols → ZMod (p ^ s)) (c : Fin r → ZMod (p ^ s)) :
    Nat.card (representedFiber p s U g cols b c) ≤ p ^ (A * r) := by
  classical
  by_cases hne : (representedFiber p s U g cols b c).Nonempty
  · obtain ⟨v, hb, w, hw, hv, hc⟩ := hne
    have hwb : ∀ j : Untouched cols, PadicInt.toZModPow s (w j.1) = b j :=
      fun j => (hv j.1).trans (hb j)
    exact (card_representedFiber_le_reduction_fiber p s (s - A) (Nat.sub_le s A)
      U g cols b c w hwb hc (fun z hz => hcontrol s z w hz hw)).trans
        (PrimePowerFibers.card_vector_truncation_fiber_le p s A r
          (fun a => PadicInt.toZModPow (s - A) (w (cols a))))
  · haveI : IsEmpty (representedFiber p s U g cols b c) :=
      ⟨fun v => hne ⟨v.1, v.2⟩⟩
    simp

/-- An actual inverse-distance bound on the integral patch gives a uniform
bound on its literal finite residue fibers, with a prescribed precision loss. -/
theorem card_representedFiber_le_of_norm_control
    (U : Set (Fin n → ℤ_[p]))
    (g : (Fin n → ℤ_[p]) → (Fin r → ℤ_[p])) (cols : Fin r → Fin n)
    (C : ℝ≥0) (A : ℕ) (hC : (C : ℝ) ≤ (p : ℝ) ^ A)
    (hbound : ∀ z ∈ U, ∀ w ∈ U,
      ‖z - w‖ ≤ C * ‖(g z - g w, fun j : Untouched cols => z j.1 - w j.1)‖)
    (s : ℕ) (b : Untouched cols → ZMod (p ^ s)) (c : Fin r → ZMod (p ^ s)) :
    Nat.card (representedFiber p s U g cols b c) ≤ p ^ (A * r) := by
  apply card_representedFiber_le_of_local_congruence_control p U g cols A
  intro t z w hz hw hb hc
  have houtputs : ‖(g z - g w, fun j : Untouched cols => z j.1 - w j.1)‖ ≤
      ((p : ℝ) ^ t)⁻¹ := by
    apply norm_prod_le_iff.mpr
    constructor
    · exact (PadicResidueNorm.pi_toZModPow_eq_iff_norm_sub_le t (g z) (g w)).mp hc
    · exact (PadicResidueNorm.pi_toZModPow_eq_iff_norm_sub_le t
        (fun j : Untouched cols => z j.1) (fun j : Untouched cols => w j.1)).mp hb
  have hdist : ‖z - w‖ ≤ C * ((p : ℝ) ^ t)⁻¹ :=
    (hbound z hz w hw).trans (mul_le_mul_of_nonneg_left houtputs C.2)
  exact fun a => PadicResidueNorm.pi_toZModPow_sub_eq_of_norm_sub_le_mul_inv_pow
    z w C A t hC hdist (cols a)

/-- The loss exponent is chosen once from the actual distance constant, before
the modulus or either target tuple. -/
theorem exists_uniform_representedFiber_bound_of_norm_control
    (U : Set (Fin n → ℤ_[p]))
    (g : (Fin n → ℤ_[p]) → (Fin r → ℤ_[p])) (cols : Fin r → Fin n)
    (C : ℝ≥0)
    (hbound : ∀ z ∈ U, ∀ w ∈ U,
      ‖z - w‖ ≤ C * ‖(g z - g w, fun j : Untouched cols => z j.1 - w j.1)‖) :
    ∃ A : ℕ, ∀ (s : ℕ) (b : Untouched cols → ZMod (p ^ s))
      (c : Fin r → ZMod (p ^ s)),
      Nat.card (representedFiber p s U g cols b c) ≤ p ^ (A * r) := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨A, hA⟩ := pow_unbounded_of_one_lt (C : ℝ) hp
  exact ⟨A, fun s b c => card_representedFiber_le_of_norm_control p U g cols C A
    hA.le hbound s b c⟩

/-- An antilipschitz restriction of the actual output/untouched-coordinate map
supplies the inverse-distance hypothesis without any further local assumption. -/
theorem exists_uniform_representedFiber_bound_of_antilipschitz
    (U : Set (Fin n → ℤ_[p]))
    (g : (Fin n → ℤ_[p]) → (Fin r → ℤ_[p])) (cols : Fin r → Fin n)
    (C : ℝ≥0)
    (hanti : AntilipschitzWith C (U.restrict
      (fun z => (g z, fun j : Untouched cols => z j.1)))) :
    ∃ A : ℕ, ∀ (s : ℕ) (b : Untouched cols → ZMod (p ^ s))
      (c : Fin r → ZMod (p ^ s)),
      Nat.card (representedFiber p s U g cols b c) ≤ p ^ (A * r) := by
  apply exists_uniform_representedFiber_bound_of_norm_control p U g cols C
  intro z hz w hw
  simpa only [Subtype.dist_eq, Set.restrict_apply, dist_eq_norm,
    Prod.mk_sub_mk, Pi.sub_apply] using hanti.le_mul_dist ⟨z, hz⟩ ⟨w, hw⟩

end CubicTenVariables.LocalCongruenceFibers
