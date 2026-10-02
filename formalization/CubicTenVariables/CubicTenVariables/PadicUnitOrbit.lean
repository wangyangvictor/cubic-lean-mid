import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic

/-!
# Literal integral p-adic cosets and their finite unit-orbit cover

The coset consists of actual points `ξ + p^M t` with integral coordinates.
The orbit is covered by at most `p^M` unit-scaled copies of that coset,
using representatives only of the actual image of integral units modulo
`p^M`. No surjectivity assertion about residue units is needed. Level zero
and zero ambient dimension are included.
-/

noncomputable section
namespace CubicTenVariables.PadicUnitOrbit

variable (p : ℕ) [Fact p.Prime]

/-- The literal integral congruence coset. -/
def coset {n : ℕ} (ξ : Fin n → ℤ_[p]) (M : ℕ) : Set (Fin n → ℤ_[p]) :=
  Set.range (fun t : Fin n → ℤ_[p] => ξ + (p : ℤ_[p]) ^ M • t)

/-- The orbit under scalar multiplication by actual integral units. -/
def unitOrbit {n : ℕ} (ξ : Fin n → ℤ_[p]) (M : ℕ) : Set (Fin n → ℤ_[p]) :=
  {x | ∃ u : ℤ_[p]ˣ, ∃ z ∈ coset p ξ M, (u : ℤ_[p]) • z = x}

@[simp] theorem center_mem_coset {n : ℕ} (ξ : Fin n → ℤ_[p]) (M : ℕ) :
    ξ ∈ coset p ξ M := by
  exact ⟨0, by simp⟩

/-- Increasing the exponent shrinks the literal coset. -/
theorem coset_mono {n : ℕ} (ξ : Fin n → ℤ_[p]) {M N : ℕ} (hMN : M ≤ N) :
    coset p ξ N ⊆ coset p ξ M := by
  rintro x ⟨t, rfl⟩
  refine ⟨(p : ℤ_[p]) ^ (N - M) • t, ?_⟩
  change ξ + (p : ℤ_[p]) ^ M • ((p : ℤ_[p]) ^ (N - M) • t) =
    ξ + (p : ℤ_[p]) ^ N • t
  rw [smul_smul, ← pow_add, Nat.add_sub_of_le hMN]

/-- Every point of the literal coset belongs to its unit orbit. -/
theorem coset_subset_unitOrbit {n : ℕ} (ξ : Fin n → ℤ_[p]) (M : ℕ) :
    coset p ξ M ⊆ unitOrbit p ξ M := by
  intro x hx
  exact ⟨1, x, hx, by simp⟩

/-- Increasing the exponent also shrinks the entire unit orbit. -/
theorem unitOrbit_mono {n : ℕ} (ξ : Fin n → ℤ_[p]) {M N : ℕ} (hMN : M ≤ N) :
    unitOrbit p ξ N ⊆ unitOrbit p ξ M := by
  rintro x ⟨u, z, hz, rfl⟩
  exact ⟨u, z, coset_mono p ξ hMN hz, rfl⟩

/-- The literal orbit is stable under every actual integral unit. -/
theorem unit_smul_unitOrbit {n : ℕ} (ξ : Fin n → ℤ_[p]) (M : ℕ) (u : ℤ_[p]ˣ) :
    (fun z => (u : ℤ_[p]) • z) '' unitOrbit p ξ M = unitOrbit p ξ M := by
  ext x
  constructor
  · rintro ⟨y, ⟨v, z, hz, rfl⟩, rfl⟩
    exact ⟨u * v, z, hz, by simp [smul_smul]⟩
  · rintro ⟨v, z, hz, rfl⟩
    refine ⟨((↑(u⁻¹ * v) : ℤ_[p]) • z), ⟨u⁻¹ * v, z, hz, rfl⟩, ?_⟩
    dsimp only
    rw [smul_smul, ← Units.val_mul]
    simp

/-- Membership is exactly coordinatewise equality under literal reduction. -/
theorem mem_coset_iff {n : ℕ} (ξ x : Fin n → ℤ_[p]) (M : ℕ) :
    x ∈ coset p ξ M ↔
      ∀ j, PadicInt.toZModPow M (x j) = PadicInt.toZModPow M (ξ j) := by
  have hpow : PadicInt.toZModPow M ((p : ℤ_[p]) ^ M) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]
    exact Ideal.subset_span (Set.mem_singleton _)
  constructor
  · rintro ⟨t, rfl⟩ j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul,
      hpow, zero_mul, add_zero]
  · intro hx
    have hdvd : ∀ j, (p : ℤ_[p]) ^ M ∣ x j - ξ j := by
      intro j
      rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker,
        map_sub, hx j, sub_self]
    choose t ht using hdvd
    refine ⟨t, ?_⟩
    funext j
    change ξ j + (p : ℤ_[p]) ^ M * t j = x j
    rw [← ht j]
    exact add_sub_cancel _ _

/-- Congruent integral centers define exactly the same literal coset. -/
theorem coset_eq_of_congruent {n : ℕ} (ξ η : Fin n → ℤ_[p]) (M : ℕ)
    (h : ∀ j, PadicInt.toZModPow M (ξ j) = PadicInt.toZModPow M (η j)) :
    coset p ξ M = coset p η M := by
  ext x
  simp only [mem_coset_iff, h]

/-- Scaling a coset by an actual unit scales exactly its center. -/
theorem unit_smul_coset {n : ℕ} (ξ : Fin n → ℤ_[p]) (M : ℕ) (u : ℤ_[p]ˣ) :
    (fun z => (u : ℤ_[p]) • z) '' coset p ξ M = coset p ((u : ℤ_[p]) • ξ) M := by
  ext x
  constructor
  · rintro ⟨z, ⟨t, rfl⟩, rfl⟩
    refine ⟨(u : ℤ_[p]) • t, ?_⟩
    simp only [smul_add]
    congr 1
    exact smul_comm _ _ _
  · rintro ⟨t, rfl⟩
    refine ⟨ξ + (p : ℤ_[p]) ^ M • ((↑u⁻¹ : ℤ_[p]) • t),
      ⟨(↑u⁻¹ : ℤ_[p]) • t, rfl⟩, ?_⟩
    simp only [smul_add]
    congr 1
    rw [smul_comm (u : ℤ_[p])]
    simp only [smul_smul, Units.mul_inv, one_smul]

/-- Unit multipliers congruent modulo `p^M` yield the same scaled coset. -/
theorem unit_smul_coset_eq_of_congruent {n : ℕ} (ξ : Fin n → ℤ_[p]) (M : ℕ)
    (u v : ℤ_[p]ˣ)
    (huv : PadicInt.toZModPow M (u : ℤ_[p]) = PadicInt.toZModPow M (v : ℤ_[p])) :
    (fun z => (u : ℤ_[p]) • z) '' coset p ξ M =
      (fun z => (v : ℤ_[p]) • z) '' coset p ξ M := by
  rw [unit_smul_coset, unit_smul_coset]
  apply coset_eq_of_congruent
  intro j
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, huv]

/-- Representatives are selected only for the actual finite residue image
of the units. In particular, no lifting theorem for residue units is used. -/
theorem exists_unit_residue_representatives (M : ℕ) :
    ∃ T : Finset ℤ_[p]ˣ, T.card ≤ p ^ M ∧
      ∀ u : ℤ_[p]ˣ, ∃ v ∈ T,
        PadicInt.toZModPow M (v : ℤ_[p]) = PadicInt.toZModPow M (u : ℤ_[p]) := by
  classical
  letI : NeZero (p ^ M) := ⟨pow_ne_zero M (Fact.out : p.Prime).ne_zero⟩
  let f : ℤ_[p]ˣ → ZMod (p ^ M) := fun u => PadicInt.toZModPow M (u : ℤ_[p])
  let S : Finset (ZMod (p ^ M)) := Finset.univ.filter (fun b => b ∈ Set.range f)
  have hex : ∀ b : S, ∃ u : ℤ_[p]ˣ, f u = (b : ZMod (p ^ M)) := by
    intro b
    exact (Finset.mem_filter.mp b.property).2
  choose rep hrep using hex
  let T : Finset ℤ_[p]ˣ := S.attach.image rep
  refine ⟨T, ?_, ?_⟩
  · calc
      T.card ≤ S.attach.card := Finset.card_image_le
      _ = S.card := Finset.card_attach
      _ ≤ (Finset.univ : Finset (ZMod (p ^ M))).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = p ^ M := by simp
  · intro u
    have hfu : f u ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨u, rfl⟩⟩
    refine ⟨rep ⟨f u, hfu⟩, ?_, hrep ⟨f u, hfu⟩⟩
    exact Finset.mem_image.mpr ⟨⟨f u, hfu⟩, Finset.mem_attach _ _, rfl⟩

/-- The whole unit orbit is covered exactly by at most `p^M` actual
unit-scaled copies of the literal integral coset. The representatives and
cardinality bound are fixed before the point in the orbit. -/
theorem exists_finite_unit_orbit_cover {n : ℕ} (ξ : Fin n → ℤ_[p]) (M : ℕ) :
    ∃ T : Finset ℤ_[p]ˣ, T.card ≤ p ^ M ∧
      unitOrbit p ξ M = ⋃ u ∈ T, (fun z => (u : ℤ_[p]) • z) '' coset p ξ M := by
  classical
  obtain ⟨T, hcard, hrep⟩ := exists_unit_residue_representatives p M
  refine ⟨T, hcard, ?_⟩
  ext x
  constructor
  · rintro ⟨u, z, hz, rfl⟩
    obtain ⟨v, hv, huv⟩ := hrep u
    have hx : (u : ℤ_[p]) • z ∈ (fun y => (v : ℤ_[p]) • y) '' coset p ξ M := by
      rw [unit_smul_coset_eq_of_congruent p ξ M v u huv]
      exact ⟨z, hz, rfl⟩
    exact Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨hv, hx⟩⟩
  · intro hx
    obtain ⟨u, hu⟩ := Set.mem_iUnion.mp hx
    obtain ⟨_, z, hz, hzx⟩ := Set.mem_iUnion.mp hu
    exact ⟨u, z, hz, hzx⟩

end CubicTenVariables.PadicUnitOrbit
