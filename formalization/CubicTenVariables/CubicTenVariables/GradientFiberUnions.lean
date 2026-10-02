import CubicTenVariables.IntegralGradientFibers
import Mathlib.Data.Set.Card.Arithmetic

/-! Exact finite-union and monotonicity statements for actual gradient residue
fibers. Overlaps are allowed: the upper bound counts each patch separately. -/

noncomputable section
namespace CubicTenVariables.GradientFiberUnions

open MvPolynomial IntegralGradientFibers LocalCongruenceFibers

variable (p : ℕ) [Fact p.Prime] {n r : ℕ}
variable (F : MvPolynomial (Fin n) ℤ) (rows cols : Fin r → Fin n)
variable (s : ℕ) (u : (ZMod (p ^ s))ˣ)
variable (b : Untouched cols → ZMod (p ^ s)) (c : Fin r → ZMod (p ^ s))

theorem unitModularFiber_mono {U V : Set (Fin n → ℤ_[p])} (hUV : U ⊆ V) :
    unitModularFiber p F rows cols s U u b c ⊆
      unitModularFiber p F rows cols s V u b c := by
  rintro v ⟨hb, hc, z, hz, hv⟩
  exact ⟨hb, hc, z, hUV hz, hv⟩

theorem card_unitModularFiber_mono {U V : Set (Fin n → ℤ_[p])} (hUV : U ⊆ V) :
    Nat.card (unitModularFiber p F rows cols s U u b c) ≤
      Nat.card (unitModularFiber p F rows cols s V u b c) :=
  Set.ncard_le_ncard (unitModularFiber_mono p F rows cols s u b c hUV)

set_option maxHeartbeats 800000 in
theorem unitModularFiber_biUnion {ι : Type*} (T : Finset ι)
    (U : ι → Set (Fin n → ℤ_[p])) :
    unitModularFiber p F rows cols s (⋃ i ∈ T, U i) u b c =
      ⋃ i ∈ T, unitModularFiber p F rows cols s (U i) u b c := by
  ext v
  constructor
  · rintro ⟨hb, hc, z, hz, hv⟩
    obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hi, hz⟩ := Set.mem_iUnion.mp hzi
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hb, hc, z, hz, hv⟩⟩
  · intro hv
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hv
    obtain ⟨hiT, hb, hc, z, hz, hv⟩ := Set.mem_iUnion.mp hi
    exact ⟨hb, hc, z, Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hiT, hz⟩⟩, hv⟩

theorem card_unitModularFiber_biUnion_le {ι : Type*} (T : Finset ι)
    (U : ι → Set (Fin n → ℤ_[p])) :
    Nat.card (unitModularFiber p F rows cols s (⋃ i ∈ T, U i) u b c) ≤
      ∑ i ∈ T, Nat.card (unitModularFiber p F rows cols s (U i) u b c) := by
  rw [unitModularFiber_biUnion]
  exact Finset.set_ncard_biUnion_le T _

/-- A finite family of patches, each with the same actual fiber bound,
gives the cardinality of the family times that bound. -/
theorem card_unitModularFiber_biUnion_le_uniform {ι : Type*} (T : Finset ι)
    (U : ι → Set (Fin n → ℤ_[p])) (K : ℕ)
    (hK : ∀ i ∈ T, Nat.card (unitModularFiber p F rows cols s (U i) u b c) ≤ K) :
    Nat.card (unitModularFiber p F rows cols s (⋃ i ∈ T, U i) u b c) ≤ T.card * K := by
  apply (card_unitModularFiber_biUnion_le p F rows cols s u b c T U).trans
  calc
    (∑ i ∈ T, Nat.card (unitModularFiber p F rows cols s (U i) u b c)) ≤
        ∑ _i ∈ T, K := Finset.sum_le_sum hK
    _ = T.card * K := by simp

end CubicTenVariables.GradientFiberUnions
