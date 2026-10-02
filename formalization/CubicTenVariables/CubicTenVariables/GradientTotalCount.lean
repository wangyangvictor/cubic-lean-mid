import CubicTenVariables.GradientFiberUnions

/-! Summing the proved selected-coordinate fiber bound over the actual
untouched coordinate residues. This recovers the factor p^(s*(n-r)) used in
the local stationary-phase argument. -/

noncomputable section
namespace CubicTenVariables.GradientTotalCount

open MvPolynomial IntegralGradientFibers LocalCongruenceFibers

attribute [local instance] Classical.propDecidable

variable (p : ℕ) [Fact p.Prime] {n r : ℕ}

/-- Actual gradient residues with a lift in the patch, without fixing the
untouched coordinate tuple. -/
def gradientFiber (F : MvPolynomial (Fin n) ℤ) (rows : Fin r → Fin n)
    (s : ℕ) (U : Set (Fin n → ℤ_[p])) (u : (ZMod (p ^ s))ˣ)
    (c : Fin r → ZMod (p ^ s)) : Set (Fin n → ZMod (p ^ s)) :=
  {v | (∀ a, (u : ZMod (p ^ s)) * modularSelectedGradient p F rows s v a = c a) ∧
    ∃ z ∈ U, ∀ k, PadicInt.toZModPow s (z k) = v k}

theorem gradientFiber_eq_iUnion (F : MvPolynomial (Fin n) ℤ)
    (rows cols : Fin r → Fin n) (s : ℕ) (U : Set (Fin n → ℤ_[p]))
    (u : (ZMod (p ^ s))ˣ) (c : Fin r → ZMod (p ^ s)) :
    gradientFiber p F rows s U u c =
      ⋃ b : Untouched cols → ZMod (p ^ s), unitModularFiber p F rows cols s U u b c := by
  ext v
  constructor
  · rintro ⟨hc, hlift⟩
    exact Set.mem_iUnion.mpr ⟨fun j => v j.1, fun _ => rfl, hc, hlift⟩
  · intro hv
    obtain ⟨b, hb, hc, hlift⟩ := Set.mem_iUnion.mp hv
    exact ⟨hc, hlift⟩

theorem card_untouched (cols : Fin r → Fin n) (hc : Function.Injective cols) :
    Fintype.card (Untouched cols) = n - r := by
  have hrange : Fintype.card (Set.range cols) = r := by
    rw [← Fintype.card_congr (Equiv.ofInjective cols hc), Fintype.card_fin]
  change Fintype.card {j : Fin n // ¬ j ∈ Set.range cols} = _
  rw [Fintype.card_subtype_compl, Fintype.card_fin, hrange]

/-- Fixing the untouched residues loses exactly the factor p^(s*(n-r)). -/
theorem card_gradientFiber_le (F : MvPolynomial (Fin n) ℤ)
    (rows cols : Fin r → Fin n) (hcols : Function.Injective cols)
    (s : ℕ) (U : Set (Fin n → ℤ_[p])) (u : (ZMod (p ^ s))ˣ)
    (c : Fin r → ZMod (p ^ s)) (K : ℕ)
    (hK : ∀ b : Untouched cols → ZMod (p ^ s),
      Nat.card (unitModularFiber p F rows cols s U u b c) ≤ K) :
    Nat.card (gradientFiber p F rows s U u c) ≤ K * p ^ (s * (n - r)) := by
  rw [gradientFiber_eq_iUnion p F rows cols]
  apply (Set.ncard_iUnion_le_of_fintype
    (fun b => unitModularFiber p F rows cols s U u b c)).trans
  calc
    (∑ b : Untouched cols → ZMod (p ^ s),
        (unitModularFiber p F rows cols s U u b c).ncard) ≤
        ∑ _b : Untouched cols → ZMod (p ^ s), K :=
      Finset.sum_le_sum (fun b _ => hK b)
    _ = K * p ^ (s * (n - r)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        ZMod.card, card_untouched cols hcols, nsmul_eq_mul, ← pow_mul]
      exact Nat.mul_comm _ _

/-- A full gradient congruence implies the corresponding selected-row
congruence, preserving the actual lift and residue tuple. -/
theorem full_gradientFiber_subset (F : MvPolynomial (Fin n) ℤ)
    (rows : Fin r → Fin n) (s : ℕ) (U : Set (Fin n → ℤ_[p]))
    (u : (ZMod (p ^ s))ˣ) (c : Fin n → ZMod (p ^ s)) :
    gradientFiber p F id s U u c ⊆
      gradientFiber p F rows s U u (fun a => c (rows a)) := by
  rintro v ⟨hc, hlift⟩
  exact ⟨fun a => hc (rows a), hlift⟩

theorem card_full_gradientFiber_le (F : MvPolynomial (Fin n) ℤ)
    (rows cols : Fin r → Fin n) (hcols : Function.Injective cols)
    (s : ℕ) (U : Set (Fin n → ℤ_[p])) (u : (ZMod (p ^ s))ˣ)
    (c : Fin n → ZMod (p ^ s)) (K : ℕ)
    (hK : ∀ b : Untouched cols → ZMod (p ^ s),
      Nat.card (unitModularFiber p F rows cols s U u b (fun a => c (rows a))) ≤ K) :
    Nat.card (gradientFiber p F id s U u c) ≤ K * p ^ (s * (n - r)) :=
  (Set.ncard_le_ncard (full_gradientFiber_subset p F rows s U u c)).trans
    (card_gradientFiber_le p F rows cols hcols s U u (fun a => c (rows a)) K hK)

end CubicTenVariables.GradientTotalCount
