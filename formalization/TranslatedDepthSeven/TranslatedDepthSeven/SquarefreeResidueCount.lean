import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import TranslatedDepthSeven.BertrandReservoir
import TranslatedDepthSeven.ReservoirSubpower

/-!
# Exact Chinese-remainder multiplication of residue counts

This file isolates the finite statement used when residue classes are counted
modulo a square-free product.  A residue vector modulo the product is sent,
coordinate by coordinate, through the Chinese-remainder equivalence.  If the
condition imposed on that vector is the conjunction of independent local
conditions, then the number of admissible global vectors is exactly the
product of the local cardinalities.

There is no geometric estimate in this file: the local sets are written down
as literal finite sets.  A later geometric argument may bound their
cardinalities by `C * p ^ d`; the final theorem below then gives the exact
global consequence `C ^ #P * q ^ d`.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coordinatewise Chinese-remainder equivalence, with the two finite
indices transposed on the target side. -/
def crtVectorEquiv (a : ι → ℕ) (hcop : Pairwise (Nat.Coprime on a))
    (N : ℕ) :
    (Fin N → ZMod (∏ i, a i)) ≃ (∀ i, Fin N → ZMod (a i)) where
  toFun y i j := ZMod.prodEquivPi a hcop (y j) i
  invFun z j := (ZMod.prodEquivPi a hcop).symm (fun i ↦ z i j)
  left_inv y := by
    ext j
    exact (ZMod.prodEquivPi a hcop).symm_apply_apply (y j)
  right_inv z := by
    funext i j
    exact congrFun ((ZMod.prodEquivPi a hcop).apply_symm_apply
      (fun i ↦ z i j)) i

/-- The literal finite set of global residue vectors whose image at every
factor belongs to the prescribed local finite set. -/
def crtGlobalResidues (a : ι → ℕ) (hcop : Pairwise (Nat.Coprime on a))
    (hzero : ∀ i, a i ≠ 0) (N : ℕ)
    (R : ∀ i, Finset (Fin N → ZMod (a i))) :
    Finset (Fin N → ZMod (∏ i, a i)) := by
  letI (i : ι) : NeZero (a i) := ⟨hzero i⟩
  letI : NeZero (∏ i, a i) :=
    ⟨Finset.prod_ne_zero_iff.mpr fun i _ ↦ hzero i⟩
  exact Finset.univ.filter fun y ↦ ∀ i, crtVectorEquiv a hcop N y i ∈ R i

omit [DecidableEq ι] in
theorem mem_crtGlobalResidues_iff
    {a : ι → ℕ} {hcop : Pairwise (Nat.Coprime on a)}
    {hzero : ∀ i, a i ≠ 0} {N : ℕ}
    {R : ∀ i, Finset (Fin N → ZMod (a i))}
    {y : Fin N → ZMod (∏ i, a i)} :
    y ∈ crtGlobalResidues a hcop hzero N R ↔
      ∀ i, crtVectorEquiv a hcop N y i ∈ R i := by
  letI (i : ι) : NeZero (a i) := ⟨hzero i⟩
  letI : NeZero (∏ i, a i) :=
    ⟨Finset.prod_ne_zero_iff.mpr fun i _ ↦ hzero i⟩
  simp [crtGlobalResidues]

/-- Chinese remaindering restricts to an equivalence between the admissible
global residue vectors and the product of the prescribed local sets. -/
def crtRestrictedResidueEquiv
    (a : ι → ℕ) (hcop : Pairwise (Nat.Coprime on a))
    (hzero : ∀ i, a i ≠ 0)
    (N : ℕ) (R : ∀ i, Finset (Fin N → ZMod (a i))) :
    {y // y ∈ crtGlobalResidues a hcop hzero N R} ≃
      (∀ i, {z // z ∈ R i}) where
  toFun y i := ⟨crtVectorEquiv a hcop N y i,
    (mem_crtGlobalResidues_iff.mp y.property) i⟩
  invFun z := ⟨(crtVectorEquiv a hcop N).symm (fun i ↦ (z i : _)), by
    rw [mem_crtGlobalResidues_iff]
    intro i
    have hi := congrFun ((crtVectorEquiv a hcop N).apply_symm_apply
      (fun i ↦ (z i : Fin N → ZMod (a i)))) i
    rw [hi]
    exact (z i).property⟩
  left_inv y := by
    apply Subtype.ext
    exact (crtVectorEquiv a hcop N).symm_apply_apply y
  right_inv z := by
    funext i
    apply Subtype.ext
    exact congrFun ((crtVectorEquiv a hcop N).apply_symm_apply
      (fun i ↦ (z i : Fin N → ZMod (a i)))) i

/-- Exact multiplication of independently prescribed local residue counts. -/
theorem card_crtGlobalResidues
    (a : ι → ℕ) (hcop : Pairwise (Nat.Coprime on a))
    (hzero : ∀ i, a i ≠ 0)
    (N : ℕ) (R : ∀ i, Finset (Fin N → ZMod (a i))) :
    (crtGlobalResidues a hcop hzero N R).card = ∏ i, (R i).card := by
  rw [← Fintype.card_coe]
  calc
    Fintype.card {y // y ∈ crtGlobalResidues a hcop hzero N R} =
        Fintype.card (∀ i, {z // z ∈ R i}) :=
      Fintype.card_congr (crtRestrictedResidueEquiv a hcop hzero N R)
    _ = ∏ i, Fintype.card {z // z ∈ R i} := Fintype.card_pi
    _ = ∏ i, (R i).card := by simp

/-- If every local residue set has at most `C * a_i^d` elements, the global
set has at most `C^(# factors) * (product a_i)^d` elements. -/
theorem card_crtGlobalResidues_le_constant_mul_product_pow
    (a : ι → ℕ) (hcop : Pairwise (Nat.Coprime on a))
    (hzero : ∀ i, a i ≠ 0)
    (N d C : ℕ) (R : ∀ i, Finset (Fin N → ZMod (a i)))
    (hlocal : ∀ i, (R i).card ≤ C * (a i) ^ d) :
    (crtGlobalResidues a hcop hzero N R).card ≤
      C ^ Fintype.card ι * (∏ i, a i) ^ d := by
  rw [card_crtGlobalResidues]
  calc
    (∏ i, (R i).card) ≤ ∏ i, C * (a i) ^ d := by
      exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) fun i _ ↦ hlocal i
    _ = C ^ Fintype.card ι * (∏ i, a i) ^ d := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Finset.prod_pow]

/-- Distinct members of a finite set of primes are pairwise coprime when
viewed through the subtype indexing that the finite Chinese remainder theorem
uses. -/
theorem primeSubtype_pairwise_coprime {P : Finset ℕ}
    (hprime : ∀ p ∈ P, p.Prime) :
    Pairwise (Nat.Coprime on fun p : P ↦ (p : ℕ)) := by
  intro p q hpq
  exact (Nat.coprime_primes (hprime p p.property) (hprime q q.property)).mpr
    (fun hpqval ↦ hpq (Subtype.ext hpqval))

theorem primeSubtype_ne_zero {P : Finset ℕ}
    (hprime : ∀ p ∈ P, p.Prime) (p : P) : (p : ℕ) ≠ 0 :=
  (hprime p p.property).ne_zero

/-- The product indexed by the subtype of a finite set is exactly the
`primeProduct` notation used for reservoir moduli.  Naming this equality
keeps later statements on the literal modulus `primeProduct P`. -/
theorem primeSubtype_prod_eq_primeProduct (P : Finset ℕ) :
    (∏ p : P, (p : ℕ)) = primeProduct P := by
  simpa only [primeProduct] using
    (Finset.prod_coe_sort P (fun p : ℕ ↦ p))

/-- The exact square-free-prime specialization.  In particular, a local
`C * p^d` bound gives `C^(#P) * q^d`, where `q` is the literal product of
the primes in `P`. -/
theorem card_squarefreePrime_crtGlobalResidues_le
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (N d C : ℕ)
    (R : ∀ p : P, Finset (Fin N → ZMod (p : ℕ)))
    (hlocal : ∀ p : P, (R p).card ≤ C * (p : ℕ) ^ d) :
    (crtGlobalResidues (fun p : P ↦ (p : ℕ))
      (primeSubtype_pairwise_coprime hprime)
      (primeSubtype_ne_zero hprime) N R).card ≤
      C ^ P.card * (primeProduct P) ^ d := by
  have h := card_crtGlobalResidues_le_constant_mul_product_pow
    (fun p : P ↦ (p : ℕ)) (primeSubtype_pairwise_coprime hprime)
    (primeSubtype_ne_zero hprime) N d C R hlocal
  calc
    (crtGlobalResidues (fun p : P ↦ (p : ℕ))
      (primeSubtype_pairwise_coprime hprime)
      (primeSubtype_ne_zero hprime) N R).card ≤
        C ^ Fintype.card P * (∏ p : P, (p : ℕ)) ^ d := h
    _ = C ^ P.card * (primeProduct P) ^ d := by
      rw [Fintype.card_coe, primeSubtype_prod_eq_primeProduct]

/-- The fixed local constant is subpower when the number of prime factors is
at most the logarithmic reservoir depth.  This is the exact quantitative
form of the `H^o(1)` factor in the square-free residue count. -/
theorem card_squarefreePrime_crtGlobalResidues_cast_le_rpow_mul
    {M0 ε H : ℝ} (hM0 : 0 ≤ M0) (hε : 0 < ε)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (N d C : ℕ) (hC : 1 ≤ C)
    (hPcard : P.card ≤ reservoirDepth M0 H)
    (hH : reservoirSubpowerThreshold M0 (C : ℝ) ε ≤ H)
    (R : ∀ p : P, Finset (Fin N → ZMod (p : ℕ)))
    (hlocal : ∀ p : P, (R p).card ≤ C * (p : ℕ) ^ d) :
    ((crtGlobalResidues (fun p : P ↦ (p : ℕ))
      (primeSubtype_pairwise_coprime hprime)
      (primeSubtype_ne_zero hprime) N R).card : ℝ) ≤
      H ^ ε * (primeProduct P : ℝ) ^ d := by
  have hfinite := card_squarefreePrime_crtGlobalResidues_le
    P hprime N d C R hlocal
  have hfiniteCast :
      ((crtGlobalResidues (fun p : P ↦ (p : ℕ))
        (primeSubtype_pairwise_coprime hprime)
        (primeSubtype_ne_zero hprime) N R).card : ℝ) ≤
        (C : ℝ) ^ P.card * (primeProduct P : ℝ) ^ d := by
    exact_mod_cast hfinite
  have hCpowNat : C ^ P.card ≤ C ^ reservoirDepth M0 H :=
    Nat.pow_le_pow_right hC hPcard
  have hCpow : (C : ℝ) ^ P.card ≤
      (C : ℝ) ^ reservoirDepth M0 H := by
    exact_mod_cast hCpowNat
  have hsub : (C : ℝ) ^ reservoirDepth M0 H ≤ H ^ ε :=
    reservoirBase_pow_depth_le_rpow hM0 (by exact_mod_cast hC) hε hH
  exact hfiniteCast.trans
    (mul_le_mul_of_nonneg_right (hCpow.trans hsub) (by positivity))

end

end TranslatedDepthSeven
