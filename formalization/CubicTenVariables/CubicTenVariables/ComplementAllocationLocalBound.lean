import CubicTenVariables.ComplementLowModulusSum
import CubicTenVariables.ComplementFrequencyPieces
import CubicTenVariables.NumericalDepthAllocation

/-! Actual low-factor bounds for the complementary depth allocation.
The numerical depths are evaluated at the original integer frequency;
no residue invariance of the square depth is used. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ComplementAllocationLocalBound
open MvPolynomial NumericalPrimeDepth
open scoped BigOperators

variable {F : MvPolynomial (Fin 10) ℤ} {C : ℝ}

private theorem exceptional_product_le_gcd (a Δ : ℕ) (ha : a ≠ 0) :
    (∏ p ∈ a.primeFactors, if p ∣ Δ then (p : ℝ) else 1) ≤ (a.gcd Δ : ℝ) := by
  have hg : a.gcd Δ ≠ 0 := (Nat.gcd_pos_of_pos_left Δ (Nat.pos_of_ne_zero ha)).ne'
  have hsub : a.primeFactors.filter (fun p => p ∣ Δ) ⊆ (a.gcd Δ).primeFactors := by
    intro p hp
    obtain ⟨hp,hpΔ⟩ := Finset.mem_filter.mp hp
    exact (Nat.prime_of_mem_primeFactors hp).mem_primeFactors
      (Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) hpΔ) hg
  have hd : (∏ p ∈ a.primeFactors.filter (fun p => p ∣ Δ), p) ∣ a.gcd Δ :=
    (Finset.prod_dvd_prod_of_subset _ _ (fun p : ℕ => p) hsub).trans
      (Nat.prod_primeFactors_dvd (a.gcd Δ))
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hg) hd
  rw [← Finset.prod_filter, ← Nat.cast_prod]
  exact_mod_cast hle

/-- A prime below allocation threshold i+2 costs at most one exceptional
prime factor beyond the generic exponent (11+i)/2. -/
theorem prime_low_bound (h : CoarseBounds F C) (i : ℕ) (v : Fin 10 → ℤ)
    (Δ p : ℕ) [Fact p.Prime]
    (hcert : i+1 ≤ primeDepth h p v → p ∣ Δ)
    (hlow : primeDepth h p v ≤ i+1) :
    ‖completeCubicSum F p v‖ ≤ C*(p : ℝ)^((11+(i : ℝ))/2)*
      (if p ∣ Δ then (p : ℝ) else 1) := by
  have hp : p.Prime := Fact.out
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  by_cases hpΔ : p ∣ Δ
  · rw [if_pos hpΔ]
    have he : ((11 : ℝ)+((i+1 : ℕ) : ℝ))/2 ≤ (11+(i : ℝ))/2+1 := by
      push_cast
      linarith
    have hh := (primeDepth_le_iff h p v (i+1)).mp hlow
    calc
      _ ≤ C*(p : ℝ)^((11+(i : ℝ))/2+1) := hh.trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hp1 he)
          (zero_le_one.trans h.constant_pos))
      _ = _ := by rw [Real.rpow_add hp0,Real.rpow_one]; ring
  · have hd : primeDepth h p v ≤ i := by
      by_contra hn
      exact hpΔ (hcert (by omega))
    simpa only [if_neg hpΔ,mul_one] using (primeDepth_le_iff h p v i).mp hd

/-- The exact low-depth square exponent is 12+i=10+r, with no exceptional
square-prime gcd factor. -/
theorem square_low_bound (h : CoarseBounds F C) (i : ℕ) (v : Fin 10 → ℤ)
    (p : ℕ) [Fact p.Prime] (hlow : squareDepth h p v ≤ i+1) :
    ‖completeCubicSum F (p^2) v‖ ≤ C*(p : ℝ)^(12+(i : ℝ)) := by
  have hh := (squareDepth_le_iff h p v (i+1)).mp hlow
  rw [show (12+(i : ℝ)) = ((11+(i+1) : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]
  exact hh

/-- Exact same-frequency CRT converts the actual low-depth local bounds
into a single ordinary-prime gcd factor. -/
theorem low_complete_sum_bound (h : CoarseBounds F C) (hF : F.IsHomogeneous 3)
    (i : ℕ) (v : Fin 10 → ℤ) (Δ : ℕ)
    (hcert : ∀ (p : ℕ) [Fact p.Prime], i+1 ≤ primeDepth h p v → p ∣ Δ)
    (a b : ℕ) (ha : Squarefree a) (hb : Squarefree b) (hab : a.Coprime b)
    (halow : ∀ p ∈ a.primeFactors, NumericalConductor.primeDepth h p v ≤ i+1)
    (hblow : ∀ p ∈ b.primeFactors, NumericalConductor.squareDepth h p v ≤ i+1) :
    ‖completeCubicSum F (a*b^2) v‖ ≤
      C^(a.primeFactors.card+b.primeFactors.card)*(a : ℝ)^((11+(i : ℝ))/2)*
        (b : ℝ)^(12+(i : ℝ))*(a.gcd Δ : ℝ) := by
  have hpa (p : ℕ) (hp : p ∈ a.primeFactors) :
      ‖completeCubicSum F p v‖ ≤ C*(p : ℝ)^((11+(i : ℝ))/2)*
        (if p ∣ Δ then (p : ℝ) else 1) := by
    letI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    apply prime_low_bound h i v Δ p (hcert p)
    simpa only [NumericalConductor.primeDepth_of_prime] using halow p hp
  have hpb (p : ℕ) (hp : p ∈ b.primeFactors) :
      ‖completeCubicSum F (p^2) v‖ ≤ C*(p : ℝ)^(12+(i : ℝ)) := by
    letI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    apply square_low_bound h i v p
    simpa only [NumericalConductor.squareDepth_of_prime] using hblow p hp
  have hp := Finset.prod_le_prod (fun p (_ : p ∈ a.primeFactors) =>
    norm_nonneg (completeCubicSum F p v)) hpa
  have hs := Finset.prod_le_prod (fun p (_ : p ∈ b.primeFactors) =>
    norm_nonneg (completeCubicSum F (p^2) v)) hpb
  have hpow (q : ℕ) (hq : Squarefree q) (e : ℝ) :
      (∏ p ∈ q.primeFactors, (p : ℝ)^e) = (q : ℝ)^e := by
    rw [Real.finset_prod_rpow _ _ (fun p _ => Nat.cast_nonneg p)]
    congr 1
    rw [← Nat.cast_prod,Nat.prod_primeFactors_of_squarefree hq]
  simp only [Finset.prod_mul_distrib,Finset.prod_const,hpow a ha] at hp
  simp only [Finset.prod_mul_distrib,Finset.prod_const,hpow b hb] at hs
  have hp' : (∏ p ∈ a.primeFactors, ‖completeCubicSum F p v‖) ≤
      C^a.primeFactors.card*(a : ℝ)^((11+(i : ℝ))/2)*(a.gcd Δ : ℝ) :=
    hp.trans (mul_le_mul_of_nonneg_left (exceptional_product_le_gcd a Δ ha.ne_zero)
      (by have := h.constant_pos; positivity))
  rw [CompleteSumMultiplicativity.norm_squarefree_pair_product F hF a b ha hb hab v]
  calc
    _ ≤ (C^a.primeFactors.card*(a : ℝ)^((11+(i : ℝ))/2)*(a.gcd Δ : ℝ))*
        (C^b.primeFactors.card*(b : ℝ)^(12+(i : ℝ))) :=
      mul_le_mul hp' hs (Finset.prod_nonneg fun _ _ => norm_nonneg _)
        (by have := h.constant_pos; positivity)
    _ = _ := by rw [pow_add]; ring

/-- The low-modulus arithmetic sum is proved for the literal rational
piece and actual least numerical depths. Its certificate is constructed
from the supplied common microlocal data, not assumed as an average. -/
theorem exists_low_sum_bound {t : ℕ}
    {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
    {T : ∀ k : Fin 4, MicrolocalPromotionTable.Table F f (k.val+1)}
    {N d : ℕ} {h : CoarseBounds F C}
    (hF : F.IsHomogeneous 3) (hc : MicrolocalConductorDepth.Conclusion F f T N C d h)
    (i : Fin 5) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ v : Fin 10 → ℤ,
      (fun k => (v k : ℚ)) ∈ ComplementFrequencyPieces.piece F f T i →
      ∀ D H : ℝ, 1 ≤ D → 1 ≤ H → (∀ k, |(v k : ℝ)| ≤ H) →
      ∀ Q : Finset (ℕ × ℕ),
        (∀ x ∈ Q, Squarefree x.1 ∧ Squarefree x.2 ∧ x.1.Coprime x.2 ∧
          (x.1 : ℝ)*(x.2 : ℝ)^2 ≤ 2*D ∧
          (∀ p ∈ x.1.primeFactors, NumericalConductor.primeDepth h p v ≤ i.val+1) ∧
          (∀ p ∈ x.2.primeFactors, NumericalConductor.squareDepth h p v ≤ i.val+1)) →
        (∑ x ∈ Q, ‖completeCubicSum F (x.1*x.2^2) v‖) ≤
          M*(D*H)^ε*D^((13+(i.val : ℝ))/2) := by
  obtain ⟨M,hM,hbound⟩ := ComplementLowModulusSum.exists_weighted_bound
    ((11+(i.val : ℝ))/2) (by positivity) C h.constant_pos d ε hε
  refine ⟨M,hM,?_⟩
  intro v hv D H hD hH hvH Q hQ
  obtain ⟨Δ,hΔ,hheight,hcert,_⟩ := ComplementFrequencyPieces.exists_prime_certificate T hc i v hv
  have he₁ : 2*((11+(i.val : ℝ))/2)+1 = 12+(i.val : ℝ) := by ring
  have he₂ : (11+(i.val : ℝ))/2+1 = (13+(i.val : ℝ))/2 := by ring
  calc
    _ ≤ ∑ x ∈ Q, C^(x.1.primeFactors.card+x.2.primeFactors.card)*
        (x.1 : ℝ)^((11+(i.val : ℝ))/2)*(x.2 : ℝ)^(12+(i.val : ℝ))*
        (Nat.gcd x.1 Δ : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      obtain ⟨ha,hb,hab,_,hla,hlb⟩ := hQ x hx
      exact low_complete_sum_bound h hF i.val v Δ hcert x.1 x.2 ha hb hab hla hlb
    _ ≤ _ := by
      have hb := hbound D H hD hH Δ hΔ (hheight H hH hvH) Q (fun x hx =>
        ⟨Nat.one_le_iff_ne_zero.mpr (hQ x hx).1.ne_zero,
          Nat.one_le_iff_ne_zero.mpr (hQ x hx).2.1.ne_zero,(hQ x hx).2.2.2.1⟩)
      simpa only [he₁,he₂] using hb

end CubicTenVariables.ComplementAllocationLocalBound
