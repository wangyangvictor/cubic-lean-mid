import CubicTenVariables.RamanujanDivisorSwitch
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Finite weighted divisor switching for the delta construction. All sums
and weights are literal; no convergence or analytic kernel hypothesis enters. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.FiniteDeltaDivisorIdentity
open Finset RamanujanDivisorSwitch
open scoped BigOperators

/-- Reindex the positive pairs `(q,j)` by `(r=q*j,q)`. -/
theorem reindex (Q : ℕ) (F : ℕ → ℕ → ℂ) :
    (∑ q ∈ Icc 1 Q, ∑ j ∈ Icc 1 (Q/q), F (q*j) q) =
      ∑ r ∈ Icc 1 Q, ∑ q ∈ r.divisors, F r q := by
  classical
  rw [sum_sigma',sum_sigma']
  apply sum_bij (fun (a : Σ _ : ℕ, ℕ) _ => (⟨a.1*a.2,a.1⟩ : Σ _ : ℕ, ℕ))
  · rintro ⟨q,j⟩ ha
    simp only [mem_sigma,mem_Icc] at ha ⊢
    have hq : 0 < q := ha.1.1
    have hj : 0 < j := ha.2.1
    refine ⟨⟨Nat.mul_pos hq hj,?_⟩,Nat.mem_divisors.mpr ⟨dvd_mul_right q j,?_⟩⟩
    · simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hq).mp ha.2.2
    · exact (Nat.mul_pos hq hj).ne'
  · rintro ⟨q,j⟩ ha ⟨q',j'⟩ hb he
    have hq : q = q' := congrArg (fun a : Σ _ : ℕ, ℕ => a.2) he
    have hm : q*j = q'*j' := congrArg (fun a : Σ _ : ℕ, ℕ => a.1) he
    subst q'
    have hq0 : 0 < q := (mem_Icc.mp (mem_sigma.mp ha).1).1
    have hj := Nat.eq_of_mul_eq_mul_left hq0 hm
    subst j'
    rfl
  · rintro ⟨r,q⟩ hb
    obtain ⟨hr,hq⟩ := mem_sigma.mp hb
    obtain ⟨hr0,hrQ⟩ := mem_Icc.mp hr
    have hqr : q ∣ r := Nat.dvd_of_mem_divisors hq
    have hq0 : 0 < q := Nat.pos_of_mem_divisors hq
    have hqrle : q ≤ r := Nat.le_of_dvd hr0 hqr
    refine ⟨⟨q,r/q⟩,mem_sigma.mpr ⟨mem_Icc.mpr ⟨hq0,hqrle.trans hrQ⟩,
      mem_Icc.mpr ⟨Nat.div_pos hqrle hq0,Nat.div_le_div_right hrQ⟩⟩,?_⟩
    simp only [Nat.mul_div_cancel' hqr]
  · intro a ha
    rfl

/-- The exact weighted divisor identity, with `q*j` in the denominator.
The cutoff may be zero, in which case both sides are empty sums. -/
theorem weighted_switch (Q : ℕ) (m : ℤ) (f : ℕ → ℂ) :
    (∑ q ∈ Icc 1 Q, ramanujan q m *
      ∑ j ∈ Icc 1 (Q/q), f (q*j)/(q*j : ℕ)) =
        ∑ r ∈ Icc 1 Q, if (r : ℤ) ∣ m then f r else 0 := by
  classical
  simp_rw [mul_sum]
  rw [reindex Q (fun r q => ramanujan q m * (f r/(r : ℂ)))]
  apply sum_congr rfl
  intro r hr
  have hr0 : 0 < r := (mem_Icc.mp hr).1
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  rw [← sum_mul,sum_divisors r hr0 m]
  split_ifs
  · field_simp
  · simp

/-- Literal primitive exponential version of the finite weighted switch. -/
theorem weighted_switch_primitive (Q : ℕ) (m : ℤ) (f : ℕ → ℂ) :
    (∑ q ∈ Icc 1 Q,
      (∑ a : Fin q, if Nat.Coprime a.val q then
        residueExponential q ((a.val : ℤ)*m) else 0) *
      ∑ j ∈ Icc 1 (Q/q), f (q*j)/(q*j : ℕ)) =
        ∑ r ∈ Icc 1 Q, if (r : ℤ) ∣ m then f r else 0 :=
  weighted_switch Q m f

/-- Weighted switch with the manuscript numerator representatives `1,...,q`. -/
theorem weighted_switch_Icc (Q : ℕ) (m : ℤ) (f : ℕ → ℂ) :
    (∑ q ∈ Icc 1 Q,
      (∑ a ∈ Icc 1 q, if Nat.Coprime a q then
        residueExponential q ((a : ℤ)*m) else 0) *
      ∑ j ∈ Icc 1 (Q/q), f (q*j)/(q*j : ℕ)) =
        ∑ r ∈ Icc 1 Q, if (r : ℤ) ∣ m then f r else 0 := by
  classical
  rw [← weighted_switch Q m f]
  apply sum_congr rfl
  intro q hq
  rw [ramanujan_eq_Icc q (mem_Icc.mp hq).1 m]

/-- Complementary divisors preserve the exact real-scaled weight. The real
scale may be zero: the identity uses the field's usual total division. -/
theorem complementary_divisors (n : ℕ) (Q : ℝ) (ω : ℝ → ℂ) :
    (∑ d ∈ n.divisors, ω ((d : ℝ)/Q)) =
      ∑ d ∈ n.divisors, ω ((n : ℝ)/((d : ℝ)*Q)) := by
  classical
  rw [← Nat.sum_div_divisors n (fun d => ω ((d : ℝ)/Q))]
  apply sum_congr rfl
  intro d hd
  rw [Nat.cast_div_charZero (Nat.dvd_of_mem_divisors hd),div_div]

/-- The same complementary-divisor identity for an arbitrary integer. -/
theorem complementary_divisors_natAbs (m : ℤ) (Q : ℝ) (ω : ℝ → ℂ) :
    (∑ d ∈ m.natAbs.divisors, ω ((d : ℝ)/Q)) =
      ∑ d ∈ m.natAbs.divisors, ω ((m.natAbs : ℝ)/((d : ℝ)*Q)) :=
  complementary_divisors m.natAbs Q ω

end CubicTenVariables.FiniteDeltaDivisorIdentity
