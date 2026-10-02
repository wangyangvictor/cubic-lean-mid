import CubicTenVariables.LiftingCharacters
import Mathlib.Data.Nat.Totient

/-! The exact finite Ramanujan divisor switch for the project's positive
integer-representative exponential. The proof partitions all residues by
their gcd with the modulus; it assumes no analytic or literature input. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.RamanujanDivisorSwitch
open scoped BigOperators
open Finset

/-- The literal primitive scalar sum, including modulus one. -/
def ramanujan (q : ℕ) (m : ℤ) : ℂ :=
  ∑ a : Fin q, if Nat.Coprime a.val q then
    residueExponential q ((a.val : ℤ)*m) else 0

theorem ramanujan_eq_range (q : ℕ) (m : ℤ) :
    ramanujan q m = ∑ a ∈ (range q).filter (fun a => q.Coprime a),
      residueExponential q ((a : ℤ)*m) := by
  classical
  simp only [ramanujan,sum_filter,Nat.coprime_comm]
  exact Fin.sum_univ_eq_sum_range
    (fun a => if q.Coprime a then residueExponential q ((a : ℤ)*m) else 0) q

/-- Multiplication by the gcd identifies each reduced-residue sum with the
corresponding fiber in the complete scalar sum. -/
theorem ramanujan_div_eq_gcd_fiber (r d : ℕ) (hr : 0 < r) (hd : d ∣ r) (m : ℤ) :
    ramanujan (r/d) m = ∑ a ∈ (range r).filter (fun a => r.gcd a = d),
      residueExponential r ((a : ℤ)*m) := by
  classical
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hr
  letI : NeZero d := ⟨hd0.ne'⟩
  obtain ⟨x,rfl⟩ := hd
  rw [Nat.mul_div_cancel_left x hd0,ramanujan_eq_range]
  apply Finset.sum_bij (fun a _ => d*a)
  · simp only [mem_filter,mem_range,Nat.Coprime]
    intro a ha
    refine ⟨by gcongr; exact ha.1,?_⟩
    rw [Nat.gcd_mul_left,ha.2,mul_one]
  · intro a ha b hb hab
    exact Nat.eq_of_mul_eq_mul_left hd0 hab
  · simp only [mem_filter,mem_range]
    intro b hb
    have hdb : d ∣ b := by rw [← hb.2]; exact Nat.gcd_dvd_right _ _
    obtain ⟨a,rfl⟩ := hdb
    refine ⟨a,⟨?_,?_⟩,rfl⟩
    · exact (mul_lt_mul_iff_right₀ hd0).mp hb.1
    · change x.gcd a = 1
      have hg := hb.2
      rw [Nat.gcd_mul_left] at hg
      exact Nat.eq_of_mul_eq_mul_left hd0 (hg.trans (mul_one d).symm)
  · intro a ha
    symm
    rw [mul_comm d x]
    have he : ((d*a : ℕ) : ℤ)*m = (d : ℤ)*((a : ℤ)*m) := by push_cast; ring
    rw [he,LiftingCharacters.residueExponential_mul_modulus]

/-- The finite divisor identity for every positive modulus and every
integer argument, including zero and negative arguments. -/
theorem sum_divisors (r : ℕ) (hr : 0 < r) (m : ℤ) :
    (∑ q ∈ r.divisors, ramanujan q m) =
      if (r : ℤ) ∣ m then (r : ℂ) else 0 := by
  classical
  letI : NeZero r := ⟨hr.ne'⟩
  rw [← Nat.sum_div_divisors r (fun q => ramanujan q m)]
  calc
    _ = ∑ d ∈ r.divisors, ∑ a ∈ (range r).filter (fun a => r.gcd a = d),
        residueExponential r ((a : ℤ)*m) := by
      apply sum_congr rfl
      intro d hd
      exact ramanujan_div_eq_gcd_fiber r d hr (Nat.dvd_of_mem_divisors hd) m
    _ = ∑ a ∈ range r, residueExponential r ((a : ℤ)*m) := by
      apply sum_fiberwise_of_maps_to
      intro a ha
      exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _,hr.ne'⟩
    _ = _ := by
      rw [← Fin.sum_univ_eq_sum_range]
      exact LiftingCharacters.sum_scalar_phase r m

/-- Expanded original-representative version of the divisor switch. -/
theorem sum_divisors_primitive (r : ℕ) (hr : 0 < r) (m : ℤ) :
    (∑ q ∈ r.divisors, ∑ a : Fin q, if Nat.Coprime a.val q then
      residueExponential q ((a.val : ℤ)*m) else 0) =
        if (r : ℤ) ∣ m then (r : ℂ) else 0 :=
  sum_divisors r hr m

/-- The manuscript's representatives `1 ≤ a ≤ q` give the same primitive
sum as `0 ≤ a < q`, including the endpoint at modulus one. -/
theorem ramanujan_eq_Icc (q : ℕ) (hq : 0 < q) (m : ℤ) :
    ramanujan q m = ∑ a ∈ Icc 1 q, if Nat.Coprime a q then
      residueExponential q ((a : ℤ)*m) else 0 := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  let f : ℕ → ℂ := fun a => if Nat.Coprime a q then
    residueExponential q ((a : ℤ)*m) else 0
  have hend : f 0 = f q := by
    by_cases hq1 : q = 1
    · subst q
      simp [f,PrimeSumAdapter.residueExponential_eq_stdAddChar]
    · simp [f,hq1]
  have hrange : ramanujan q m = ∑ a ∈ range q, f a := by
    rw [ramanujan_eq_range,sum_filter]
    simp only [f,Nat.coprime_comm]
  rw [hrange,sum_range_eq_add_Ico f hq,hend]
  exact add_sum_Ico_eq_sum_Icc hq

/-- Divisor switch with the literal numerator range `1,...,q`. -/
theorem sum_divisors_Icc (r : ℕ) (hr : 0 < r) (m : ℤ) :
    (∑ q ∈ r.divisors, ∑ a ∈ Icc 1 q, if Nat.Coprime a q then
      residueExponential q ((a : ℤ)*m) else 0) =
        if (r : ℤ) ∣ m then (r : ℂ) else 0 := by
  classical
  rw [← sum_divisors r hr m]
  apply sum_congr rfl
  intro q hq
  exact (ramanujan_eq_Icc q (Nat.pos_of_mem_divisors hq) m).symm

end CubicTenVariables.RamanujanDivisorSwitch
