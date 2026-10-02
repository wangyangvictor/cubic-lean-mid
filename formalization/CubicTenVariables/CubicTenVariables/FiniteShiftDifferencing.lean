import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-! Finite-shift Cauchy--Schwarz without omitting diagonal or negative shifts.
The shift family is indexed: repeated shifts modulo a small modulus are allowed.
This is the elementary analytic step of van der Corput differencing. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.FiniteShiftDifferencing
open scoped BigOperators

private theorem mul_conj_re (z : ℂ) :
    (z * starRingEnd ℂ z).re = ‖z‖^2 := by
  rw [Complex.mul_conj]
  exact Complex.normSq_eq_norm_sq z

/-- Cauchy--Schwarz followed by the triangle inequality for the exact
double correlation sum. No pointwise bound on the complex values is assumed. -/
theorem norm_sum_sum_sq_le {G I : Type*} [Fintype G] [Fintype I]
    (u : I → G → ℂ) :
    ‖∑ x, ∑ i, u i x‖^2 ≤ (Fintype.card G : ℝ) *
      ∑ i, ∑ j, ‖∑ x, u i x * starRingEnd ℂ (u j x)‖ := by
  classical
  have hcs : ‖∑ x, ∑ i, u i x‖^2 ≤
      (Fintype.card G : ℝ) * ∑ x, ‖∑ i, u i x‖^2 := by
    calc
      _ ≤ (∑ x, ‖∑ i, u i x‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := by simpa using
        (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
          (f := fun x : G => ‖∑ i, u i x‖))
  apply hcs.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have heq : (∑ x, ‖∑ i, u i x‖^2) =
      ∑ i, ∑ j, (∑ x, u i x * starRingEnd ℂ (u j x)).re := by
    simp_rw [← mul_conj_re, map_sum, Finset.sum_mul, Finset.mul_sum]
    change (∑ x, Complex.reAddGroupHom (∑ i, ∑ j,
      u i x * starRingEnd ℂ (u j x))) =
        ∑ i, ∑ j, Complex.reAddGroupHom (∑ x,
          u i x * starRingEnd ℂ (u j x))
    simp_rw [map_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_comm
  rw [heq]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Complex.re_le_norm _

/-- The exact finite-shift bound on an arbitrary finite additive group.
Every ordered pair of shifts is retained, including equal shifts. -/
theorem card_sq_mul_norm_sum_sq_le {G I : Type*}
    [AddCommGroup G] [Fintype G] [Fintype I]
    (f : G → ℂ) (shift : I → G) :
    (Fintype.card I : ℝ)^2 * ‖∑ x, f x‖^2 ≤
      (Fintype.card G : ℝ) *
        ∑ i, ∑ j, ‖∑ x, f (x + (shift i - shift j)) * starRingEnd ℂ (f x)‖ := by
  classical
  have hshift (i : I) : (∑ x, f (x + shift i)) = ∑ x, f x :=
    Equiv.sum_comp (Equiv.addRight (shift i)) f
  have havg : (∑ x, ∑ i, f (x + shift i)) =
      (Fintype.card I : ℂ) * ∑ x, f x := by
    rw [Finset.sum_comm]
    simp only [hshift, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcorr (i j : I) :
      (∑ x, f (x + shift i) * starRingEnd ℂ (f (x + shift j))) =
        ∑ x, f (x + (shift i - shift j)) * starRingEnd ℂ (f x) := by
    convert Equiv.sum_comp (Equiv.addRight (shift j))
      (fun x => f (x + (shift i - shift j)) * starRingEnd ℂ (f x)) using 1
    congr 1
    ext x
    congr 2
    change x + shift i = (x + shift j) + (shift i - shift j)
    abel
  have h := norm_sum_sum_sq_le (fun i x => f (x + shift i))
  simpa only [havg, norm_mul, Complex.norm_natCast, mul_pow, hcorr] using h

/-- Each integer difference occurs at most as often as there are shifts.
The set of differences must include zero as well as both signs. -/
theorem sum_pair_sub_le {A : Type*} [AddCommGroup A]
    (s t : Finset A) (M : A → ℝ)
    (ht : ∀ a ∈ s, ∀ b ∈ s, a-b ∈ t)
    (hM : ∀ h ∈ t, 0 ≤ M h) :
    (∑ a ∈ s, ∑ b ∈ s, M (a-b)) ≤ (s.card : ℝ) * ∑ h ∈ t, M h := by
  classical
  have hone (a : A) (ha : a ∈ s) : (∑ b ∈ s, M (a-b)) ≤ ∑ h ∈ t, M h := by
    rw [← Finset.sum_image (g := fun b => a-b) (f := M)
      (fun b _ c _ hbc => sub_right_injective hbc)]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · rintro h hh
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hh
      exact ht a ha b hb
    · exact fun h hh _ => hM h hh
  calc
    _ ≤ ∑ _a ∈ s, ∑ h ∈ t, M h := Finset.sum_le_sum hone
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

/-- The usual loss of one shift-box cardinality in van der Corput's
inequality, with literal finite correlations and an explicit difference set.
The map into the finite group need not be injective. -/
theorem norm_sum_sq_le_of_difference_majorant {A G : Type*}
    [AddCommGroup A] [AddCommGroup G] [Fintype G]
    (f : G → ℂ) (π : A →+ G) (s t : Finset A) (hs : s.Nonempty)
    (M : A → ℝ) (hM : ∀ h ∈ t, 0 ≤ M h)
    (ht : ∀ a ∈ s, ∀ b ∈ s, a-b ∈ t)
    (hcor : ∀ h ∈ t, ‖∑ x, f (x + π h) * starRingEnd ℂ (f x)‖ ≤ M h) :
    (s.card : ℝ) * ‖∑ x, f x‖^2 ≤
      (Fintype.card G : ℝ) * ∑ h ∈ t, M h := by
  classical
  have h := card_sq_mul_norm_sum_sq_le f (fun a : s => π a)
  have hpair : (∑ a : s, ∑ b : s,
      ‖∑ x, f (x + (π a - π b)) * starRingEnd ℂ (f x)‖) ≤
        (s.card : ℝ) * ∑ h ∈ t, M h := by
    calc
      _ ≤ ∑ a : s, ∑ b : s, M (a.val-b.val) := by
        apply Finset.sum_le_sum
        intro a _
        apply Finset.sum_le_sum
        intro b _
        simpa only [map_sub] using hcor (a.val-b.val) (ht a.val a.property b.val b.property)
      _ = ∑ a ∈ s, ∑ b ∈ s, M (a-b) := by
        rw [← Finset.sum_coe_sort s (fun a => ∑ b ∈ s, M (a-b))]
        apply Finset.sum_congr rfl
        intro a _
        exact Finset.sum_coe_sort s (fun b => M (a.val-b))
      _ ≤ _ := sum_pair_sub_le s t M ht hM
  have h' := h.trans (mul_le_mul_of_nonneg_left hpair (Nat.cast_nonneg _))
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  simp only [Fintype.card_coe] at h'
  nlinarith

end CubicTenVariables.FiniteShiftDifferencing
