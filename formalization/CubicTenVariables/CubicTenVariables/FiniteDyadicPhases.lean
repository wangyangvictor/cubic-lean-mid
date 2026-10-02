import CubicTenVariables.DyadicFrequencyError
import CubicTenVariables.DeltaMethod
import Mathlib.Data.Nat.Log

/-! Finite disjoint phase shells, with an exact integral partition of any
clipped domain. The small central interval is retained, not discarded. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.FiniteDyadicPhases
open MeasureTheory DyadicFrequencyError DeltaMethod
open scoped BigOperators

/-- Increasing dyadic shell widths, starting at the tiny cutoff. -/
def radius (τ : ℝ) (k : ℕ) : ℝ := τ*2^k

theorem radius_pos (τ : ℝ) (hτ : 0 < τ) (k : ℕ) : 0 < radius τ k := by
  unfold radius
  positivity

@[simp] theorem radius_zero (τ : ℝ) : radius τ 0=τ := by simp [radius]

@[simp] theorem radius_succ (τ : ℝ) (k : ℕ) : radius τ (k+1)=2*radius τ k := by
  simp only [radius,pow_succ]
  ring

theorem radius_mono (τ : ℝ) (hτ : 0 ≤ τ) : Monotone (radius τ) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hij) hτ

theorem exists_shell (τ : ℝ) (_hτ : 0 < τ) (K : ℕ) {θ : ℝ}
    (hlo : τ < |θ|) (hhi : |θ| ≤ radius τ K) :
    ∃ k ∈ Finset.range K, θ ∈ shell (radius τ k) := by
  induction K with
  | zero => simpa using (not_lt_of_ge (by simpa using hhi)) hlo
  | succ K ih =>
      by_cases hsmall : |θ| ≤ radius τ K
      · obtain ⟨k,hk,hθ⟩ := ih hsmall
        exact ⟨k,Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hk)),hθ⟩
      · exact ⟨K,Finset.mem_range.mpr (Nat.lt_succ_self K),
          (not_le.mp hsmall),by simpa only [radius_succ] using hhi⟩

/-- The strict lower and weak upper shell endpoints give actual disjointness. -/
theorem shells_disjoint (τ : ℝ) (hτ : 0 < τ) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (shell (radius τ i)) (shell (radius τ j)) := by
  apply Set.disjoint_left.mpr
  intro θ hi hj
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hstep := radius_mono τ hτ.le (Nat.succ_le_of_lt hij)
    rw [radius_succ] at hstep
    exact (not_lt_of_ge (hi.2.trans hstep)) hj.1
  · have hstep := radius_mono τ hτ.le (Nat.succ_le_of_lt hji)
    rw [radius_succ] at hstep
    exact (not_lt_of_ge (hj.2.trans hstep)) hi.1

/-- Literal finite partition of an arbitrary clipped phase domain. -/
theorem set_partition (τ : ℝ) (hτ : 0 < τ) (K : ℕ) (S : Set ℝ)
    (hS : S ⊆ Set.Icc (-(radius τ K)) (radius τ K)) :
    S = (S ∩ Set.Icc (-τ) τ) ∪
      ⋃ k ∈ Finset.range K, shell (radius τ k) ∩ S := by
  ext θ
  constructor
  · intro hθ
    by_cases ht : |θ| ≤ τ
    · exact Or.inl ⟨hθ,abs_le.mp ht⟩
    · obtain ⟨k,hk,hkθ⟩ := exists_shell τ hτ K (not_le.mp ht) (abs_le.mpr (hS hθ))
      exact Or.inr (Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨hk,hkθ,hθ⟩⟩)
  · intro hθ
    rcases hθ with ht | hθ
    · exact ht.1
    · obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hθ
      obtain ⟨_,hkθ⟩ := Set.mem_iUnion.mp hk
      exact hkθ.2

/-- Exact finite sum of integrals. Integrability is inherited from the
original domain; no infinite sum/integral interchange occurs. -/
theorem integral_partition (τ : ℝ) (hτ : 0 < τ) (K : ℕ) (S : Set ℝ)
    (hSm : MeasurableSet S) (hS : S ⊆ Set.Icc (-(radius τ K)) (radius τ K))
    (f : ℝ → ℂ) (hf : IntegrableOn f S) :
    (∫ θ in S, f θ) = (∫ θ in S ∩ Set.Icc (-τ) τ, f θ) +
      ∑ k ∈ Finset.range K, ∫ θ in shell (radius τ k) ∩ S, f θ := by
  have hm (k : ℕ) : MeasurableSet (shell (radius τ k) ∩ S) :=
    (measurableSet_shell _).inter hSm
  have hu : (⋃ k ∈ Finset.range K, shell (radius τ k) ∩ S) ⊆ S := by
    intro θ hθ
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hθ
    obtain ⟨_,hk⟩ := Set.mem_iUnion.mp hk
    exact hk.2
  have hd : Disjoint (S ∩ Set.Icc (-τ) τ)
      (⋃ k ∈ Finset.range K, shell (radius τ k) ∩ S) := by
    apply Set.disjoint_left.mpr
    intro θ ht hθ
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hθ
    obtain ⟨_,hk⟩ := Set.mem_iUnion.mp hk
    have ht' := abs_le.mpr ht.2
    have hb : τ ≤ radius τ k := by
      simpa only [radius_zero] using radius_mono τ hτ.le (Nat.zero_le k)
    exact (not_lt_of_ge (ht'.trans hb)) hk.1.1
  calc
    _ = ∫ θ in (S ∩ Set.Icc (-τ) τ) ∪
        ⋃ k ∈ Finset.range K, shell (radius τ k) ∩ S, f θ := by
          exact congrArg (fun T : Set ℝ => ∫ θ in T, f θ) (set_partition τ hτ K S hS)
    _ = (∫ θ in S ∩ Set.Icc (-τ) τ, f θ) +
        ∫ θ in ⋃ k ∈ Finset.range K, shell (radius τ k) ∩ S, f θ :=
      setIntegral_union hd (Finset.measurableSet_biUnion _ (fun k _ => hm k))
        (hf.mono_set Set.inter_subset_left) (hf.mono_set hu)
    _ = _ := by
      congr 1
      apply integral_biUnion_finset
      · exact fun k _ => hm k
      · intro i _ j _ hij
        exact (shells_disjoint τ hτ hij).mono Set.inter_subset_left Set.inter_subset_left
      · exact fun _ _ => hf.mono_set Set.inter_subset_right

/-- A unit-bounded clipped domain, with the tiny interval placed first in
its intersection, as in the global count assembly. -/
theorem integral_partition_unit (τ : ℝ) (hτ : 0 < τ) (K : ℕ)
    (hK : 1 ≤ τ*2^K) (S : Set ℝ) (hSm : MeasurableSet S)
    (hS : S ⊆ Set.Icc (-1) 1) (f : ℝ → ℂ) (hf : IntegrableOn f S) :
    (∫ θ in S, f θ) = (∫ θ in Set.Icc (-τ) τ ∩ S, f θ) +
      ∑ k ∈ Finset.range K, ∫ θ in shell (τ*2^k) ∩ S, f θ := by
  have hb : S ⊆ Set.Icc (-(radius τ K)) (radius τ K) := by
    intro θ hθ
    exact ⟨(neg_le_neg hK).trans (hS hθ).1,(hS hθ).2.trans hK⟩
  simpa only [radius,Set.inter_comm S (Set.Icc (-τ) τ)] using
    integral_partition τ hτ K S hSm hb f hf

/-- The logarithmic number of phase blocks used for natural physical scales. -/
def count (P : ℕ) : ℕ := Nat.log 2 (P^20)+1

/-- These finitely many shells reach at least unit phase. -/
theorem one_le_last_radius (P : ℕ) (hP : 0 < P) :
    1 ≤ radius ((P:ℝ)^(-20:ℝ)) (count P) := by
  have hP' : 0 < (P:ℝ) := by exact_mod_cast hP
  have hpow : (P:ℝ)^20 ≤ (2:ℝ)^(count P) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1<2) (P^20)).le
  have he : (P:ℝ)^(-20:ℝ)*(P:ℝ)^20=1 := by
    rw [← Real.rpow_natCast (P:ℝ) 20,← Real.rpow_add hP']
    norm_num
  calc
    1 = (P:ℝ)^(-20:ℝ)*(P:ℝ)^20 := he.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hP'.le _)

/-- Every original delta arc lies in the unit interval for η≤1. -/
theorem arc_subset_unit (Q q : ℕ) (hQ : 1 ≤ Q) (hq : 1 ≤ q)
    (η : ℝ) (hη : η ≤ 1) : arc Q q η ⊆ Set.Icc (-1) 1 := by
  intro θ hθ
  have hprod : (1:ℝ) ≤ (q:ℝ)*(Q:ℝ) :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast hq) (by exact_mod_cast hQ)
  have hb : ((q:ℝ)*(Q:ℝ))^(-1+η) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_nonpos zero_lt_one hprod (by linarith : -1+η ≤ 0)
  exact abs_le.mp ((show |θ| < _ from hθ).le.trans hb)

/-- The finite phase partition applies directly to every source delta arc. -/
theorem arc_integral_partition (P Q q : ℕ) (hP : 0 < P) (hQ : 1 ≤ Q) (hq : 1 ≤ q)
    (η : ℝ) (hη : η ≤ 1) (f : ℝ → ℂ) (hf : IntegrableOn f (arc Q q η)) :
    (∫ θ in arc Q q η, f θ) =
      (∫ θ in arc Q q η ∩ Set.Icc (-((P:ℝ)^(-20:ℝ))) ((P:ℝ)^(-20:ℝ)), f θ) +
      ∑ k ∈ Finset.range (count P),
        ∫ θ in shell (radius ((P:ℝ)^(-20:ℝ)) k) ∩ arc Q q η, f θ := by
  apply integral_partition _ (Real.rpow_pos_of_pos (by exact_mod_cast hP) _) _ _
  · rw [arc_eq_Ioo]
    exact measurableSet_Ioo
  · have hlast := one_le_last_radius P hP
    exact (arc_subset_unit Q q hQ hq η hη).trans (by
      intro θ hθ
      exact ⟨(neg_le_neg hlast).trans hθ.1,hθ.2.trans hlast⟩)
  · exact hf

end CubicTenVariables.FiniteDyadicPhases
