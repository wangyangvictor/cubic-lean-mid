import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.CharP.Basic
import Mathlib.Tactic

/-! Literal polynomial zero counts over arbitrary finite fields, not just
prime fields. A fixed nonzero integer coefficient excludes finitely many
characteristics before any extension field is chosen. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.FiniteFieldPolynomialZeros
open MvPolynomial
open scoped BigOperators Classical

variable {K σ : Type*} [Field K] [Fintype K] [Fintype σ]

def zeros (f : MvPolynomial σ K) : Finset (σ → K) :=
  Finset.univ.filter fun x => eval x f = 0

@[simp] theorem mem_zeros (f : MvPolynomial σ K) (x : σ → K) :
    x ∈ zeros f ↔ eval x f = 0 := by simp [zeros]

theorem natCard_zeros (f : MvPolynomial σ K) :
    Nat.card {x : σ → K // eval x f = 0} = (zeros f).card := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, zeros]

theorem card_zeros_fin_le {n : ℕ} (f : MvPolynomial (Fin n) K) (hf : f ≠ 0) :
    (zeros f).card ≤ f.totalDegree * Fintype.card K ^ (n-1) := by
  have hratio : ((zeros f).card : ℚ≥0) / (Fintype.card K : ℚ≥0)^n ≤
      (f.totalDegree : ℚ≥0) / Fintype.card K := by
    have h := schwartz_zippel_totalDegree hf (Finset.univ : Finset K)
    have hpi : ((Fintype.piFinset fun _ : Fin n => (Finset.univ : Finset K)).filter
        fun x => eval x f = 0) = zeros f := by ext x; simp [zeros]
    rw [hpi] at h
    simpa only [Finset.card_univ] using h
  cases n with
  | zero =>
    have hd : f.totalDegree = 0 := by
      rw [f.eq_C_of_isEmpty, totalDegree_C]
    simpa only [hd, Nat.cast_zero, zero_div, pow_zero, div_one,
      nonpos_iff_eq_zero, Nat.cast_eq_zero, Nat.zero_sub, zero_mul] using hratio
  | succ n =>
    have hq : (Fintype.card K : ℚ≥0) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have hqn : (Fintype.card K : ℚ≥0)^(n+1) ≠ 0 := pow_ne_zero _ hq
    have hbound : ((zeros f).card : ℚ≥0) ≤
        (f.totalDegree : ℚ≥0) * (Fintype.card K : ℚ≥0)^n := by
      calc
        _ = (((zeros f).card : ℚ≥0) / (Fintype.card K : ℚ≥0)^(n+1)) *
            (Fintype.card K : ℚ≥0)^(n+1) := (div_mul_cancel₀ _ hqn).symm
        _ ≤ ((f.totalDegree : ℚ≥0) / Fintype.card K) *
            (Fintype.card K : ℚ≥0)^(n+1) := mul_le_mul_left hratio _
        _ = _ := by rw [pow_succ]; field_simp
    simpa only [Nat.succ_sub_one] using (show (zeros f).card ≤
      f.totalDegree * Fintype.card K^n by exact_mod_cast hbound)

/-- Schwartz--Zippel for any finite coordinate index, including an actual
complement of selected coordinates. -/
theorem card_zeros_le_totalDegree_mul (f : MvPolynomial σ K) (hf : f ≠ 0) :
    (zeros f).card ≤ f.totalDegree * Fintype.card K ^ (Fintype.card σ-1) := by
  let e := Fintype.equivFin σ
  let g := rename e f
  have hg : g ≠ 0 := fun hz => hf ((rename_injective e e.injective)
    (by simpa only [map_zero] using hz))
  have hcount : (zeros f).card = (zeros g).card := by
    let E : (σ → K) ≃ (Fin (Fintype.card σ) → K) := e.arrowCongr (Equiv.refl K)
    have hE : ∀ x, eval x f = 0 ↔ eval (E x) g = 0 := by
      intro x
      simp only [g, eval_rename]
      have he : E x ∘ e = x := by funext i; simp [E]
      rw [he]
    apply Finset.card_bij (fun x _ => E x)
    · intro x hx
      exact (mem_zeros g _).mpr ((hE x).mp ((mem_zeros f x).mp hx))
    · intro x _ y _ hxy
      exact E.injective hxy
    · intro y hy
      refine ⟨E.symm y, ?_, E.apply_symm_apply y⟩
      apply (mem_zeros f _).mpr
      apply (hE (E.symm y)).mpr
      simpa only [E.apply_symm_apply] using (mem_zeros g y).mp hy
  rw [hcount]
  exact (card_zeros_fin_le g hg).trans
    (Nat.mul_le_mul_right _ (totalDegree_rename_le e f))

theorem card_zeros_le_degree_mul (f : MvPolynomial σ K) (hf : f ≠ 0)
    (d : ℕ) (hd : f.totalDegree ≤ d) :
    (zeros f).card ≤ d * Fintype.card K ^ (Fintype.card σ-1) :=
  (card_zeros_le_totalDegree_mul f hf).trans (Nat.mul_le_mul_right _ hd)

omit [Fintype K] [Fintype σ] in
/-- One nonzero integer coefficient is a nonvanishing certificate over
every field of characteristic not dividing its absolute value. -/
theorem reduction_ne_zero_of_coefficient (f : MvPolynomial σ ℤ)
    (m : σ →₀ ℕ) (p : ℕ) [CharP K p]
    (hp : ¬ p ∣ (coeff m f).natAbs) :
    map (Int.castRingHom K) f ≠ 0 := by
  intro hz
  have hc : ((coeff m f : ℤ) : K) = 0 := by
    simpa only [coeff_map, coeff_zero] using congrArg (coeff m) hz
  have hdiv := (CharP.intCast_eq_zero_iff K p (coeff m f)).mp hc
  exact hp (by simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hdiv)

theorem exists_uniform_nonzero_reduction (f : MvPolynomial σ ℤ) (hf : f ≠ 0) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ p : ℕ, ¬ p ∣ N →
      ∀ (k : Type*) [Field k] [CharP k p], map (Int.castRingHom k) f ≠ 0 := by
  obtain ⟨m,hm⟩ := exists_coeff_ne_zero hf
  exact ⟨(coeff m f).natAbs, Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hm),
    fun p hp k _ _ => reduction_ne_zero_of_coefficient f m p hp⟩

/-- The exceptional integer and degree constant precede the characteristic
and every finite extension. No point-count literature is needed. -/
theorem exists_uniform_extension_zero_bound (f : MvPolynomial σ ℤ) (hf : f ≠ 0) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ p : ℕ, ¬ p ∣ N →
      ∀ (k : Type*) [Field k] [Fintype k] [CharP k p],
        (zeros (map (Int.castRingHom k) f)).card ≤
          f.totalDegree * Fintype.card k ^ (Fintype.card σ-1) := by
  obtain ⟨m,hm⟩ := exists_coeff_ne_zero hf
  refine ⟨(coeff m f).natAbs, Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hm), ?_⟩
  intro p hp k _ _ _
  exact card_zeros_le_degree_mul _ (reduction_ne_zero_of_coefficient f m p hp) _
    (Finset.sup_mono (support_map_subset _ _))

end CubicTenVariables.FiniteFieldPolynomialZeros
