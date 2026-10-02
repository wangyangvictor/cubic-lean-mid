import TranslatedDepthSeven.PowerSeriesProductSpaceInternal
import TranslatedDepthSeven.PublishedCountingTheorems
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# Linear growth forced by a one-variable formal-series embedding

For a degree filtration admitting an injective algebra map to formal power
series, the product-space inequality forces
`dim F_n ≥ n*(dim F_1 - 1) + 1`.  When the Hilbert polynomial is linear,
its slope is therefore at least `dim F_1 - 1`.
-/

namespace TranslatedDepthSeven

noncomputable section

open Published

set_option maxHeartbeats 2000000

theorem filtered_finrank_linear_lower_of_powerSeries_embedding
    {K A : Type*} [Field K] [CommRing A] [Nontrivial A] [Algebra K A]
    (F : ℕ → Submodule K A) [∀ n, Module.Finite K (F n)]
    (h : A →ₐ[K] PowerSeries K) (hh : Function.Injective h)
    (hone : ∀ n, (1 : A) ∈ F n)
    (hmul : ∀ n, ∀ x ∈ F n, ∀ y ∈ F 1, x * y ∈ F (n + 1)) :
    ∀ n, n * (Module.finrank K (F 1) - 1) + 1 ≤ Module.finrank K (F n) := by
  let G := fun n ↦ (F n).map h.toLinearMap
  have hG (n : ℕ) : Module.finrank K (G n) = Module.finrank K (F n) :=
    ((F n).equivMapOfInjective h.toLinearMap hh).finrank_eq.symm
  have hpos (n : ℕ) : 0 < Module.finrank K (F n) := by
    haveI : Nontrivial (F n) :=
      ⟨⟨⟨1, hone n⟩, 0, fun heq ↦ one_ne_zero (congrArg Subtype.val heq)⟩⟩
    exact Module.finrank_pos
  have hstep (n : ℕ) :
      Module.finrank K (F n) + Module.finrank K (F 1) ≤
        Module.finrank K (F (n + 1)) + 1 := by
    letI (k : ℕ) : Module.Finite K (G k) := Module.Finite.map _ _
    have hg := powerSeries_productSpace_finrank_inequality (G n) (G 1) (G (n + 1))
      (by rw [hG]; exact hpos n) (by rw [hG]; exact hpos 1) (by
        intro x hx y hy
        obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx
        obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hy
        exact Submodule.mem_map.mpr ⟨a * b, hmul n a ha b hb, h.map_mul a b⟩)
    simpa only [hG] using hg
  intro n
  induction n with
  | zero =>
      have hp := hpos 0
      simpa only [Nat.zero_mul, zero_add] using hp
  | succ n ih =>
      have hs := hstep n
      have hp := hpos 1
      rw [Nat.succ_mul]
      omega

theorem affineHilbertFiltration_linear_lower_of_powerSeries_embedding
    {K : Type*} [Field K] {N : ℕ}
    (J : Ideal (MvPolynomial (Fin N) K)) (hJ : J.IsPrime)
    (h : (MvPolynomial (Fin N) K ⧸ J) →ₐ[K] PowerSeries K)
    (hh : Function.Injective h) (n : ℕ) :
    n * (Module.finrank K (affineHilbertFiltration K N J 1) - 1) + 1 ≤
      Module.finrank K (affineHilbertFiltration K N J n) := by
  letI : J.IsPrime := hJ
  apply filtered_finrank_linear_lower_of_powerSeries_embedding
    (affineHilbertFiltration K N J) h hh
  · intro k
    exact Submodule.mem_map.mpr ⟨1, by
      apply (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
      simp, by simp⟩
  · intro k x hx y hy
    obtain ⟨P, hP, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨Q, hQ, rfl⟩ := Submodule.mem_map.mp hy
    refine Submodule.mem_map.mpr ⟨P * Q, ?_, (Ideal.Quotient.mkₐ K J).map_mul P Q⟩
    apply (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
    exact (MvPolynomial.totalDegree_mul P Q).trans
      (Nat.add_le_add ((MvPolynomial.mem_restrictTotalDegree _ _ _).mp hP)
        ((MvPolynomial.mem_restrictTotalDegree _ _ _).mp hQ))

theorem linear_hilbert_slope_ge_filtration_first_rank_sub_one
    (H : ℕ → ℕ) (d : ℕ) (P : Polynomial ℚ)
    (hdeg : P.natDegree = 1) (hlc : P.leadingCoeff = d)
    (hpoly : ∃ n₀, ∀ n ≥ n₀, (H n : ℚ) = P.eval (n : ℚ))
    (hlower : ∀ n, n * (H 1 - 1) + 1 ≤ H n) :
    H 1 ≤ d + 1 := by
  have hP : P = Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C (P.coeff 0) := by
    have h := P.eq_X_add_C_of_natDegree_le_one hdeg.le
    have hc : P.coeff 1 = d := by
      rw [← hdeg, Polynomial.coeff_natDegree, hlc]
    simpa only [hc] using h
  obtain ⟨n₀, hn₀⟩ := hpoly
  by_contra hnot
  have hstep : d + 1 ≤ H 1 - 1 := by omega
  obtain ⟨k, hk⟩ := exists_nat_gt (P.coeff 0)
  let n := max n₀ k
  have hn : n₀ ≤ n := le_max_left _ _
  have hk' : (P.coeff 0 : ℚ) < n := hk.trans_le (by exact_mod_cast le_max_right n₀ k)
  have heval := hn₀ n hn
  rw [hP] at heval
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X] at heval
  have hlow : (n : ℚ) * (H 1 - 1 : ℕ) + 1 ≤ H n := by
    exact_mod_cast hlower n
  have hstep' : (d : ℚ) + 1 ≤ (H 1 - 1 : ℕ) := by exact_mod_cast hstep
  have hnnonneg : (0 : ℚ) ≤ n := by positivity
  nlinarith

end

end TranslatedDepthSeven
