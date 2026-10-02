import TranslatedDepthSeven.LinearPrimitiveElement
import Mathlib.Data.Finset.Prod

/-!
# A bounded natural-number coefficient in the primitive-element theorem

The only excluded coefficients are ratios of differences of roots. There
are at most deg(f)*deg(g) such values, so one of the integers from zero
through that product is allowed. This is uniform in all coefficients of
the two polynomials and in the containing fields.
-/

namespace TranslatedDepthSeven
noncomputable section
open Polynomial IntermediateField
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 300000

universe u v

/-- Avoid the root ratios using a natural number no larger than the
product of the polynomial degrees. -/
theorem exists_bounded_nat_coefficient_avoiding_root_ratios
    (K : Type u) {E : Type v} [Field K] [CharZero K] [Field E]
    (ι : K →+* E) (alpha beta : E) (f g : K[X]) :
    ∃ c : ℕ, c ≤ f.natDegree * g.natDegree ∧
      ∀ alpha' ∈ (f.map ι).roots, ∀ beta' ∈ (g.map ι).roots,
        -(alpha' - alpha) / (beta' - beta) ≠ ι (c : K) := by
  classical
  let sf := (f.map ι).roots.toFinset
  let sg := (g.map ι).roots.toFinset
  let bad := (sf ×ˢ sg).image (fun p ↦ -(p.1 - alpha) / (p.2 - beta))
  have hfcard : sf.card ≤ f.natDegree :=
    (Multiset.toFinset_card_le _).trans (Polynomial.card_roots_map_le_natDegree f)
  have hgcard : sg.card ≤ g.natDegree :=
    (Multiset.toFinset_card_le _).trans (Polynomial.card_roots_map_le_natDegree g)
  have hbad : bad.card ≤ f.natDegree * g.natDegree := by
    exact Finset.card_image_le.trans
      ((Finset.card_product sf sg).le.trans (Nat.mul_le_mul hfcard hgcard))
  let D := f.natDegree * g.natDegree
  let grid := (Finset.range (D + 1)).image (fun c : ℕ ↦ ι (c : K))
  have hcast : Function.Injective (fun c : ℕ ↦ ι (c : K)) :=
    ι.injective.comp Nat.cast_injective
  have hgrid : grid.card = D + 1 := by
    dsimp only [grid]
    rw [Finset.card_image_of_injective _ hcast, Finset.card_range]
  obtain ⟨x, hx, hxnot⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (hbad.trans_lt (by rw [hgrid]; exact Nat.lt_succ_self D))
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
  refine ⟨c, Nat.le_of_lt_succ (Finset.mem_range.mp hc), ?_⟩
  intro alpha' halpha beta' hbeta heq
  apply hxnot
  rw [← heq]
  apply Finset.mem_image.mpr
  exact ⟨(alpha', beta'), Finset.mem_product.mpr
    ⟨Multiset.mem_toFinset.mpr halpha, Multiset.mem_toFinset.mpr hbeta⟩, rfl⟩

/-- A separable pair has a primitive linear combination with a bounded
natural coefficient. The bound uses only the two minimal-polynomial degrees. -/
theorem exists_bounded_nat_linear_primitive_element_pair
    (K : Type u) {E : Type v}
    [Field K] [CharZero K] [Field E] [Algebra K E]
    [Algebra.IsSeparable K E] (alpha beta : E) :
    ∃ c : ℕ, c ≤ (minpoly K alpha).natDegree * (minpoly K beta).natDegree ∧
      K⟮alpha, beta⟯ = K⟮alpha + (c : K) • beta⟯ := by
  classical
  have halpha := Algebra.IsSeparable.isIntegral K alpha
  have hbeta := Algebra.IsSeparable.isIntegral K beta
  let f := minpoly K alpha
  let g := minpoly K beta
  let iFE := algebraMap K E
  let iEE' := algebraMap E (SplittingField (g.map iFE))
  obtain ⟨c, hcBound, hc⟩ :=
    exists_bounded_nat_coefficient_avoiding_root_ratios K
      (iEE'.comp iFE) (iEE' alpha) (iEE' beta) f g
  refine ⟨c, hcBound, ?_⟩
  let gamma := alpha + (c : K) • beta
  suffices beta_in : beta ∈ K⟮gamma⟯ by
    apply le_antisymm
    · rw [adjoin_le_iff]
      have alpha_in : alpha ∈ K⟮gamma⟯ := by
        rw [← add_sub_cancel_right alpha ((c : K) • beta)]
        exact K⟮gamma⟯.sub_mem (mem_adjoin_simple_self K gamma)
          (K⟮gamma⟯.toSubalgebra.smul_mem beta_in (c : K))
      rintro x (rfl | rfl) <;> assumption
    · rw [adjoin_simple_le_iff]
      have alpha_in : alpha ∈ K⟮alpha, beta⟯ :=
        subset_adjoin K {alpha, beta} (Set.mem_insert alpha {beta})
      have beta_in' : beta ∈ K⟮alpha, beta⟯ :=
        subset_adjoin K {alpha, beta} (Set.mem_insert_of_mem alpha rfl)
      exact K⟮alpha, beta⟯.add_mem alpha_in
        (K⟮alpha, beta⟯.smul_mem beta_in')
  let p := EuclideanDomain.gcd
    ((f.map (algebraMap K K⟮gamma⟯)).comp
      (C (AdjoinSimple.gen K gamma) -
        (C ↑(c : K) : K⟮gamma⟯[X]) * X))
    (g.map (algebraMap K K⟮gamma⟯))
  let h := EuclideanDomain.gcd
    ((f.map iFE).comp (C gamma - C (iFE (c : K)) * X)) (g.map iFE)
  have map_g_ne_zero : g.map iFE ≠ 0 :=
    map_ne_zero (minpoly.ne_zero hbeta)
  have h_ne_zero : h ≠ 0 :=
    mt EuclideanDomain.gcd_eq_zero_iff.mp
      (not_and.mpr fun _ ↦ map_g_ne_zero)
  suffices p_linear :
      p.map (algebraMap K⟮gamma⟯ E) =
        C h.leadingCoeff * (X - C beta) by
    have finale :
        beta = algebraMap K⟮gamma⟯ E (-p.coeff 0 / p.coeff 1) := by
      simp [map_div₀, map_neg, ← coeff_map, ← coeff_map, p_linear,
        mul_sub, coeff_C, mul_div_cancel_left₀ beta
          (mt leadingCoeff_eq_zero.mp h_ne_zero)]
    rw [finale]
    exact Subtype.mem (-p.coeff 0 / p.coeff 1)
  have h_sep : h.Separable :=
    separable_gcd_right _
      (.map (Algebra.IsSeparable.isSeparable K beta))
  have h_root : h.eval beta = 0 := by
    apply eval_gcd_eq_zero
    · rw [eval_comp, eval_sub, eval_mul, eval_C, eval_C, eval_X,
        eval_map_algebraMap, ← Algebra.smul_def, add_sub_cancel_right,
        minpoly.aeval]
    · rw [eval_map_algebraMap, minpoly.aeval]
  have h_splits : Splits (h.map iEE') := by
    rw [← Polynomial.gcd_map]
    exact (SplittingField.splits _).splits_of_dvd
      (map_ne_zero map_g_ne_zero) (EuclideanDomain.gcd_dvd_right _ _)
  have h_roots : ∀ x ∈ (h.map iEE').roots, x = iEE' beta := by
    intro x hx
    rw [mem_roots_map h_ne_zero] at hx
    specialize hc (iEE' gamma - iEE' (iFE (c : K)) * x) (by
      have f_root := root_left_of_root_gcd hx
      rw [eval₂_comp, eval₂_sub, eval₂_mul, eval₂_C, eval₂_C,
        eval₂_X, eval₂_map] at f_root
      exact (mem_roots_map (minpoly.ne_zero halpha)).mpr f_root)
    specialize hc x (by
      rw [mem_roots_map (minpoly.ne_zero hbeta), ← eval₂_map]
      exact root_right_of_root_gcd hx)
    by_contra hne
    apply hc
    apply (div_eq_iff (sub_ne_zero.mpr hne)).mpr
    simp only [gamma, Algebra.smul_def, map_add, map_mul,
      RingHom.comp_apply]
    ring
  rw [← eq_X_sub_C_of_separable_of_root_eq h_sep h_root h_splits h_roots]
  trans EuclideanDomain.gcd (?_ : E[X]) (?_ : E[X])
  · dsimp only [gamma]
    convert (gcd_map (algebraMap K⟮gamma⟯ E)).symm
  · simp only [map_comp, Polynomial.map_map, ← IsScalarTower.algebraMap_eq,
      Polynomial.map_sub, map_C, AdjoinSimple.algebraMap_gen,
      Polynomial.map_mul, map_X]
    congr

end
end TranslatedDepthSeven
