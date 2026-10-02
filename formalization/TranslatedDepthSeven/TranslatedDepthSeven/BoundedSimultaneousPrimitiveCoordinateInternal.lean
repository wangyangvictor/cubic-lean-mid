import TranslatedDepthSeven.BoundedLinearPrimitiveElementInternal
import Mathlib.Data.Fin.Tuple.Basic

/-!
# One bounded primitive coordinate for two extensions

The source projection and its hyperplane-at-infinity restriction must use
the same final linear form.  The usual bounded primitive-element argument
excludes at most a product of two minimal-polynomial degrees.  For two
extensions, the union of the two exceptional sets therefore excludes at
most the sum of those products.  A single natural coefficient outside that
union works for both extensions.

Iterating the two-generator argument gives one integral linear combination
of two displayed coordinate families.  If both extension degrees are at
most `D`, every coefficient is bounded by `(2 * D * D + 1)^n`.  This bound
depends only on the two degree bounds and the family length.
-/

namespace TranslatedDepthSeven
noncomputable section

open Polynomial IntermediateField

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 500000

universe u₁ v₁ u₂ v₂

/-- A fixed natural coefficient gives a primitive linear combination once
it avoids all ratios of conjugate differences. -/
theorem linear_primitive_element_pair_of_bounded_root_ratio_avoidance
    (K : Type u₁) {E : Type v₁}
    [Field K] [CharZero K] [Field E] [Algebra K E]
    [Algebra.IsSeparable K E] (alpha beta : E) (c : ℕ)
    (hc :
      let f := minpoly K alpha
      let g := minpoly K beta
      let iKE := algebraMap K E
      let iEE' := algebraMap E (SplittingField (g.map iKE))
      ∀ alpha' ∈ (f.map (iEE'.comp iKE)).roots,
        ∀ beta' ∈ (g.map (iEE'.comp iKE)).roots,
          -(alpha' - iEE' alpha) / (beta' - iEE' beta) ≠
            (iEE'.comp iKE) (c : K)) :
    K⟮alpha, beta⟯ = K⟮alpha + (c : K) • beta⟯ := by
  classical
  have halpha := Algebra.IsSeparable.isIntegral K alpha
  have hbeta := Algebra.IsSeparable.isIntegral K beta
  let f := minpoly K alpha
  let g := minpoly K beta
  let iKE := algebraMap K E
  let iEE' := algebraMap E (SplittingField (g.map iKE))
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
    ((f.map iKE).comp (C gamma - C (iKE (c : K)) * X)) (g.map iKE)
  have map_g_ne_zero : g.map iKE ≠ 0 :=
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
    specialize hc (iEE' gamma - iEE' (iKE (c : K)) * x) (by
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

/-- Avoid the two finite root-ratio sets with one natural number. -/
theorem exists_bounded_nat_coefficient_avoiding_two_root_ratio_families
    (K₁ : Type u₁) {E₁ : Type v₁} [Field K₁] [CharZero K₁] [Field E₁]
    (ι₁ : K₁ →+* E₁) (alpha₁ beta₁ : E₁) (f₁ g₁ : K₁[X])
    (K₂ : Type u₂) {E₂ : Type v₂} [Field K₂] [CharZero K₂] [Field E₂]
    (ι₂ : K₂ →+* E₂) (alpha₂ beta₂ : E₂) (f₂ g₂ : K₂[X]) :
    ∃ c : ℕ,
      c ≤ f₁.natDegree * g₁.natDegree + f₂.natDegree * g₂.natDegree ∧
      (∀ alpha' ∈ (f₁.map ι₁).roots, ∀ beta' ∈ (g₁.map ι₁).roots,
        -(alpha' - alpha₁) / (beta' - beta₁) ≠ ι₁ (c : K₁)) ∧
      (∀ alpha' ∈ (f₂.map ι₂).roots, ∀ beta' ∈ (g₂.map ι₂).roots,
        -(alpha' - alpha₂) / (beta' - beta₂) ≠ ι₂ (c : K₂)) := by
  classical
  let sf₁ := (f₁.map ι₁).roots.toFinset
  let sg₁ := (g₁.map ι₁).roots.toFinset
  let bad₁ := (sf₁ ×ˢ sg₁).image
    (fun p ↦ -(p.1 - alpha₁) / (p.2 - beta₁))
  let sf₂ := (f₂.map ι₂).roots.toFinset
  let sg₂ := (g₂.map ι₂).roots.toFinset
  let bad₂ := (sf₂ ×ˢ sg₂).image
    (fun p ↦ -(p.1 - alpha₂) / (p.2 - beta₂))
  have hcast₁ : Function.Injective (fun c : ℕ ↦ ι₁ (c : K₁)) :=
    ι₁.injective.comp Nat.cast_injective
  have hcast₂ : Function.Injective (fun c : ℕ ↦ ι₂ (c : K₂)) :=
    ι₂.injective.comp Nat.cast_injective
  let badNat₁ : Finset ℕ := bad₁.preimage (fun c : ℕ ↦ ι₁ (c : K₁))
    hcast₁.injOn
  let badNat₂ : Finset ℕ := bad₂.preimage (fun c : ℕ ↦ ι₂ (c : K₂))
    hcast₂.injOn
  have hsf₁ : sf₁.card ≤ f₁.natDegree :=
    (Multiset.toFinset_card_le _).trans
      (Polynomial.card_roots_map_le_natDegree f₁)
  have hsg₁ : sg₁.card ≤ g₁.natDegree :=
    (Multiset.toFinset_card_le _).trans
      (Polynomial.card_roots_map_le_natDegree g₁)
  have hsf₂ : sf₂.card ≤ f₂.natDegree :=
    (Multiset.toFinset_card_le _).trans
      (Polynomial.card_roots_map_le_natDegree f₂)
  have hsg₂ : sg₂.card ≤ g₂.natDegree :=
    (Multiset.toFinset_card_le _).trans
      (Polynomial.card_roots_map_le_natDegree g₂)
  have hbad₁ : bad₁.card ≤ f₁.natDegree * g₁.natDegree :=
    Finset.card_image_le.trans
      ((Finset.card_product sf₁ sg₁).le.trans (Nat.mul_le_mul hsf₁ hsg₁))
  have hbad₂ : bad₂.card ≤ f₂.natDegree * g₂.natDegree :=
    Finset.card_image_le.trans
      ((Finset.card_product sf₂ sg₂).le.trans (Nat.mul_le_mul hsf₂ hsg₂))
  have hbadNat₁ : badNat₁.card ≤ f₁.natDegree * g₁.natDegree := by
    calc
      badNat₁.card ≤ bad₁.card := by
        rw [show badNat₁ = bad₁.preimage (fun c : ℕ ↦ ι₁ (c : K₁))
          hcast₁.injOn from rfl, Finset.card_preimage]
        exact Finset.card_filter_le _ _
      _ ≤ _ := hbad₁
  have hbadNat₂ : badNat₂.card ≤ f₂.natDegree * g₂.natDegree := by
    calc
      badNat₂.card ≤ bad₂.card := by
        rw [show badNat₂ = bad₂.preimage (fun c : ℕ ↦ ι₂ (c : K₂))
          hcast₂.injOn from rfl, Finset.card_preimage]
        exact Finset.card_filter_le _ _
      _ ≤ _ := hbad₂
  let D := f₁.natDegree * g₁.natDegree + f₂.natDegree * g₂.natDegree
  let forbidden := badNat₁ ∪ badNat₂
  have hforbidden : forbidden.card ≤ D := by
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add hbadNat₁ hbadNat₂)
  obtain ⟨c, hcgrid, hcgood⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (hforbidden.trans_lt (by rw [Finset.card_range]; exact Nat.lt_succ_self D))
  have hcbound : c ≤ D := Nat.le_of_lt_succ (Finset.mem_range.mp hcgrid)
  refine ⟨c, hcbound, ?_, ?_⟩
  · intro alpha' halpha beta' hbeta heq
    apply hcgood
    apply Finset.mem_union_left
    apply Finset.mem_preimage.mpr
    rw [← heq]
    apply Finset.mem_image.mpr
    exact ⟨(alpha', beta'), Finset.mem_product.mpr
      ⟨Multiset.mem_toFinset.mpr halpha, Multiset.mem_toFinset.mpr hbeta⟩, rfl⟩
  · intro alpha' halpha beta' hbeta heq
    apply hcgood
    apply Finset.mem_union_right
    apply Finset.mem_preimage.mpr
    rw [← heq]
    apply Finset.mem_image.mpr
    exact ⟨(alpha', beta'), Finset.mem_product.mpr
      ⟨Multiset.mem_toFinset.mpr halpha, Multiset.mem_toFinset.mpr hbeta⟩, rfl⟩

/-- One bounded natural coefficient is primitive for two separable pairs. -/
theorem exists_bounded_nat_simultaneous_linear_primitive_element_pair
    (K₁ : Type u₁) {E₁ : Type v₁}
    [Field K₁] [CharZero K₁] [Field E₁] [Algebra K₁ E₁]
    [Algebra.IsSeparable K₁ E₁] (alpha₁ beta₁ : E₁)
    (K₂ : Type u₂) {E₂ : Type v₂}
    [Field K₂] [CharZero K₂] [Field E₂] [Algebra K₂ E₂]
    [Algebra.IsSeparable K₂ E₂] (alpha₂ beta₂ : E₂) :
    ∃ c : ℕ,
      c ≤ (minpoly K₁ alpha₁).natDegree * (minpoly K₁ beta₁).natDegree +
        (minpoly K₂ alpha₂).natDegree * (minpoly K₂ beta₂).natDegree ∧
      K₁⟮alpha₁, beta₁⟯ = K₁⟮alpha₁ + (c : K₁) • beta₁⟯ ∧
      K₂⟮alpha₂, beta₂⟯ = K₂⟮alpha₂ + (c : K₂) • beta₂⟯ := by
  classical
  let f₁ := minpoly K₁ alpha₁
  let g₁ := minpoly K₁ beta₁
  let i₁ := algebraMap K₁ E₁
  let j₁ := algebraMap E₁ (SplittingField (g₁.map i₁))
  let f₂ := minpoly K₂ alpha₂
  let g₂ := minpoly K₂ beta₂
  let i₂ := algebraMap K₂ E₂
  let j₂ := algebraMap E₂ (SplittingField (g₂.map i₂))
  obtain ⟨c, hc, hc₁, hc₂⟩ :=
    exists_bounded_nat_coefficient_avoiding_two_root_ratio_families
      K₁ (j₁.comp i₁) (j₁ alpha₁) (j₁ beta₁) f₁ g₁
      K₂ (j₂.comp i₂) (j₂ alpha₂) (j₂ beta₂) f₂ g₂
  refine ⟨c, hc, ?_, ?_⟩
  · exact linear_primitive_element_pair_of_bounded_root_ratio_avoidance
      K₁ alpha₁ beta₁ c hc₁
  · exact linear_primitive_element_pair_of_bounded_root_ratio_avoidance
      K₂ alpha₂ beta₂ c hc₂

/-- Every two displayed coordinate families admit one bounded integral
linear combination which generates both of their respective adjoins. -/
theorem exists_bounded_nat_simultaneous_linearCombination_primitive_element
    (K₁ : Type u₁) {E₁ : Type v₁}
    [Field K₁] [CharZero K₁] [Field E₁] [Algebra K₁ E₁]
    [Algebra.IsSeparable K₁ E₁] [FiniteDimensional K₁ E₁]
    (K₂ : Type u₂) {E₂ : Type v₂}
    [Field K₂] [CharZero K₂] [Field E₂] [Algebra K₂ E₂]
    [Algebra.IsSeparable K₂ E₂] [FiniteDimensional K₂ E₂]
    (D : ℕ) (hD₁ : Module.finrank K₁ E₁ ≤ D)
    (hD₂ : Module.finrank K₂ E₂ ≤ D)
    (n : ℕ) (x₁ : Fin n → E₁) (x₂ : Fin n → E₂) :
    ∃ c : Fin n → ℕ, (∀ i, c i ≤ (2 * D * D + 1) ^ n) ∧
      K₁⟮∑ i, (c i : K₁) • x₁ i⟯ =
        IntermediateField.adjoin K₁ (Set.range x₁) ∧
      K₂⟮∑ i, (c i : K₂) • x₂ i⟯ =
        IntermediateField.adjoin K₂ (Set.range x₂) := by
  classical
  induction n with
  | zero =>
      refine ⟨fun i ↦ Fin.elim0 i, ?_, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · simp
      · simp
  | succ n ih =>
      obtain ⟨c, hc, hprimitive₁, hprimitive₂⟩ :=
        ih (Fin.tail x₁) (Fin.tail x₂)
      let beta₁ := ∑ i, (c i : K₁) • x₁ i.succ
      let beta₂ := ∑ i, (c i : K₂) • x₂ i.succ
      have hbeta₁ : K₁⟮beta₁⟯ =
          IntermediateField.adjoin K₁ (Set.range (Fin.tail x₁)) :=
        hprimitive₁
      have hbeta₂ : K₂⟮beta₂⟯ =
          IntermediateField.adjoin K₂ (Set.range (Fin.tail x₂)) :=
        hprimitive₂
      obtain ⟨a, ha, hpair₁, hpair₂⟩ :=
        exists_bounded_nat_simultaneous_linear_primitive_element_pair
          K₁ (x₁ 0) beta₁ K₂ (x₂ 0) beta₂
      have haD : a ≤ 2 * D * D := by
        have hx₁ : (minpoly K₁ (x₁ 0)).natDegree ≤ D :=
          (minpoly.natDegree_le (x₁ 0)).trans hD₁
        have hb₁ : (minpoly K₁ beta₁).natDegree ≤ D :=
          (minpoly.natDegree_le beta₁).trans hD₁
        have hx₂ : (minpoly K₂ (x₂ 0)).natDegree ≤ D :=
          (minpoly.natDegree_le (x₂ 0)).trans hD₂
        have hb₂ : (minpoly K₂ beta₂).natDegree ≤ D :=
          (minpoly.natDegree_le beta₂).trans hD₂
        calc
          a ≤ (minpoly K₁ (x₁ 0)).natDegree * (minpoly K₁ beta₁).natDegree +
              (minpoly K₂ (x₂ 0)).natDegree * (minpoly K₂ beta₂).natDegree := ha
          _ ≤ D * D + D * D :=
            Nat.add_le_add (Nat.mul_le_mul hx₁ hb₁) (Nat.mul_le_mul hx₂ hb₂)
          _ = 2 * D * D := by ring
      let c' : Fin (n + 1) → ℕ := Fin.cases 1 (fun i ↦ a * c i)
      have hsum₁ : (∑ i, (c' i : K₁) • x₁ i) =
          x₁ 0 + (a : K₁) • beta₁ := by
        rw [Fin.sum_univ_succ]
        simp only [c', Fin.cases_zero, Fin.cases_succ, Nat.cast_one,
          one_smul, Nat.cast_mul, mul_smul]
        rw [Finset.smul_sum]
      have hsum₂ : (∑ i, (c' i : K₂) • x₂ i) =
          x₂ 0 + (a : K₂) • beta₂ := by
        rw [Fin.sum_univ_succ]
        simp only [c', Fin.cases_zero, Fin.cases_succ, Nat.cast_one,
          one_smul, Nat.cast_mul, mul_smul]
        rw [Finset.smul_sum]
      refine ⟨c', ?_, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · change 1 ≤ (2 * D * D + 1) ^ (n + 1)
          exact Nat.one_le_pow _ _ (by omega)
        · change a * c j ≤ (2 * D * D + 1) ^ (n + 1)
          calc
            a * c j ≤ (2 * D * D + 1) * (2 * D * D + 1) ^ n :=
              Nat.mul_le_mul (haD.trans (Nat.le_succ _)) (hc j)
            _ = (2 * D * D + 1) ^ (n + 1) := by
              rw [pow_succ]
              exact Nat.mul_comm _ _
      · rw [hsum₁, ← hpair₁, Fin.range_fin_succ]
        calc
          K₁⟮x₁ 0, beta₁⟯ = IntermediateField.adjoin K₁
              (Set.insert (x₁ 0) (K₁⟮beta₁⟯ : Set E₁)) :=
            (IntermediateField.adjoin_insert_adjoin (F := K₁)
              (S := ({beta₁} : Set E₁)) (x₁ 0)).symm
          _ = IntermediateField.adjoin K₁
              (Set.insert (x₁ 0)
                (IntermediateField.adjoin K₁
                  (Set.range (Fin.tail x₁)) : Set E₁)) := by
            rw [hbeta₁]
          _ = IntermediateField.adjoin K₁
              (Set.insert (x₁ 0) (Set.range (Fin.tail x₁))) :=
            IntermediateField.adjoin_insert_adjoin (F := K₁)
              (S := Set.range (Fin.tail x₁)) (x₁ 0)
      · rw [hsum₂, ← hpair₂, Fin.range_fin_succ]
        calc
          K₂⟮x₂ 0, beta₂⟯ = IntermediateField.adjoin K₂
              (Set.insert (x₂ 0) (K₂⟮beta₂⟯ : Set E₂)) :=
            (IntermediateField.adjoin_insert_adjoin (F := K₂)
              (S := ({beta₂} : Set E₂)) (x₂ 0)).symm
          _ = IntermediateField.adjoin K₂
              (Set.insert (x₂ 0)
                (IntermediateField.adjoin K₂
                  (Set.range (Fin.tail x₂)) : Set E₂)) := by
            rw [hbeta₂]
          _ = IntermediateField.adjoin K₂
              (Set.insert (x₂ 0) (Set.range (Fin.tail x₂))) :=
            IntermediateField.adjoin_insert_adjoin (F := K₂)
              (S := Set.range (Fin.tail x₂)) (x₂ 0)

end
end TranslatedDepthSeven
