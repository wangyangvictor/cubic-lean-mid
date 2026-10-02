import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Primitive elements which are linear combinations

For a projective birational projection one needs a primitive element which
is a *linear* form in the original homogeneous coordinates.  The usual
primitive-element theorem only exposes an arbitrary element of the field.
The first lemma below records the stronger statement actually proved in
Mathlib's infinite-field argument: two separable elements are replaced by
`alpha + c * beta`.  Iteration keeps the final primitive element in the
ground-field linear span of the displayed generators.
-/

namespace TranslatedDepthSeven

noncomputable section

open Polynomial IntermediateField

universe u v

/-- The two-generator primitive-element theorem with the linear combination
visible in the conclusion. -/
theorem exists_linear_primitive_element_pair
    (F : Type u) {E : Type v}
    [Field F] [Infinite F] [Field E] [Algebra F E]
    [Algebra.IsSeparable F E] (alpha beta : E) :
    ∃ c : F, F⟮alpha, beta⟯ = F⟮alpha + c • beta⟯ := by
  classical
  have halpha := Algebra.IsSeparable.isIntegral F alpha
  have hbeta := Algebra.IsSeparable.isIntegral F beta
  let f := minpoly F alpha
  let g := minpoly F beta
  let iFE := algebraMap F E
  let iEE' := algebraMap E (SplittingField (g.map iFE))
  obtain ⟨c, hc⟩ :=
    Field.primitive_element_inf_aux_exists_c
      (iEE'.comp iFE) (iEE' alpha) (iEE' beta) f g
  refine ⟨c, ?_⟩
  let gamma := alpha + c • beta
  suffices beta_in : beta ∈ F⟮gamma⟯ by
    apply le_antisymm
    · rw [adjoin_le_iff]
      have alpha_in : alpha ∈ F⟮gamma⟯ := by
        rw [← add_sub_cancel_right alpha (c • beta)]
        exact F⟮gamma⟯.sub_mem (mem_adjoin_simple_self F gamma)
          (F⟮gamma⟯.toSubalgebra.smul_mem beta_in c)
      rintro x (rfl | rfl) <;> assumption
    · rw [adjoin_simple_le_iff]
      have alpha_in : alpha ∈ F⟮alpha, beta⟯ :=
        subset_adjoin F {alpha, beta} (Set.mem_insert alpha {beta})
      have beta_in' : beta ∈ F⟮alpha, beta⟯ :=
        subset_adjoin F {alpha, beta} (Set.mem_insert_of_mem alpha rfl)
      exact F⟮alpha, beta⟯.add_mem alpha_in
        (F⟮alpha, beta⟯.smul_mem beta_in')
  let p := EuclideanDomain.gcd
    ((f.map (algebraMap F F⟮gamma⟯)).comp
      (C (AdjoinSimple.gen F gamma) -
        (C ↑c : F⟮gamma⟯[X]) * X))
    (g.map (algebraMap F F⟮gamma⟯))
  let h := EuclideanDomain.gcd
    ((f.map iFE).comp (C gamma - C (iFE c) * X)) (g.map iFE)
  have map_g_ne_zero : g.map iFE ≠ 0 :=
    map_ne_zero (minpoly.ne_zero hbeta)
  have h_ne_zero : h ≠ 0 :=
    mt EuclideanDomain.gcd_eq_zero_iff.mp
      (not_and.mpr fun _ ↦ map_g_ne_zero)
  suffices p_linear :
      p.map (algebraMap F⟮gamma⟯ E) =
        C h.leadingCoeff * (X - C beta) by
    have finale :
        beta = algebraMap F⟮gamma⟯ E (-p.coeff 0 / p.coeff 1) := by
      simp [map_div₀, map_neg, ← coeff_map, ← coeff_map, p_linear,
        mul_sub, coeff_C, mul_div_cancel_left₀ beta
          (mt leadingCoeff_eq_zero.mp h_ne_zero)]
    rw [finale]
    exact Subtype.mem (-p.coeff 0 / p.coeff 1)
  have h_sep : h.Separable :=
    separable_gcd_right _
      (.map (Algebra.IsSeparable.isSeparable F beta))
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
    specialize hc (iEE' gamma - iEE' (iFE c) * x) (by
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
    convert (gcd_map (algebraMap F⟮gamma⟯ E)).symm
  · simp only [map_comp, Polynomial.map_map, ← IsScalarTower.algebraMap_eq,
      Polynomial.map_sub, map_C, AdjoinSimple.algebraMap_gen,
      Polynomial.map_mul, map_X]
    congr

/-- The finite exceptional set in the primitive-element argument can be
avoided already in an arbitrary infinite subfield of the base field.  This
is the coefficient-selection input needed when the base is, for example, a
rational-function field but the desired linear forms must have rational
coefficients. -/
theorem exists_coefficient_from_infinite_subfield_avoiding_roots
    (F : Type u) (K : Type v) {E : Type*}
    [Field F] [Infinite F] [Field K] [Field E]
    (e : F →+* K) (ι : K →+* E) (alpha beta : E)
    (f g : K[X]) :
    ∃ c : F,
      ∀ alpha' ∈ (f.map ι).roots,
        ∀ beta' ∈ (g.map ι).roots,
          -(alpha' - alpha) / (beta' - beta) ≠ ι (e c) := by
  classical
  let sf := (f.map ι).roots
  let sg := (g.map ι).roots
  let s := (sf.bind fun alpha' =>
    sg.map fun beta' => -(alpha' - alpha) / (beta' - beta)).toFinset
  let s' := s.preimage (ι.comp e) fun x _ y _ h => (ι.comp e).injective h
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset s'
  simp_rw [s', s, Finset.mem_preimage, Multiset.mem_toFinset,
    Multiset.mem_bind, Multiset.mem_map] at hc
  push_neg at hc
  exact ⟨c, hc⟩

/-- A separable pair has a primitive linear combination whose coefficient
comes from a chosen infinite subfield of the base. -/
theorem exists_linear_primitive_element_pair_of_infinite_subfield
    (F : Type u) (K : Type v) {E : Type*}
    [Field F] [Infinite F] [Field K] [Algebra F K]
    [Field E] [Algebra K E] [Algebra F E] [IsScalarTower F K E]
    [Algebra.IsSeparable K E] (alpha beta : E) :
    ∃ c : F,
      K⟮alpha, beta⟯ = K⟮alpha + (algebraMap F K c) • beta⟯ := by
  classical
  have halpha := Algebra.IsSeparable.isIntegral K alpha
  have hbeta := Algebra.IsSeparable.isIntegral K beta
  let f := minpoly K alpha
  let g := minpoly K beta
  let iKE := algebraMap K E
  let iEE' := algebraMap E (SplittingField (g.map iKE))
  obtain ⟨c, hc⟩ :=
    exists_coefficient_from_infinite_subfield_avoiding_roots F K
      (algebraMap F K) (iEE'.comp iKE) (iEE' alpha) (iEE' beta) f g
  refine ⟨c, ?_⟩
  let gamma := alpha + (algebraMap F K c) • beta
  suffices beta_in : beta ∈ K⟮gamma⟯ by
    apply le_antisymm
    · rw [adjoin_le_iff]
      have alpha_in : alpha ∈ K⟮gamma⟯ := by
        rw [← add_sub_cancel_right alpha ((algebraMap F K c) • beta)]
        exact K⟮gamma⟯.sub_mem (mem_adjoin_simple_self K gamma)
          (K⟮gamma⟯.toSubalgebra.smul_mem beta_in (algebraMap F K c))
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
        (C ↑(algebraMap F K c) : K⟮gamma⟯[X]) * X))
    (g.map (algebraMap K K⟮gamma⟯))
  let h := EuclideanDomain.gcd
    ((f.map iKE).comp
      (C gamma - C (iKE (algebraMap F K c)) * X))
    (g.map iKE)
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
    specialize hc
      (iEE' gamma - iEE' (iKE (algebraMap F K c)) * x) (by
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

/-- A finite family of separable elements has a primitive element in its
span over any chosen infinite subfield of the base field. -/
theorem exists_primitive_element_mem_span_finset_of_infinite_subfield
    (F : Type u) (K : Type v) {E : Type*}
    [Field F] [Infinite F] [Field K] [Algebra F K]
    [Field E] [Algebra K E] [Algebra F E] [IsScalarTower F K E]
    [Algebra.IsSeparable K E] (S : Finset E) :
    ∃ alpha : E, alpha ∈ Submodule.span F (↑S : Set E) ∧
      K⟮alpha⟯ = IntermediateField.adjoin K (↑S : Set E) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_, ?_⟩
      · simp
      · simp
  | @insert a S ha ih =>
      obtain ⟨beta, hbetaSpan, hbetaAdjoin⟩ := ih
      obtain ⟨c, hpair⟩ :=
        exists_linear_primitive_element_pair_of_infinite_subfield F K a beta
      have hpair' : K⟮a, beta⟯ = K⟮a + c • beta⟯ := by
        simpa only [Algebra.smul_def,
          ← IsScalarTower.algebraMap_apply F K E] using hpair
      refine ⟨a + c • beta, ?_, ?_⟩
      · apply Submodule.add_mem
        · exact Submodule.subset_span (by simp)
        · apply Submodule.smul_mem
          exact (Submodule.span_mono (by simp)) hbetaSpan
      · rw [← hpair']
        calc
          K⟮a, beta⟯ =
              IntermediateField.adjoin K
                (Set.insert a (K⟮beta⟯ : Set E)) := by
            exact (IntermediateField.adjoin_insert_adjoin
              (F := K) (S := ({beta} : Set E)) a).symm
          _ = IntermediateField.adjoin K
                (Set.insert a
                  (IntermediateField.adjoin K (↑S : Set E) : Set E)) := by
            rw [hbetaAdjoin]
          _ = IntermediateField.adjoin K
                (Set.insert a (↑S : Set E)) := by
            exact IntermediateField.adjoin_insert_adjoin
              (F := K) (S := (↑S : Set E)) a
          _ = IntermediateField.adjoin K
                (↑(insert a S) : Set E) := by
            exact congrArg (IntermediateField.adjoin K)
              (Finset.coe_insert a S).symm

/-- Finite-family form with coefficients in the selected infinite subfield.
In particular, taking `F = ℚ` gives a rational linear primitive element over
any separable extension of a field containing `ℚ`. -/
theorem exists_linearCombination_primitive_element_of_infinite_subfield
    (F : Type u) (K : Type v) {E : Type*}
    [Field F] [Infinite F] [Field K] [Algebra F K]
    [Field E] [Algebra K E] [Algebra F E] [IsScalarTower F K E]
    [Algebra.IsSeparable K E]
    {n : ℕ} (x : Fin n → E) :
    ∃ c : Fin n → F,
      K⟮∑ i, c i • x i⟯ = IntermediateField.adjoin K (Set.range x) := by
  classical
  let S : Finset E := Finset.univ.image x
  obtain ⟨alpha, halphaSpan, halphaAdjoin⟩ :=
    exists_primitive_element_mem_span_finset_of_infinite_subfield F K S
  have hS : (↑S : Set E) = Set.range x := by
    ext y
    simp [S]
  have halphaRange : alpha ∈ Submodule.span F (Set.range x) := by
    simpa only [hS] using halphaSpan
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun F).mp halphaRange
  refine ⟨c, ?_⟩
  rw [hc]
  simpa only [hS] using halphaAdjoin

/-- Rational-coefficient specialization of the infinite-subfield theorem.
This applies in particular when `K` is a rational-function field over
`ℚ`; the extension `E / K` need only satisfy the displayed separability
hypothesis. -/
theorem exists_rational_linearCombination_primitive_element
    (K : Type v) {E : Type*}
    [Field K] [Algebra ℚ K]
    [Field E] [Algebra K E] [Algebra ℚ E] [IsScalarTower ℚ K E]
    [Algebra.IsSeparable K E]
    {n : ℕ} (x : Fin n → E) :
    ∃ c : Fin n → ℚ,
      K⟮∑ i, c i • x i⟯ = IntermediateField.adjoin K (Set.range x) := by
  exact exists_linearCombination_primitive_element_of_infinite_subfield ℚ K x

/-- A finite set of separable elements has a primitive element in its
ground-field linear span. -/
theorem exists_primitive_element_mem_span_finset
    (F : Type u) {E : Type v}
    [Field F] [Infinite F] [Field E] [Algebra F E]
    [Algebra.IsSeparable F E] (S : Finset E) :
    ∃ alpha : E, alpha ∈ Submodule.span F (↑S : Set E) ∧
      F⟮alpha⟯ = IntermediateField.adjoin F (↑S : Set E) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_, ?_⟩
      · simp
      · simp
  | @insert a S ha ih =>
      obtain ⟨beta, hbetaSpan, hbetaAdjoin⟩ := ih
      obtain ⟨c, hpair⟩ :=
        exists_linear_primitive_element_pair F a beta
      refine ⟨a + c • beta, ?_, ?_⟩
      · apply Submodule.add_mem
        · exact Submodule.subset_span (by simp)
        · apply Submodule.smul_mem
          exact (Submodule.span_mono (by simp)) hbetaSpan
      · rw [← hpair]
        calc
          F⟮a, beta⟯ =
              IntermediateField.adjoin F
                (Set.insert a (F⟮beta⟯ : Set E)) := by
            exact (IntermediateField.adjoin_insert_adjoin
              (F := F) (S := ({beta} : Set E)) a).symm
          _ = IntermediateField.adjoin F
                (Set.insert a
                  (IntermediateField.adjoin F (↑S : Set E) : Set E)) := by
            rw [hbetaAdjoin]
          _ = IntermediateField.adjoin F
                (Set.insert a (↑S : Set E)) := by
            exact IntermediateField.adjoin_insert_adjoin
              (F := F) (S := (↑S : Set E)) a
          _ = IntermediateField.adjoin F
                (↑(insert a S) : Set E) := by
            exact congrArg (IntermediateField.adjoin F)
              (Finset.coe_insert a S).symm

/-- Finite-family form: the primitive element is a displayed linear
combination of the given generators. -/
theorem exists_linearCombination_primitive_element
    (F : Type u) {E : Type v}
    [Field F] [Infinite F] [Field E] [Algebra F E]
    [Algebra.IsSeparable F E]
    {n : ℕ} (x : Fin n → E) :
    ∃ c : Fin n → F,
      F⟮∑ i, c i • x i⟯ = IntermediateField.adjoin F (Set.range x) := by
  classical
  let S : Finset E := Finset.univ.image x
  obtain ⟨alpha, halphaSpan, halphaAdjoin⟩ :=
    exists_primitive_element_mem_span_finset F S
  have hS : (↑S : Set E) = Set.range x := by
    ext y
    simp [S]
  have halphaRange : alpha ∈ Submodule.span F (Set.range x) := by
    simpa only [hS] using halphaSpan
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun F).mp halphaRange
  refine ⟨c, ?_⟩
  rw [hc]
  simpa only [hS] using halphaAdjoin

end

end TranslatedDepthSeven
