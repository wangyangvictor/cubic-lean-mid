import TranslatedDepthSeven.ComponentHilbertInjectionInternal
import TranslatedDepthSeven.ProjectiveZerofoldDegreeOneInternal
import Mathlib.Analysis.Polynomial.Basic

/-!
# Homogeneous forms separating equal-dimensional prime components

Pairwise incomparability supplies homogeneous ideal differences. Their
products separate each component from all the others. Multiplication by a
power of a surviving coordinate puts the separators in one common degree.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published Filter

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 300000

universe u v

/-- A rational polynomial with positive leading coefficient is eventually
positive on the nonnegative integers, including the constant case. -/
theorem polynomial_eventually_pos_nat_of_leadingCoeff_pos
    (P : Polynomial ℚ) (hpositive : 0 < P.leadingCoeff) :
    ∀ᶠ n : ℕ in atTop, 0 < P.eval (n : ℚ) := by
  by_cases hzero : P.natDegree = 0
  · have hP := Polynomial.eq_C_of_natDegree_eq_zero hzero
    have heval (t : ℚ) : P.eval t = P.leadingCoeff := by rw [hP]; simp
    exact Eventually.of_forall fun n ↦ by rw [heval]; exact hpositive
  · have hdegree : 0 < P.degree :=
      Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hzero)
    have ht := (P.tendsto_atTop_of_leadingCoeff_nonneg hdegree hpositive.le).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℚ)) atTop atTop)
    exact ht.eventually (eventually_gt_atTop 0)

/-- Positive projective degree implies that a coordinate survives, with no
separate saturation or irrelevant-ideal assumption. -/
theorem exists_coordinate_not_mem_of_projectiveHilbertDimensionDegree
    {K : Type u} [Field K] {N r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hI : HasProjectiveHilbertDimensionDegree I r d) :
    ∃ i : Fin (N + 1), X i ∉ I := by
  obtain ⟨hd, P, _hPdegree, hPlc, k₀, heventual⟩ := hI
  have hpositive : 0 < P.leadingCoeff := by
    rw [hPlc]
    exact div_pos (by exact_mod_cast hd) (by exact_mod_cast Nat.factorial_pos r)
  have hev : ∀ᶠ k : ℕ in atTop, k₀ ≤ k ∧ 0 < k ∧ 0 < P.eval (k : ℚ) := by
    filter_upwards [polynomial_eventually_pos_nat_of_leadingCoeff_pos P hpositive,
      eventually_ge_atTop (k₀ + 1)] with k hpos hk
    exact ⟨by omega, by omega, hpos⟩
  obtain ⟨k, hk, hkpos, hpos⟩ := hev.exists
  apply exists_coordinate_not_mem_of_positive_projectiveHilbertPiece I hkpos
  rw [← heventual k hk] at hpos
  exact_mod_cast hpos

/-- Distinct homogeneous prime components with a common projective
dimension admit separators in one common degree. -/
theorem exists_equal_degree_homogeneous_component_separators
    {K : Type u} [Field K] {N r : ℕ}
    {ι : Type v} [Fintype ι]
    (P : ι → Ideal (MvPolynomial (Fin (N + 1)) K))
    (d : ι → ℕ) (hinjective : Function.Injective P)
    (hprime : ∀ i, (P i).IsPrime)
    (hhom : ∀ i, (P i).IsHomogeneous
      (homogeneousSubmodule (Fin (N + 1)) K))
    (hdim : ∀ i, HasProjectiveDimensionDegree (P i) r (d i)) :
    ∃ (E : ℕ) (g : ι → MvPolynomial (Fin (N + 1)) K),
      (∀ i, (g i).IsHomogeneous E) ∧ (∀ i, g i ∉ P i) ∧
        (∀ i j, i ≠ j → g i ∈ P j) := by
  classical
  have hsep : ∀ i j, ∃ (e : ℕ) (f : MvPolynomial (Fin (N + 1)) K),
      f.IsHomogeneous e ∧ f ∉ P i ∧ (i ≠ j → f ∈ P j) := by
    intro i j
    by_cases hij : i = j
    · refine ⟨0, 1, isHomogeneous_one (Fin (N + 1)) K, (hprime i).one_notMem, ?_⟩
      intro h
      exact (h hij).elim
    · letI : (P i).IsPrime := hprime i
      letI : (P j).IsPrime := hprime j
      have hinc := incomparable_of_distinct_primes_same_finite_quotient_dimension
        (P i) (P j) (fun h ↦ hij (hinjective h))
        (s := r + 1)
        (by simpa only [Nat.cast_add, Nat.cast_one] using (hdim i).1)
        (by simpa only [Nat.cast_add, Nat.cast_one] using (hdim j).1)
      obtain ⟨e, f, hfhom, hfmem, hfnot⟩ :=
        exists_homogeneous_form_mem_not_mem_of_not_le (P i) (P j) (hhom j) hinc.2
      exact ⟨e, f, hfhom, hfnot, fun _ ↦ hfmem⟩
  choose e f hfhom hfnot hfmem using hsep
  let s (i : ι) : MvPolynomial (Fin (N + 1)) K := ∏ j, f i j
  let de (i : ι) : ℕ := ∑ j, e i j
  have hshom (i : ι) : (s i).IsHomogeneous (de i) :=
    IsHomogeneous.prod Finset.univ _ _ (fun j _ ↦ hfhom i j)
  have hsnot (i : ι) : s i ∉ P i := by
    letI : (P i).IsPrime := hprime i
    have hnonzero : Ideal.Quotient.mk (P i) (s i) ≠ 0 := by
      dsimp only [s]
      rw [map_prod]
      apply Finset.prod_ne_zero_iff.mpr
      intro j _
      exact fun h ↦ hfnot i j (Ideal.Quotient.eq_zero_iff_mem.mp h)
    exact fun h ↦ hnonzero (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  have hsmem (i j : ι) (hij : i ≠ j) : s i ∈ P j :=
    (P j).prod_mem (Finset.mem_univ j) (hfmem i j hij)
  choose coordinate hcoordinate using fun i ↦
    exists_coordinate_not_mem_of_projectiveHilbertDimensionDegree (P i)
      (hdim i).toHilbert
  let E := Finset.univ.sup de
  have hle (i : ι) : de i ≤ E := Finset.le_sup (Finset.mem_univ i)
  refine ⟨E, fun i ↦ s i * X (coordinate i) ^ (E - de i), ?_, ?_, ?_⟩
  · intro i
    have hh := (hshom i).mul
      (isHomogeneous_X_pow (R := K) (coordinate i) (E - de i))
    simpa only [Nat.add_sub_of_le (hle i)] using hh
  · intro i
    apply (hprime i).mul_notMem (hsnot i)
    intro h
    exact hcoordinate i ((hprime i).mem_of_pow_mem (E - de i) h)
  · intro i j hij
    exact (P j).mul_mem_right _ (hsmem i j hij)

/-- The actual finite family of equal-dimensional homogeneous primes gives
one uniform shift for the Hilbert-function inequality, for every degree. -/
theorem exists_shift_sum_finrank_homogeneousComponents_le
    {K : Type u} [Field K] {N r : ℕ}
    {ι : Type v} [Fintype ι]
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (P : ι → Ideal (MvPolynomial (Fin (N + 1)) K))
    (d : ι → ℕ) (hinjective : Function.Injective P)
    (hprime : ∀ i, (P i).IsPrime)
    (hhom : ∀ i, (P i).IsHomogeneous
      (homogeneousSubmodule (Fin (N + 1)) K))
    (hdim : ∀ i, HasProjectiveDimensionDegree (P i) r (d i))
    (hcontain : ∀ i, I ≤ P i) :
    ∃ E : ℕ, ∀ k : ℕ,
      (∑ i, Module.finrank K (projectiveHilbertPiece K N (P i) k)) ≤
        Module.finrank K (projectiveHilbertPiece K N I (k + E)) := by
  obtain ⟨E, g, hghom, hgown, hgother⟩ :=
    exists_equal_degree_homogeneous_component_separators P d hinjective hprime hhom hdim
  exact ⟨E, fun k ↦ sum_finrank_homogeneousComponents_le_of_separating_forms
    I P hprime hcontain E g hghom hgown hgother k⟩

end

end TranslatedDepthSeven
