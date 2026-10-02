import CubicTenVariables.BinarySliceCounting
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Specializing complementary coordinates cannot change a pure coefficient
of maximal total degree. These are polynomial identities over the coefficient
ring, with no geometric or point-counting premise. -/

noncomputable section
namespace CubicTenVariables.BinarySliceLeadingCoefficient

open MvPolynomial BinarySliceCounting

private theorem exponent_lt_of_ne_single {n d : ℕ} (m : Fin n →₀ ℕ)
    (i : Fin n) (hd : m.sum (fun _ a => a) ≤ d)
    (hne : m ≠ Finsupp.single i d) : m i < d := by
  classical
  rw [Finsupp.sum_fintype _ _ (by simp)] at hd
  have hi : m i ≤ d := (Finset.single_le_sum (fun j _ => Nat.zero_le (m j))
    (Finset.mem_univ i)).trans hd
  by_contra h
  have hid : m i = d := by omega
  have hsum : ∑ j ∈ Finset.univ.erase i, m j = 0 := by
    have he := Finset.add_sum_erase Finset.univ (fun j => m j) (Finset.mem_univ i)
    dsimp only at he
    omega
  apply hne
  ext j
  by_cases hj : j = i
  · subst j
    simpa using hid
  · have hz : m j = 0 := (Finset.sum_eq_zero_iff.mp hsum) j (by simp [hj])
    simpa [Finsupp.single_apply, hj] using hz

private theorem degreeOf_substitution_variable {n : ℕ} {R : Type*}
    [CommRing R] [Nontrivial R] (e : Fin 2 ↪ Fin n)
    (w : Complement e → R) (j : Fin 2) (i : Fin n) :
    (combine e (X : Fin 2 → MvPolynomial (Fin 2) R) (fun a => C (w a)) i).degreeOf j
      ≤ if i = e j then 1 else 0 := by
  classical
  by_cases hi : i ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hi
    simp only [combine_selected, degreeOf_X, e.injective.eq_iff]
    split_ifs <;> simp_all
  · have hij : i ≠ e j := fun h => hi (h ▸ Set.mem_range_self j)
    simp [combine_complement e _ _ i hi, hij]

private theorem degreeOf_substituted_monomial {n : ℕ} {R : Type*}
    [CommRing R] [Nontrivial R] (e : Fin 2 ↪ Fin n)
    (w : Complement e → R) (j : Fin 2) (m : Fin n →₀ ℕ) (c : R) :
    (aeval (combine e (X : Fin 2 → MvPolynomial (Fin 2) R)
      (fun a => C (w a))) (monomial m c)).degreeOf j ≤ m (e j) := by
  classical
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (by simp)]
  change (C c * ∏ i, (combine e X (fun a => C (w a)) i) ^ m i).degreeOf j ≤ _
  refine (degreeOf_C_mul_le _ j c).trans ?_
  refine (degreeOf_prod_le j Finset.univ _).trans ?_
  calc
    _ ≤ ∑ i : Fin n, m i * (if i = e j then 1 else 0) := by
      apply Finset.sum_le_sum
      intro i _
      exact (degreeOf_pow_le j _ _).trans
        (Nat.mul_le_mul_left _ (degreeOf_substitution_variable e w j i))
    _ = m (e j) := by simp

/-- A pure coefficient at the total-degree bound is unchanged by fixing
the complementary coordinates. The values fixed there are arbitrary. -/
theorem coeff_pure_slice {n d : ℕ} {R : Type*} [CommRing R] [Nontrivial R]
    (e : Fin 2 ↪ Fin n) (F : MvPolynomial (Fin n) R)
    (w : Complement e → R) (j : Fin 2) (hF : F.totalDegree ≤ d) :
    coeff (Finsupp.single j d)
      (aeval (combine e (X : Fin 2 → MvPolynomial (Fin 2) R) (fun i => C (w i))) F)
      = coeff (Finsupp.single (e j) d) F := by
  classical
  conv_lhs => rw [F.as_sum]
  rw [map_sum, coeff_sum]
  conv_rhs => rw [F.as_sum]
  rw [coeff_sum]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases he : m = Finsupp.single (e j) d
  · subst m
    simp [aeval_monomial, coeff_X_pow]
  · have hmd : m (e j) < d := exponent_lt_of_ne_single m (e j)
      ((le_totalDegree hm).trans hF) he
    have hz : coeff (Finsupp.single j d)
        (aeval (combine e (X : Fin 2 → MvPolynomial (Fin 2) R)
          (fun i => C (w i))) (monomial m (coeff m F))) = 0 := by
      by_contra hn
      have hl := monomial_le_degreeOf j (mem_support_iff.mpr hn)
      simp only [Finsupp.single_eq_same] at hl
      have hu := degreeOf_substituted_monomial e w j m (coeff m F)
      omega
    rw [hz, coeff_monomial]
    simp [he]

private theorem monomial_slice_product {n : ℕ} {R : Type*} [CommRing R]
    (e : Fin 2 ↪ Fin n) (m : Fin n →₀ ℕ) (c : R) (w : Complement e → R) :
    aeval (combine e (X : Fin 2 → MvPolynomial (Fin 2) R) (fun i => C (w i)))
      (monomial m c) =
      C c * ((∏ j : Fin 2, X j ^ m (e j)) *
        ∏ i : Complement e, C (w i) ^ m i) := by
  classical
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (by simp)]
  change C c * _ = _
  congr 1
  have h := Equiv.prod_comp (indexEquiv e)
    (fun i => (combine e (X : Fin 2 → MvPolynomial (Fin 2) R)
      (fun a => C (w a)) i) ^ m i)
  simpa only [Fintype.prod_sum_type, indexEquiv_inl, indexEquiv_inr,
    combine_selected, combine_complement_index] using h.symm

private theorem monomial_slice_homogeneous {n : ℕ} {R : Type*} [CommRing R]
    (e : Fin 2 ↪ Fin n) (m : Fin n →₀ ℕ) (c : R) (w : Complement e → R) :
    (aeval (combine e (X : Fin 2 → MvPolynomial (Fin 2) R) (fun i => C (w i)))
      (monomial m c)).IsHomogeneous (∑ j : Fin 2, m (e j)) := by
  rw [monomial_slice_product]
  apply IsHomogeneous.C_mul
  have hs : (∏ j : Fin 2, (X j : MvPolynomial (Fin 2) R) ^ m (e j)).IsHomogeneous
      (∑ j : Fin 2, m (e j)) :=
    IsHomogeneous.prod _ _ _ (fun j _ => isHomogeneous_X_pow j _)
  have hc : (∏ i : Complement e, (C (w i) : MvPolynomial (Fin 2) R) ^ m i).IsHomogeneous 0 := by
    simpa using IsHomogeneous.prod Finset.univ
      (fun i : Complement e => (C (w i) : MvPolynomial (Fin 2) R) ^ m i)
      (fun _ => 0) (fun i _ => by simpa using (isHomogeneous_C (Fin 2) (w i)).pow (m i))
  simpa only [add_zero] using hs.mul hc

private theorem top_component_monomial_slice {n d : ℕ} {R : Type*} [CommRing R]
    (e : Fin 2 ↪ Fin n) (m : Fin n →₀ ℕ) (c : R) (w : Complement e → R)
    (hm : m.degree = d) :
    homogeneousComponent d
      (aeval (combine e (X : Fin 2 → MvPolynomial (Fin 2) R) (fun i => C (w i)))
        (monomial m c)) =
      aeval (combine e (X : Fin 2 → MvPolynomial (Fin 2) R) (fun _ => 0))
        (monomial m c) := by
  classical
  have hsum : (∑ j : Fin 2, m (e j)) + (∑ i : Complement e, m i) = d := by
    rw [← sum_split e (fun i => m i), ← Finsupp.degree_eq_sum, hm]
  rw [homogeneousComponent_of_mem (monomial_slice_homogeneous e m c w)]
  by_cases hcomp : ∑ i : Complement e, m i = 0
  · have hsel : ∑ j : Fin 2, m (e j) = d := by omega
    rw [hsel, if_pos rfl, monomial_slice_product]
    have hz : ∀ i : Complement e, m i = 0 := fun i =>
      (Finset.sum_eq_zero_iff.mp hcomp) i (Finset.mem_univ i)
    have hzero := monomial_slice_product e m c (0 : Complement e → R)
    simpa only [Pi.zero_apply, C_0, hz, pow_zero, Finset.prod_const_one, mul_one] using hzero.symm
  · have hsel : d ≠ ∑ j : Fin 2, m (e j) := by omega
    rw [if_neg hsel]
    have hi : ∃ i : Complement e, m i ≠ 0 := by
      by_contra hn
      push_neg at hn
      simp only [hn, Finset.sum_const_zero] at hcomp
      exact hcomp trivial
    obtain ⟨i, hi⟩ := hi
    have hzero := monomial_slice_product e m c (0 : Complement e → R)
    have hp : (∏ a : Complement e, (0 : MvPolynomial (Fin 2) R) ^ m a) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
    simpa only [Pi.zero_apply, C_0, hp, mul_zero] using hzero.symm

/-- For a homogeneous polynomial, the complete leading homogeneous part
of every translated binary slice is exactly its restriction with all
complementary coordinates set to zero. -/
theorem homogeneousComponent_slice {n d : ℕ} {R : Type*} [CommRing R]
    (e : Fin 2 ↪ Fin n) (F : MvPolynomial (Fin n) R)
    (w : Complement e → R) (hF : F.IsHomogeneous d) :
    homogeneousComponent d
      (aeval (combine e (X : Fin 2 → MvPolynomial (Fin 2) R) (fun i => C (w i))) F) =
      aeval (combine e (X : Fin 2 → MvPolynomial (Fin 2) R) (fun _ => 0)) F := by
  classical
  conv_lhs => rw [F.as_sum]
  rw [map_sum, map_sum]
  conv_rhs => rw [F.as_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply top_component_monomial_slice
  rw [Finsupp.degree_eq_weight_one]
  exact hF (mem_support_iff.mp hm)

end CubicTenVariables.BinarySliceLeadingCoefficient
