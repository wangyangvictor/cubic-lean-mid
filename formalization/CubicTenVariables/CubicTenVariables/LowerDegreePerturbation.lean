import CubicTenVariables.TotalDegreePowerSpan
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Quotient bounds preserved by lower-degree perturbations

Exact homogeneous coordinate-power certificates for a fixed family give
uniform finite-module and field dimension bounds for all perturbations of
strictly lower degree. The proof works over any commutative coefficient ring.
Once the certificates are supplied, no separate homogeneity hypothesis on
the generators is needed; their prescribed degrees enter the certificates
and the strict perturbation bounds explicitly.
-/

noncomputable section
namespace CubicTenVariables.LowerDegreePerturbation
open MvPolynomial
open scoped BigOperators

variable {n : ℕ} {ι R : Type*} [Fintype ι] [CommRing R]

/-- The explicit lower-degree residue of a coordinate power. -/
def remainder (f f' : ι → MvPolynomial (Fin n) R)
    (c : Fin n → ι → MvPolynomial (Fin n) R) (i : Fin n) :
    MvPolynomial (Fin n) R := ∑ j, c i j * (f j - f' j)

omit [Fintype ι] in
/-- Zero coefficients impose no incompatible degree-sum condition. Each
nonzero term has strictly smaller degree than the corresponding power. -/
theorem term_totalDegree_lt
    (f f' : ι → MvPolynomial (Fin n) R) (e : ι → ℕ) (d : Fin n → ℕ)
    (c : Fin n → ι → MvPolynomial (Fin n) R)
    (hd : ∀ i, 0 < d i)
    (hc : ∀ i j, (c i j).IsHomogeneous (d i - e j))
    (hzero : ∀ i j, d i < e j → c i j = 0)
    (hpert : ∀ j, (f' j - f j).totalDegree < e j) (i : Fin n) (j : ι) :
    (c i j * (f j - f' j)).totalDegree < d i := by
  by_cases hz : c i j = 0
  · simpa only [hz, zero_mul, totalDegree_zero] using hd i
  have hle : e j ≤ d i := by
    by_contra h
    exact hz (hzero i j (by omega))
  have hcdeg := (hc i j).totalDegree_le
  have hdiff : (f j - f' j).totalDegree < e j := by
    rw [← totalDegree_neg (f j - f' j), neg_sub]
    exact hpert j
  have hmul := totalDegree_mul (c i j) (f j - f' j)
  omega

/-- The concrete remainder has strictly smaller total degree. -/
theorem remainder_totalDegree_lt
    (f f' : ι → MvPolynomial (Fin n) R) (e : ι → ℕ) (d : Fin n → ℕ)
    (c : Fin n → ι → MvPolynomial (Fin n) R)
    (hd : ∀ i, 0 < d i)
    (hc : ∀ i j, (c i j).IsHomogeneous (d i - e j))
    (hzero : ∀ i j, d i < e j → c i j = 0)
    (hpert : ∀ j, (f' j - f j).totalDegree < e j) (i : Fin n) :
    (remainder f f' c i).totalDegree < d i := by
  have hs : (remainder f f' c i).totalDegree ≤ d i - 1 :=
    totalDegree_finsetSum_le (fun j _ => Nat.le_sub_one_of_lt
      (term_totalDegree_lt f f' e d c hd hc hzero hpert i j))
  exact hs.trans_lt (Nat.sub_lt (hd i) (by decide))

/-- The original power identity becomes the actual perturbed-ideal relation. -/
theorem power_sub_remainder_mem
    (f f' : ι → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (c : Fin n → ι → MvPolynomial (Fin n) R)
    (hcert : ∀ i, X i ^ d i = ∑ j, c i j * f j) (i : Fin n) :
    X i ^ d i - remainder f f' c i ∈ Ideal.span (Set.range f') := by
  have hid : X i ^ d i - remainder f f' c i = ∑ j, c i j * f' j := by
    rw [hcert, remainder]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    abel
  rw [hid]
  apply Ideal.sum_mem
  intro j _
  exact Ideal.mul_mem_left _ (c i j) (Ideal.subset_span ⟨j,rfl⟩)

/-- Exact lower-degree coordinate relations in the ideal of the perturbed
family. These are constructed explicitly, not assumed as a new input. -/
theorem exists_lower_degree_relations
    (f f' : ι → MvPolynomial (Fin n) R) (e : ι → ℕ) (d : Fin n → ℕ)
    (c : Fin n → ι → MvPolynomial (Fin n) R)
    (hd : ∀ i, 0 < d i)
    (hc : ∀ i j, (c i j).IsHomogeneous (d i - e j))
    (hzero : ∀ i j, d i < e j → c i j = 0)
    (hcert : ∀ i, X i ^ d i = ∑ j, c i j * f j)
    (hpert : ∀ j, (f' j - f j).totalDegree < e j) :
    ∃ g : Fin n → MvPolynomial (Fin n) R,
      (∀ i, X i ^ d i - g i ∈ Ideal.span (Set.range f')) ∧
      ∀ i, (g i).totalDegree < d i :=
  ⟨remainder f f' c, power_sub_remainder_mem f f' d c hcert,
    remainder_totalDegree_lt f f' e d c hd hc hzero hpert⟩

/-- Uniform finite generation over the coefficient ring after all permitted
lower-degree perturbations of the fixed certificate. -/
theorem finite_quotient
    (f f' : ι → MvPolynomial (Fin n) R) (e : ι → ℕ) (d : Fin n → ℕ)
    (c : Fin n → ι → MvPolynomial (Fin n) R)
    (hd : ∀ i, 0 < d i)
    (hc : ∀ i j, (c i j).IsHomogeneous (d i - e j))
    (hzero : ∀ i j, d i < e j → c i j = 0)
    (hcert : ∀ i, X i ^ d i = ∑ j, c i j * f j)
    (hpert : ∀ j, (f' j - f j).totalDegree < e j) :
    Module.Finite R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f')) := by
  obtain ⟨g,hrel,hdeg⟩ := exists_lower_degree_relations f f' e d c hd hc hzero hcert hpert
  exact TotalDegreePowerSpan.finite_quotient _ d g hrel hdeg

/-- The same product of coordinate exponents bounds every perturbed
quotient dimension. All dependence on the perturbation is in hpert. -/
theorem finrank_quotient_le {K : Type*} [Field K]
    (f f' : ι → MvPolynomial (Fin n) K) (e : ι → ℕ) (d : Fin n → ℕ)
    (c : Fin n → ι → MvPolynomial (Fin n) K)
    (hd : ∀ i, 0 < d i)
    (hc : ∀ i j, (c i j).IsHomogeneous (d i - e j))
    (hzero : ∀ i j, d i < e j → c i j = 0)
    (hcert : ∀ i, X i ^ d i = ∑ j, c i j * f j)
    (hpert : ∀ j, (f' j - f j).totalDegree < e j) :
    Module.finrank K (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range f')) ≤ ∏ i, d i := by
  obtain ⟨g,hrel,hdeg⟩ := exists_lower_degree_relations f f' e d c hd hc hzero hcert hpert
  exact TotalDegreePowerSpan.finrank_quotient_le _ d g hrel hdeg

end CubicTenVariables.LowerDegreePerturbation
