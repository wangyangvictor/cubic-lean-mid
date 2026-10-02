import TranslatedDepthSeven.SupportedRectangularDeterminant
import TranslatedDepthSeven.SmoothSurfaceResidueExponent

/-! Add the exact smooth surface jet exponents across all occupied residue
classes. Each class may use different bivariate polynomials and coordinates.
The factorization has zero entries off its class; no determinant-divisibility
or adapted-basis premise is supplied. -/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial
open scoped BigOperators
set_option maxHeartbeats 1000000

/-- Distinct supported monomials are needed within each class only. -/
theorem pow_dvd_det_rectangular_mul_of_bivariate_blocks
    {ι κ ν : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν]
    (M : Matrix ι κ ℤ) (N : Matrix κ ι ℤ)
    (p : ℤ) (cls : ι → ν) (label : κ → ν) (coord : κ → ℕ × ℕ)
    (hcoord : ∀ c, Set.InjOn coord {a | label a = c})
    (hN : ∀ a j, p ^ ((coord a).1 + (coord a).2) ∣ N a j)
    (hsupport : ∀ a j, N a j ≠ 0 → label a = cls j) :
    p ^ (∑ c, smoothSurfaceJetExponent (Fintype.card {j // cls j = c})) ∣
      (M * N).det := by
  classical
  apply pow_dvd_det_rectangular_mul_of_supported_injective_weight
    M N p (fun a => (coord a).1 + (coord a).2) _ hN
  intro f hf hn
  have hsum (c : ν) :
      smoothSurfaceJetExponent (Fintype.card {j // cls j = c}) ≤
        ∑ j : {j // cls j = c}, ((coord (f j)).1 + (coord (f j)).2) := by
    by_cases hc : Fintype.card {j // cls j = c} = 0
    · simp [hc]
    · obtain ⟨t, u, hcard, _, hexp⟩ := exists_smoothSurfaceJetExponent_layer
        (Fintype.card {j // cls j = c}) (Nat.pos_of_ne_zero hc)
      rw [hexp]
      apply sum_pair_weight_ge_first_affinePlaneJetWeight
        (fun j : {j // cls j = c} => coord (f j)) _ id Function.injective_id t u hcard
      intro i j hij
      apply Subtype.ext
      apply hf
      exact hcoord c (by exact (hsupport _ _ (hn i)).trans i.property)
        (by exact (hsupport _ _ (hn j)).trans j.property) hij
  calc
    _ ≤ ∑ c, ∑ j : {j // cls j = c}, ((coord (f j)).1 + (coord (f j)).2) :=
      Finset.sum_le_sum (fun c _ => hsum c)
    _ = _ := Fintype.sum_fiberwise cls (fun j => (coord (f j)).1 + (coord (f j)).2)

/-- A finite support common to every class and every row. -/
def blockBivariateCommonSupport {ι ν : Type*} [Fintype ι] [Fintype ν]
    (y : ν → Fin 2 → ℤ) (F : ν → ι → MvPolynomial (Fin 2) ℤ) :
    Finset (Fin 2 →₀ ℕ) :=
  Finset.univ.biUnion fun c => translatedBivariateCommonSupport (y c) (F c)

abbrev BlockBivariateMonomialIndex {ι ν : Type*} [Fintype ι] [Fintype ν]
    (y : ν → Fin 2 → ℤ) (F : ν → ι → MvPolynomial (Fin 2) ℤ) :=
  {d : Fin 2 →₀ ℕ // d ∈ blockBivariateCommonSupport y F}

private theorem blockBivariate_support_subset {ι ν : Type*}
    [Fintype ι] [Fintype ν] (y : ν → Fin 2 → ℤ)
    (F : ν → ι → MvPolynomial (Fin 2) ℤ) (c : ν) (i : ι) :
    (translateBivariatePolynomial (y c) (F c i)).support ⊆
      blockBivariateCommonSupport y F := by
  intro d hd
  exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _,
    Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hd⟩⟩

def blockBivariateCoefficientMatrix {ι ν : Type*} [Fintype ι] [Fintype ν]
    (y : ν → Fin 2 → ℤ) (F : ν → ι → MvPolynomial (Fin 2) ℤ) :
    Matrix ι (ν × BlockBivariateMonomialIndex y F) ℤ :=
  fun i a => coeff a.2.val (translateBivariatePolynomial (y a.1) (F a.1 i))

def blockBivariateMonomialMatrix {ι ν : Type*} [Fintype ι] [Fintype ν]
    [DecidableEq ν] (cls : ι → ν)
    (y : ν → Fin 2 → ℤ) (F : ν → ι → MvPolynomial (Fin 2) ℤ)
    (x : ι → Fin 2 → ℤ) : Matrix (ν × BlockBivariateMonomialIndex y F) ι ℤ :=
  fun a j => if a.1 = cls j then
    (x j 0 - y a.1 0) ^ a.2.val 0 * (x j 1 - y a.1 1) ^ a.2.val 1 else 0

/-- Exact block factorization of an arbitrary class-dependent family. -/
theorem blockBivariateEvaluation_factorization
    {ι ν : Type*} [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν]
    (cls : ι → ν) (y : ν → Fin 2 → ℤ)
    (F : ν → ι → MvPolynomial (Fin 2) ℤ) (x : ι → Fin 2 → ℤ) :
    Matrix.of (fun i j => MvPolynomial.eval (x j) (F (cls j) i)) =
      blockBivariateCoefficientMatrix y F * blockBivariateMonomialMatrix cls y F x := by
  classical
  ext i j
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [blockBivariateCoefficientMatrix, blockBivariateMonomialMatrix,
    mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  let z : Fin 2 → ℤ := fun q => x j q - y (cls j) q
  have hp : (fun q => y (cls j) q + z q) = x j := by funext q; simp [z]
  change MvPolynomial.eval (x j) (F (cls j) i) = _
  rw [← hp, ← eval_translateBivariatePolynomial, MvPolynomial.eval_eq']
  simp only [Fin.prod_univ_two, add_sub_cancel_left]
  change (∑ d ∈ (translateBivariatePolynomial (y (cls j)) (F (cls j) i)).support,
      coeff d (translateBivariatePolynomial (y (cls j)) (F (cls j) i)) *
        ((x j 0 - y (cls j) 0) ^ d 0 * (x j 1 - y (cls j) 1) ^ d 1)) =
    ∑ d : BlockBivariateMonomialIndex y F,
      coeff d.val (translateBivariatePolynomial (y (cls j)) (F (cls j) i)) *
        ((x j 0 - y (cls j) 0) ^ d.val 0 * (x j 1 - y (cls j) 1) ^ d.val 1)
  rw [← Finset.sum_subtype (blockBivariateCommonSupport y F) (fun _ => Iff.rfl)
    (fun d => coeff d (translateBivariatePolynomial (y (cls j)) (F (cls j) i)) *
      ((x j 0 - y (cls j) 0) ^ d 0 * (x j 1 - y (cls j) 1) ^ d 1))]
  apply Finset.sum_subset (blockBivariate_support_subset y F _ _)
  intro d _ hd
  rw [MvPolynomial.notMem_support_iff.mp hd, zero_mul]

/-- All residue classes contribute simultaneously, with the exponent
determined internally by their respective numbers of columns. -/
theorem blockBivariatePolynomialEvaluation_det_dvd
    {ι ν : Type*} [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν]
    (p : ℤ) (cls : ι → ν) (y : ν → Fin 2 → ℤ)
    (F : ν → ι → MvPolynomial (Fin 2) ℤ) (x : ι → Fin 2 → ℤ)
    (hx : ∀ j i, p ∣ x j i - y (cls j) i) :
    p ^ (∑ c, smoothSurfaceJetExponent (Fintype.card {j // cls j = c})) ∣
      (Matrix.of (fun i j => MvPolynomial.eval (x j) (F (cls j) i))).det := by
  classical
  rw [blockBivariateEvaluation_factorization]
  apply pow_dvd_det_rectangular_mul_of_bivariate_blocks
    (blockBivariateCoefficientMatrix y F) (blockBivariateMonomialMatrix cls y F x)
    p cls Prod.fst (fun a => (a.2.val 0, a.2.val 1))
  · intro c a ha b hb hab
    apply Prod.ext (ha.trans hb.symm)
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    fin_cases i
    · exact congrArg Prod.fst hab
    · exact congrArg Prod.snd hab
  · intro a j
    dsimp [blockBivariateMonomialMatrix]
    split_ifs with h
    · rw [h, pow_add]
      exact mul_dvd_mul (pow_dvd_pow_of_dvd (hx j 0) _)
        (pow_dvd_pow_of_dvd (hx j 1) _)
    · exact dvd_zero _
  · intro a j h
    by_contra hn
    exact h (by simp [blockBivariateMonomialMatrix, hn])

end
end TranslatedDepthSeven
