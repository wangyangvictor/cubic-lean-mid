import HessianTheorem11.CubicIrreducibility
import HessianTheorem11.GeometricFactorization
import HessianTheorem11.GenericRankBridge
import HessianTheorem11.BasicLoci
import HessianTheorem11.SingularLinearAlgebra
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex

/-!
Actual smooth, maximum-Hessian-rank points on an irreducible geometric cubic,
avoiding any prescribed polynomial not divisible by the cubic. The construction
intersects principal opens and uses mathlib's Nullstellensatz. The tangent
space of the hypersurface is also identified with the actual differential
kernel by differentiating its principal vanishing ideal.
-/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Module

section Partial
variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

theorem exists_nonzero_partial_of_cubic
    {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0) :
    ∃ i, pderiv i F ≠ 0 := by
  by_contra h
  push_neg at h
  have he := hF.sum_X_mul_pderiv.symm
  have hz : (3 : MvPolynomial (Fin n) K) * F = 0 := by
    simpa [h, nsmul_eq_mul] using he
  exact hF0 ((mul_eq_zero.mp hz).resolve_left (by norm_num))

omit [CharZero K] in
theorem cubic_not_dvd_nonzero_partial
    {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    (i : Fin n) (hi : pderiv i F ≠ 0) : ¬ F ∣ pderiv i F := by
  intro hdiv
  have hdegF : F.totalDegree = 3 := hF.totalDegree hF0
  have hdegP : (pderiv i F).totalDegree = 2 := hF.pderiv.totalDegree hi
  have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hi
  omega

end Partial

/-- A principal open on the irreducible cubic meets the smooth maximum-rank
locus. The generic rank here is the actual function-field matrix rank. -/
theorem exists_smooth_cubic_point_avoiding_polynomial
    (AG : GenericMatrixRankInput) {n : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous 3) (hirred : Irreducible F)
    (D : GeometricPolynomial n) (hD : ¬ F ∣ D) :
    ∃ x : GeometricPoint n,
      eval x F = 0 ∧ gradient F x ≠ 0 ∧ x ≠ 0 ∧
      (hessian F x).rank = genericMatrixRank (Ideal.span {F}) (hessianPolynomial F) ∧
      eval x D ≠ 0 := by
  let I : Ideal (GeometricPolynomial n) := Ideal.span {F}
  have hI : I.IsPrime := (Ideal.span_singleton_prime hirred.ne_zero).mpr hirred.prime
  letI : I.IsPrime := hI
  obtain ⟨q, hq, hgeneric⟩ := AG.principal_open I (hessianPolynomial F)
  obtain ⟨i, hi⟩ := exists_nonzero_partial_of_cubic hF hirred.ne_zero
  have hpi : pderiv i F ∉ I := by
    intro hmem
    exact cubic_not_dvd_nonzero_partial hF hirred.ne_zero i hi
      (Ideal.mem_span_singleton.mp hmem)
  have hDI : D ∉ I := fun hmem => hD (Ideal.mem_span_singleton.mp hmem)
  have hprod : q * pderiv i F * D ∉ I := by
    intro hm
    rcases hI.mem_or_mem hm with hp | hd
    · exact ((hI.mem_or_mem hp).elim hq hpi)
    · exact hDI hd
  obtain ⟨x, hx, hnonzero⟩ := exists_zeroLocus_eval_ne_zero I _ hprod
  have hvalues : eval x q ≠ 0 ∧ eval x (pderiv i F) ≠ 0 ∧ eval x D ≠ 0 := by
    simp only [map_mul, mul_ne_zero_iff] at hnonzero
    exact ⟨hnonzero.1.1, hnonzero.1.2, hnonzero.2⟩
  have hxF : eval x F = 0 := hx F (Ideal.mem_span_singleton_self F)
  have hxgradient : gradient F x ≠ 0 := by
    intro hz
    exact hvalues.2.1 (congrFun hz i)
  have hx0 : x ≠ 0 := by
    intro hz
    apply hxgradient
    subst x
    ext j
    exact eval_origin_of_positive_homogeneous hF.pderiv (by norm_num)
  refine ⟨x, hxF, hxgradient, hx0, ?_, hvalues.2.2⟩
  exact hgeneric x hx hvalues.1

/-- The same chosen point, stated with the rank convention of Theorem 1.1. -/
theorem exists_smooth_onCubic_generic_rank_avoiding_polynomial
    (AG : GenericMatrixRankInput) {n : ℕ} (F : RationalPolynomial n)
    (hF : F.IsHomogeneous 3) (hirred : Irreducible (geometricPolynomial F))
    (D : GeometricPolynomial n) (hD : ¬ geometricPolynomial F ∣ D) :
    ∃ x : GeometricPoint n,
      x ∈ cubicLocus F ∧ gradient (geometricPolynomial F) x ≠ 0 ∧ x ≠ 0 ∧
      (hessian (geometricPolynomial F) x).rank = genericHessianRank F ∧ eval x D ≠ 0 := by
  obtain ⟨x, hx, hgrad, hne, hrank, hD⟩ := exists_smooth_cubic_point_avoiding_polynomial
    AG (geometricPolynomial F) (geometric_homogeneous hF) hirred D hD
  refine ⟨x, hx, hgrad, hne, ?_, hD⟩
  rw [genericHessianRank_eq_genericPointHessianRank AG F hirred]
  exact hrank

/-- Source point selection using the internal proved absolute-irreducibility
lemma; public aggregates supply `CI` from geometric semistability. -/
theorem anisotropic_exists_smooth_onCubic_generic_rank_avoiding_polynomial
    (CI : CubicGeometricIrreducibility) (DT : DeterminantalTangentOver ℚ)
    (AG : GenericMatrixRankInput) {n : ℕ} (F : AnisotropicCubic n) (hn : 4 ≤ n)
    (D : GeometricPolynomial n) (hD : ¬ geometricPolynomial F.polynomial ∣ D) :
    ∃ x : GeometricPoint n,
      x ∈ cubicLocus F.polynomial ∧ gradient (geometricPolynomial F.polynomial) x ≠ 0 ∧
      x ≠ 0 ∧ (hessian (geometricPolynomial F.polynomial) x).rank =
        genericHessianRank F.polynomial ∧ eval x D ≠ 0 :=
  exists_smooth_onCubic_generic_rank_avoiding_polynomial AG F.polynomial F.homogeneous
    (CI F hn) D hD

section Tangent
variable {K : Type*} [Field K] {n : ℕ}

/-- The ordinary product rule for the actual polynomial differential. -/
theorem polynomialDifferential_mul_apply
    (F G : MvPolynomial (Fin n) K) (x t : Fin n → K) :
    polynomialDifferential (F * G) x t =
      eval x G * polynomialDifferential F x t +
        eval x F * polynomialDifferential G x t := by
  simp only [polynomialDifferential_apply, Derivation.leibniz, smul_eq_mul,
    map_add, map_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  rw [add_comm]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

end Tangent

/-- The embedded tangent space of an irreducible hypersurface at a point
on it is the kernel of its defining equation's differential. No smoothness
hypothesis is necessary for this equality. -/
theorem affineTangentSpace_irreducible_hypersurface_eq_ker
    {n : ℕ} (F : GeometricPolynomial n) (hirred : Irreducible F)
    (x : GeometricPoint n) (hx : eval x F = 0) :
    affineTangentSpace (zeroLocus GeometricField (Ideal.span {F})) x =
      LinearMap.ker (polynomialDifferential F x) := by
  let I : Ideal (GeometricPolynomial n) := Ideal.span {F}
  letI : I.IsPrime := (Ideal.span_singleton_prime hirred.ne_zero).mpr hirred.prime
  have hvan : vanishingIdeal GeometricField (zeroLocus GeometricField I) = I :=
    MvPolynomial.IsPrime.vanishingIdeal_zeroLocus I
  apply le_antisymm
  · intro t ht
    apply LinearMap.mem_ker.mpr
    apply mem_affineTangentSpace.mp ht F
    change F ∈ vanishingIdeal GeometricField (zeroLocus GeometricField I)
    rw [hvan]
    exact Ideal.mem_span_singleton_self F
  · intro t ht
    apply mem_affineTangentSpace.mpr
    intro p hp
    change p ∈ vanishingIdeal GeometricField (zeroLocus GeometricField I) at hp
    rw [hvan] at hp
    obtain ⟨G, hG⟩ := Ideal.mem_span_singleton.mp hp
    rw [hG, polynomialDifferential_mul_apply, hx]
    have ht0 : polynomialDifferential F x t = 0 := ht
    rw [ht0]
    ring

theorem affineTangentSpace_cubicLocus_eq_ker
    {n : ℕ} (F : RationalPolynomial n)
    (hirred : Irreducible (geometricPolynomial F))
    (x : GeometricPoint n) (hx : x ∈ cubicLocus F) :
    affineTangentSpace (cubicLocus F) x =
      LinearMap.ker (polynomialDifferential (geometricPolynomial F) x) := by
  rw [← zeroLocus_cubicCoordinateIdeal]
  exact affineTangentSpace_irreducible_hypersurface_eq_ker (geometricPolynomial F) hirred x hx

end HessianTheorem11
