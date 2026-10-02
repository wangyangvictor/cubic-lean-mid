import HessianTheorem11.HessianMultiplicity
import HessianTheorem11.SmoothCubicPoint

/-! A smooth maximal-rank point avoiding the residual Hessian divisor,
constructed for any irreducible geometric cubic with nonzero determinant.
No rationality or anisotropy is needed in this geometric step. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial

def geometricCubicGenericRank {n : ℕ} (F : GeometricPolynomial n) : ℕ :=
  genericMatrixRank (Ideal.span {F}) (hessianPolynomial F)

structure CubicDivisorPoint {n : ℕ} (F : GeometricPolynomial n) where
  multiplicity : ℕ
  residual : GeometricPolynomial n
  determinant_factorization : hessianDeterminantPolynomial F = F ^ multiplicity * residual
  degree_bound : 3 * multiplicity ≤ n
  corank_bound : n - geometricCubicGenericRank F ≤ multiplicity
  point : GeometricPoint n
  on_cubic : eval point F = 0
  smooth : gradient F point ≠ 0
  nonzero : point ≠ 0
  rank_eq : (hessian F point).rank = geometricCubicGenericRank F
  residual_nonzero : eval point residual ≠ 0
  maximal_rank : ∀ y, eval y F = 0 → (hessian F y).rank ≤ (hessian F point).rank

theorem exists_cubicDivisorPoint
    (AG : GenericMatrixRankInput) {n : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous 3) (hirred : Irreducible F)
    (hdet : hessianDeterminantPolynomial F ≠ 0) : Nonempty (CubicDivisorPoint F) := by
  let I : Ideal (GeometricPolynomial n) := Ideal.span {F}
  letI : I.IsPrime := (Ideal.span_singleton_prime hirred.ne_zero).mpr hirred.prime
  have hfinite : FiniteMultiplicity F (hessianDeterminantPolynomial F) :=
    finiteMultiplicity_of_positive_homogeneous_divisor hF (by norm_num) hirred.ne_zero hdet
  obtain ⟨D, hD, hnot⟩ := hfinite.exists_eq_pow_mul_and_not_dvd
  obtain ⟨x, hx, hg, hx0, hr, hDx⟩ :=
    exists_smooth_cubic_point_avoiding_polynomial AG F hF hirred D hnot
  have hpow : F ^ (n - geometricCubicGenericRank F) ∣ hessianDeterminantPolynomial F := by
    have hp := prime_pow_generic_corank_dvd_det F hirred.prime (hessianPolynomial F)
    simpa only [Fintype.card_fin, geometricCubicGenericRank, genericMatrixRank,
      genericMatrix, genericPointMap, hessianDeterminantPolynomial] using hp
  have hdegree : 3 * multiplicity F (hessianDeterminantPolynomial F) ≤ n :=
    homogeneous_pow_degree_le_of_dvd hF hirred.ne_zero hdet
      (hessianDeterminantPolynomial_totalDegree_le hF) (pow_multiplicity_dvd _ _)
  refine ⟨{
    multiplicity := multiplicity F (hessianDeterminantPolynomial F)
    residual := D
    determinant_factorization := hD
    degree_bound := hdegree
    corank_bound := hfinite.le_multiplicity_of_pow_dvd hpow
    point := x
    on_cubic := hx
    smooth := hg
    nonzero := hx0
    rank_eq := hr
    residual_nonzero := hDx
    maximal_rank := ?_
  }⟩
  intro y hy
  rw [hr]
  apply AG.specialization_le I (hessianPolynomial F) y
  apply mem_zeroLocus_iff.mpr
  intro p hp
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.mp hp
  simp [hy]

theorem geometricCubicGenericRank_geometricPolynomial
    (AG : GenericMatrixRankInput) {n : ℕ} (F : RationalPolynomial n)
    (hF : Irreducible (geometricPolynomial F)) :
    geometricCubicGenericRank (geometricPolynomial F) = genericHessianRank F := by
  rw [genericHessianRank_eq_genericPointHessianRank AG F hF]
  rfl

end HessianTheorem11
