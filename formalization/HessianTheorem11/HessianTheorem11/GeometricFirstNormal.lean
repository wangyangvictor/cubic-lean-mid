import HessianTheorem11.FirstNormalSieve
import HessianTheorem11.BasisHessianTransport
import HessianTheorem11.GeometricFactorization

/-! Construction of the first-normal sieve for the actual function-field
Hessian rank. All local coordinates, polynomial identities, multiplicities,
and normal ranks are constructed. The explicit inputs are universal
textbook generic-rank, tangent-space, and simple-root theorems. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial LocalCubicNormalForm CubicNormalFormConstruction

/-- The actual first-normal sieve at any good divisor point and any
constructed hyperbolic basis. Its normal-rank field is the actual quadratic
Hessian in that basis. -/
def firstNormalSieveAt
    (DT : SymmetricDeterminantalTangentInput)
    (FI : FormalImplicitFunctionInput GeometricField)
    {n m q : ℕ} (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (hirred : Irreducible F) (P : CubicDivisorPoint F)
    (S : HyperbolicBasis.Splitting (hessianBilinear F P.point) P.point m q) :
    FirstNormalSieve n (geometricCubicGenericRank F) := by
  classical
  let D := data hF S
  let B := coordinateMatrix S
  have hB : B = BasisHessianTransport.basisMatrix S.basis := rfl
  have hnormal : PolynomialRestriction.restrict B F = polynomial D :=
    restrict_eq_polynomial_of_geometric_generic_rank DT hF hirred P.on_cubic S P.maximal_rank
  have hlocalIrred : Irreducible (polynomial D) := by
    rw [← hnormal, hB]
    exact BasisHessianTransport.restrict_irreducible S.basis F hirred
  have hB0 : (quadraticMatrix D.Q0).det ≠ 0 := Q0_det_ne_zero hF S
  have hdims := S.hessian_rank_dimensions
  have hdim : m + geometricCubicGenericRank F = n := by
    have h := hdims.1
    rwa [P.rank_eq] at h
  have hq : q + 2 = geometricCubicGenericRank F := by rw [← P.rank_eq]; exact hdims.2
  have hlocalRank : ∀ y : Coordinate m q → GeometricField, eval y (polynomial D) = 0 →
      ((polynomialHessian D).map (eval y)).rank ≤ q + 2 := by
    intro y hy
    have hyF : eval (B.mulVec y) F = 0 := by
      rw [← PolynomialRestriction.eval_restrict B F y, hnormal]
      exact hy
    have ht := BasisHessianTransport.hessian_rank_restrict S.basis F y
    change Matrix.rank (fun i j => eval y (pderiv j (pderiv i
      (PolynomialRestriction.restrict B F)))) = (hessian F (B.mulVec y)).rank at ht
    rw [hnormal] at ht
    change Matrix.rank (fun i j => eval y (pderiv j (pderiv i (polynomial D)))) ≤ q + 2
    rw [ht, hq, ← P.rank_eq]
    exact P.maximal_rank (B.mulVec y) hyF
  let hcex := BasisHessianTransport.hessian_determinant_restrict S.basis F
  let c := Classical.choose hcex
  have hc := (Classical.choose_spec hcex).1
  have hcDet := (Classical.choose_spec hcex).2
  let G := C c * PolynomialRestriction.restrict B P.residual
  have hG : eval (basePoint m q) G ≠ 0 := by
    change eval (basePoint m q) (C c * PolynomialRestriction.restrict B P.residual) ≠ 0
    rw [map_mul, eval_C, PolynomialRestriction.eval_restrict]
    have hbase : B.mulVec (basePoint m q) = P.point := coordinateMatrix_basePoint S
    rw [hbase]
    exact mul_ne_zero hc P.residual_nonzero
  have hdetLocal : (polynomialHessian D).det = polynomial D ^ P.multiplicity * G := by
    change Matrix.det (fun i j => pderiv j (pderiv i (PolynomialRestriction.restrict B F))) =
      C c * PolynomialRestriction.restrict B (hessianDeterminantPolynomial F) at hcDet
    rw [hnormal, P.determinant_factorization] at hcDet
    have hf : PolynomialRestriction.restrict B (F ^ P.multiplicity * P.residual) =
      polynomial D ^ P.multiplicity * PolynomialRestriction.restrict B P.residual := by
      rw [show PolynomialRestriction.restrict B (F ^ P.multiplicity * P.residual) =
        PolynomialRestriction.restrict B F ^ P.multiplicity *
          PolynomialRestriction.restrict B P.residual by
            simp only [PolynomialRestriction.restrict, map_mul, map_pow], hnormal]
    rw [hf] at hcDet
    change Matrix.det (fun i j => pderiv j (pderiv i (polynomial D))) = _
    rw [hcDet]
    dsimp [G]
    ring
  refine FirstNormalSieve.of_local_cubic FI D hlocalIrred hB0 hlocalRank G hG hdetLocal
    hdim hq ?_ P.degree_bound
  have hm : m = n - geometricCubicGenericRank F := by omega
  rw [hm]
  exact P.corank_bound

@[simp] theorem firstNormalSieveAt_normalRank
    (DT : SymmetricDeterminantalTangentInput)
    (FI : FormalImplicitFunctionInput GeometricField)
    {n m q : ℕ} (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (hirred : Irreducible F) (P : CubicDivisorPoint F)
    (S : HyperbolicBasis.Splitting (hessianBilinear F P.point) P.point m q) :
    (firstNormalSieveAt DT FI F hF hirred P S).normalRank =
      (quadraticMatrix (data hF S).QA).rank := rfl

/-- Source Proposition 11.1 in the portion needed for n=11,12,13. -/
theorem exists_firstNormalSieve
    (AG : GenericMatrixRankInput) (DT : SymmetricDeterminantalTangentInput)
    (FI : FormalImplicitFunctionInput GeometricField)
    {n : ℕ} (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (hirred : Irreducible F) (hdet : hessianDeterminantPolynomial F ≠ 0) :
    Nonempty (FirstNormalSieve n (geometricCubicGenericRank F)) := by
  obtain ⟨P⟩ := exists_cubicDivisorPoint AG F hF hirred hdet
  obtain ⟨m, q, ⟨S⟩⟩ := exists_cubic_hyperbolic_splitting F hF P.point P.on_cubic P.smooth
  exact ⟨firstNormalSieveAt DT FI F hF hirred P S⟩

/-- The twelve-variable rank bound is geometric: absolute irreducibility
and a nonzero Hessian determinant suffice. -/
theorem geometric_rank_twelve
    (AG : GenericMatrixRankInput) (DT : SymmetricDeterminantalTangentInput)
    (FI : FormalImplicitFunctionInput GeometricField)
    (F : GeometricPolynomial 12) (hF : F.IsHomogeneous 3)
    (hirred : Irreducible F) (hdet : hessianDeterminantPolynomial F ≠ 0) :
    10 ≤ geometricCubicGenericRank F := by
  obtain ⟨S⟩ := exists_firstNormalSieve AG DT FI F hF hirred hdet
  exact S.rank_twelve

theorem geometric_rank_thirteen
    (AG : GenericMatrixRankInput) (DT : SymmetricDeterminantalTangentInput)
    (FI : FormalImplicitFunctionInput GeometricField)
    (F : GeometricPolynomial 13) (hF : F.IsHomogeneous 3)
    (hirred : Irreducible F) (hdet : hessianDeterminantPolynomial F ≠ 0) :
    10 ≤ geometricCubicGenericRank F := by
  obtain ⟨S⟩ := exists_firstNormalSieve AG DT FI F hF hirred hdet
  exact S.rank_thirteen

end HessianTheorem11
