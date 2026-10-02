import HessianTheorem11.Geometry
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! The relation between the maximum of ranks at geometric points and the
actual matrix rank at the generic point. The universal external input is only
the usual open-minor theorem for an arbitrary polynomial matrix on an arbitrary
integral affine variety. Nullstellensatz and the supremum bridge are proved
using mathlib. No cubic rank lower bound is assumed. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial

abbrev affineCoordinateRing {σ : Type*}
    (I : Ideal (MvPolynomial σ GeometricField)) := MvPolynomial σ GeometricField ⧸ I

abbrev affineFunctionField {σ : Type*}
    (I : Ideal (MvPolynomial σ GeometricField)) := FractionRing (affineCoordinateRing I)

/-- Polynomial functions evaluated in the fraction ring of their coordinate
ring. When `I` is prime this is the actual function field of the variety. -/
def genericPointMap {σ : Type*} (I : Ideal (MvPolynomial σ GeometricField)) :
    MvPolynomial σ GeometricField →+* affineFunctionField I :=
  (algebraMap (affineCoordinateRing I) (affineFunctionField I)).comp (Ideal.Quotient.mk I)

def genericMatrix {σ : Type*} {a b : ℕ}
    (I : Ideal (MvPolynomial σ GeometricField))
    (M : Matrix (Fin a) (Fin b) (MvPolynomial σ GeometricField)) :
    Matrix (Fin a) (Fin b) (affineFunctionField I) := M.map (genericPointMap I)

def genericMatrixRank {σ : Type*} {a b : ℕ}
    (I : Ideal (MvPolynomial σ GeometricField))
    (M : Matrix (Fin a) (Fin b) (MvPolynomial σ GeometricField)) : ℕ :=
  (genericMatrix I M).rank

def evaluatedMatrix {σ : Type*} {a b : ℕ}
    (M : Matrix (Fin a) (Fin b) (MvPolynomial σ GeometricField))
    (x : σ → GeometricField) : Matrix (Fin a) (Fin b) GeometricField :=
  M.map (eval x)

/-- Standard open-minor theorem for arbitrary polynomial matrices on integral
affine varieties: specialization cannot increase generic rank, and the rank is
generic on a principal open specified by a polynomial outside the prime ideal.
The row count, column count, and affine variable type are independent. -/
structure GenericMatrixRankInput : Prop where
  specialization_le : ∀ {σ : Type} [Fintype σ] {a b : ℕ}
    (I : Ideal (MvPolynomial σ GeometricField)) [I.IsPrime]
    (M : Matrix (Fin a) (Fin b) (MvPolynomial σ GeometricField)),
    ∀ x ∈ zeroLocus GeometricField I,
      (evaluatedMatrix M x).rank ≤ genericMatrixRank I M
  principal_open : ∀ {σ : Type} [Fintype σ] {a b : ℕ}
    (I : Ideal (MvPolynomial σ GeometricField)) [I.IsPrime]
    (M : Matrix (Fin a) (Fin b) (MvPolynomial σ GeometricField)),
    ∃ q : MvPolynomial σ GeometricField, q ∉ I ∧
      ∀ x ∈ zeroLocus GeometricField I, eval x q ≠ 0 →
        (evaluatedMatrix M x).rank = genericMatrixRank I M

/-- Nullstellensatz guarantees an actual geometric point in each nonempty
principal open of an integral affine variety. -/
theorem exists_zeroLocus_eval_ne_zero {σ : Type*} [Fintype σ]
    (I : Ideal (MvPolynomial σ GeometricField)) [I.IsPrime]
    (q : MvPolynomial σ GeometricField) (hq : q ∉ I) :
    ∃ x ∈ zeroLocus GeometricField I, eval x q ≠ 0 := by
  by_contra h
  push_neg at h
  have hm : q ∈ vanishingIdeal GeometricField (zeroLocus GeometricField I) := h
  rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus] at hm
  exact hq hm

theorem genericMatrixRank_attained
    (AG : GenericMatrixRankInput) {σ : Type} [Fintype σ] {a b : ℕ}
    (I : Ideal (MvPolynomial σ GeometricField)) [I.IsPrime]
    (M : Matrix (Fin a) (Fin b) (MvPolynomial σ GeometricField)) :
    ∃ x ∈ zeroLocus GeometricField I,
      (evaluatedMatrix M x).rank = genericMatrixRank I M := by
  obtain ⟨q, hq, hopen⟩ := AG.principal_open I M
  obtain ⟨x, hx, hqx⟩ := exists_zeroLocus_eval_ne_zero I q hq
  exact ⟨x, hx, hopen x hx hqx⟩

def geometricMatrixRanks {σ : Type*} {a b : ℕ}
    (I : Ideal (MvPolynomial σ GeometricField))
    (M : Matrix (Fin a) (Fin b) (MvPolynomial σ GeometricField)) : Set ℕ :=
  {r | ∃ x ∈ zeroLocus GeometricField I, (evaluatedMatrix M x).rank = r}

theorem geometricMatrixRanks_bddAbove {σ : Type*} {a b : ℕ}
    (I : Ideal (MvPolynomial σ GeometricField))
    (M : Matrix (Fin a) (Fin b) (MvPolynomial σ GeometricField)) :
    BddAbove (geometricMatrixRanks I M) := by
  refine ⟨b, ?_⟩
  rintro r ⟨x, _, rfl⟩
  exact Matrix.rank_le_width (A := evaluatedMatrix M x)

/-- The function-field matrix rank is exactly the maximum of the actual
geometric-point ranks. This equality does not identify different invariants by
definition: its attainment step uses Nullstellensatz on the supplied open. -/
theorem genericMatrixRank_eq_sSup
    (AG : GenericMatrixRankInput) {σ : Type} [Fintype σ] {a b : ℕ}
    (I : Ideal (MvPolynomial σ GeometricField)) [I.IsPrime]
    (M : Matrix (Fin a) (Fin b) (MvPolynomial σ GeometricField)) :
    genericMatrixRank I M = sSup (geometricMatrixRanks I M) := by
  apply le_antisymm
  · apply le_csSup (geometricMatrixRanks_bddAbove I M)
    exact genericMatrixRank_attained AG I M
  · apply csSup_le'
    rintro r ⟨x, hx, rfl⟩
    exact AG.specialization_le I M x hx

def cubicCoordinateIdeal {n : ℕ} (F : RationalPolynomial n) :
    Ideal (GeometricPolynomial n) := Ideal.span {geometricPolynomial F}

abbrev cubicCoordinateRing {n : ℕ} (F : RationalPolynomial n) :=
  affineCoordinateRing (cubicCoordinateIdeal F)

abbrev cubicFunctionField {n : ℕ} (F : RationalPolynomial n) :=
  affineFunctionField (cubicCoordinateIdeal F)

theorem cubicCoordinateIdeal_isPrime {n : ℕ} (F : RationalPolynomial n)
    (hF : Irreducible (geometricPolynomial F)) : (cubicCoordinateIdeal F).IsPrime := by
  exact (Ideal.span_singleton_prime hF.ne_zero).mpr hF.prime

theorem cubicCoordinateRing_isDomain {n : ℕ} (F : RationalPolynomial n)
    (hF : Irreducible (geometricPolynomial F)) : IsDomain (cubicCoordinateRing F) := by
  letI := cubicCoordinateIdeal_isPrime F hF
  infer_instance

theorem zeroLocus_cubicCoordinateIdeal {n : ℕ} (F : RationalPolynomial n) :
    zeroLocus GeometricField (cubicCoordinateIdeal F) = cubicLocus F := by
  rw [cubicCoordinateIdeal, zeroLocus_span]
  ext x
  simp [cubicLocus]

theorem vanishingIdeal_cubicLocus_eq {n : ℕ} (F : RationalPolynomial n)
    (hF : Irreducible (geometricPolynomial F)) :
    vanishingIdeal GeometricField (cubicLocus F) = cubicCoordinateIdeal F := by
  letI := cubicCoordinateIdeal_isPrime F hF
  rw [← zeroLocus_cubicCoordinateIdeal]
  exact MvPolynomial.IsPrime.vanishingIdeal_zeroLocus _

/-- The Hessian matrix evaluated at the generic point of the geometric cubic,
with entries in the fraction ring of its actual homogeneous coordinate ring. -/
def genericPointHessian {n : ℕ} (F : RationalPolynomial n) :
    Matrix (Fin n) (Fin n) (cubicFunctionField F) :=
  genericMatrix (cubicCoordinateIdeal F) (hessianPolynomial (geometricPolynomial F))

def genericPointHessianRank {n : ℕ} (F : RationalPolynomial n) : ℕ :=
  (genericPointHessian F).rank

theorem genericHessianRank_eq_genericPointHessianRank
    (AG : GenericMatrixRankInput) {n : ℕ} (F : RationalPolynomial n)
    (hF : Irreducible (geometricPolynomial F)) :
    genericHessianRank F = genericPointHessianRank F := by
  letI := cubicCoordinateIdeal_isPrime F hF
  have hr := genericMatrixRank_eq_sSup AG (cubicCoordinateIdeal F)
    (hessianPolynomial (geometricPolynomial F))
  calc
    genericHessianRank F = sSup (geometricMatrixRanks (cubicCoordinateIdeal F)
        (hessianPolynomial (geometricPolynomial F))) := by
      unfold genericHessianRank
      congr 1
      unfold geometricMatrixRanks onCubicRanks
      rw [zeroLocus_cubicCoordinateIdeal]
      rfl
    _ = genericPointHessianRank F := hr.symm

end HessianTheorem11
