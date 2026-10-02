import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Nat.Lattice
import Mathlib.Tactic

/-!+# Concrete objects for Theorem 1.1

All loci are defined from the actual polynomial and its formal partial derivatives.
Dimension is the Krull dimension of the reduced geometric coordinate ring.
The rank is the supremum of ranks at geometric points of the cubic. For an
irreducible cubic this is its generic rank, by openness of a nonzero minor.
The proof that a rational anisotropic cubic in these dimensions is absolutely
irreducible remains a separate obligation; it is not included in the definition.
-/

noncomputable section

namespace HessianTheorem11

open MvPolynomial

abbrev GeometricField := AlgebraicClosure ℚ
abbrev RationalPolynomial (n : ℕ) := MvPolynomial (Fin n) ℚ
abbrev GeometricPolynomial (n : ℕ) := MvPolynomial (Fin n) GeometricField
abbrev GeometricPoint (n : ℕ) := Fin n → GeometricField
abbrev Dimension := WithBot ℕ∞

def Anisotropic {n : ℕ} (F : RationalPolynomial n) : Prop :=
  ∀ v : Fin n → ℚ, eval v F = 0 → v = 0

structure AnisotropicCubic (n : ℕ) where
  polynomial : RationalPolynomial n
  homogeneous : polynomial.IsHomogeneous 3
  anisotropic : Anisotropic polynomial

def geometricPolynomial {n : ℕ} (F : RationalPolynomial n) : GeometricPolynomial n :=
  map (algebraMap ℚ GeometricField) F

def gradient {K : Type*} [CommSemiring K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (x : Fin n → K) : Fin n → K :=
  fun i => eval x (pderiv i F)

def hessianPolynomial {K : Type*} [CommSemiring K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) K) :=
  fun i j => pderiv j (pderiv i F)

def hessian {K : Type*} [CommSemiring K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (x : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  fun i j => eval x (hessianPolynomial F i j)

def cubicLocus {n : ℕ} (F : RationalPolynomial n) : Set (GeometricPoint n) :=
  {x | eval x (geometricPolynomial F) = 0}

def singularLocus {n : ℕ} (F : RationalPolynomial n) : Set (GeometricPoint n) :=
  {x | gradient (geometricPolynomial F) x = 0}

def rankAtMostLocus {n : ℕ} (F : RationalPolynomial n) (r : ℕ) : Set (GeometricPoint n) :=
  {x | (hessian (geometricPolynomial F) x).rank ≤ r}

def exactRankLocus {n : ℕ} (F : RationalPolynomial n) (r : ℕ) : Set (GeometricPoint n) :=
  {x | (hessian (geometricPolynomial F) x).rank = r}

/-- Both affine vector variables are retained. No projectivization is made. -/
def incidenceLocus {n : ℕ} (F : RationalPolynomial n) :
    Set ((Fin n ⊕ Fin n) → GeometricField) :=
  {p | (hessian (geometricPolynomial F) (p ∘ Sum.inl)).mulVec (p ∘ Sum.inr) = 0}

/-- The vanishing ideal makes the coordinate ring reduced by construction.
For the empty set mathlib uses `⊥` rather than the paper's integer `-1`.
All nine targets are upper bounds on nonempty loci, so this distinction does
not change any target. No finite dimension is silently coerced to a natural. -/
def affineDimension {σ : Type*} (Z : Set (σ → GeometricField)) : Dimension :=
  ringKrullDim (MvPolynomial σ GeometricField ⧸ vanishingIdeal GeometricField Z)

def incidenceDimension {n : ℕ} (F : RationalPolynomial n) : Dimension :=
  affineDimension (incidenceLocus F)

def singularDimension {n : ℕ} (F : RationalPolynomial n) : Dimension :=
  affineDimension (singularLocus F)

def onCubicRanks {n : ℕ} (F : RationalPolynomial n) : Set ℕ :=
  {r | ∃ x ∈ cubicLocus F, (hessian (geometricPolynomial F) x).rank = r}

def genericHessianRank {n : ℕ} (F : RationalPolynomial n) : ℕ :=
  sSup (onCubicRanks F)

theorem onCubicRanks_bddAbove {n : ℕ} (F : RationalPolynomial n) :
    BddAbove (onCubicRanks F) := by
  refine ⟨n, ?_⟩
  rintro r ⟨x, _, rfl⟩
  exact Matrix.rank_le_width (A := hessian (geometricPolynomial F) x)

theorem rank_le_genericHessianRank {n : ℕ} (F : RationalPolynomial n)
    {x : GeometricPoint n} (hx : x ∈ cubicLocus F) :
    (hessian (geometricPolynomial F) x).rank ≤ genericHessianRank F :=
  le_csSup (onCubicRanks_bddAbove F) ⟨x, hx, rfl⟩

theorem genericHessianRank_le {n : ℕ} (F : RationalPolynomial n) :
    genericHessianRank F ≤ n := by
  apply csSup_le'
  rintro r ⟨x, _, rfl⟩
  exact Matrix.rank_le_width (A := hessian (geometricPolynomial F) x)

theorem incidence_contains_zero_right {n : ℕ} (F : RationalPolynomial n)
    (x : GeometricPoint n) : Sum.elim x 0 ∈ incidenceLocus F := by
  change (hessian (geometricPolynomial F) x).mulVec 0 = 0
  exact Matrix.mulVec_zero _

theorem geometric_homogeneous {n : ℕ} {F : RationalPolynomial n}
    (hF : F.IsHomogeneous 3) : (geometricPolynomial F).IsHomogeneous 3 := by
  exact hF.map _

theorem anisotropic_polynomial_ne_zero {n : ℕ} (hn : 0 < n)
    (F : AnisotropicCubic n) : F.polynomial ≠ 0 := by
  intro hz
  have he := F.anisotropic (fun _ => 1) (by simp [hz])
  have hi := congrFun he ⟨0, hn⟩
  norm_num at hi

theorem anisotropic_eval_ne_zero {n : ℕ} {F : RationalPolynomial n}
    (hF : Anisotropic F) {v : Fin n → ℚ} (hv : v ≠ 0) : eval v F ≠ 0 :=
  fun h => hv (hF v h)

end HessianTheorem11
