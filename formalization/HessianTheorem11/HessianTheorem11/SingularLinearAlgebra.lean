import HessianTheorem11.Geometry
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!+# Tangent containment for the actual singular equations

The tangent subspace is defined by the linear terms of every polynomial in the
vanishing ideal.  Its containment in the Hessian kernel is proved from the actual
gradient equations.  The dimension comparison then uses ordinary rank-nullity.
No radial inequality or singular-dimension theorem is assumed here.
-/

namespace HessianTheorem11

open MvPolynomial Module

noncomputable section

variable {K : Type*} [Field K] {n : ℕ}

/-- The coefficient-of-first-order linear map at a point. -/
def polynomialDifferential (F : MvPolynomial (Fin n) K) (x : Fin n → K) :
    (Fin n → K) →ₗ[K] K :=
  ∑ i, eval x (pderiv i F) • LinearMap.proj i

theorem polynomialDifferential_apply (F : MvPolynomial (Fin n) K)
    (x v : Fin n → K) :
    polynomialDifferential F x v = ∑ i, eval x (pderiv i F) * v i := by
  simp [polynomialDifferential]

/-- The usual embedded Zariski tangent subspace, for the reduced vanishing
ideal of a set of points. -/
def affineTangentSpace (Z : Set (Fin n → K)) (x : Fin n → K) :
    Submodule K (Fin n → K) :=
  ⨅ f : vanishingIdeal K Z, LinearMap.ker (polynomialDifferential f.1 x)

theorem mem_affineTangentSpace {Z : Set (Fin n → K)} {x v : Fin n → K} :
    v ∈ affineTangentSpace Z x ↔
      ∀ f : MvPolynomial (Fin n) K, f ∈ vanishingIdeal K Z →
        polynomialDifferential f x v = 0 := by
  simp [affineTangentSpace, Submodule.mem_iInf, LinearMap.mem_ker]

/-- Differentiating the gradient equations puts the embedded tangent space of
any subset of the singular locus into the actual Hessian kernel. -/
theorem affineTangentSpace_le_hessian_ker
    (F : MvPolynomial (Fin n) K) (Z : Set (Fin n → K))
    (singular : ∀ y ∈ Z, gradient F y = 0) (x : Fin n → K) :
    affineTangentSpace Z x ≤ LinearMap.ker (hessian F x).mulVecLin := by
  intro v hv
  apply LinearMap.mem_ker.mpr
  ext i
  have hpi : pderiv i F ∈ vanishingIdeal K Z := by
    intro y hy
    exact congrFun (singular y hy) i
  have he := (mem_affineTangentSpace.mp hv) (pderiv i F) hpi
  simpa [polynomialDifferential_apply, hessian, hessianPolynomial,
    Matrix.mulVec, dotProduct] using he

/-- Tangent containment yields the componentwise rank-plus-dimension bound.
This statement works for every matrix over every field. -/
theorem matrix_rank_add_finrank_le_of_le_ker
    (A : Matrix (Fin n) (Fin n) K) (T : Submodule K (Fin n → K))
    (contained : T ≤ LinearMap.ker A.mulVecLin) :
    A.rank + finrank K T ≤ n := by
  have hd := Submodule.finrank_mono contained
  have hr := A.mulVecLin.finrank_range_add_finrank_ker
  have hn : finrank K (Fin n → K) = n := by simp
  rw [hn] at hr
  change finrank K (LinearMap.range A.mulVecLin) + finrank K T ≤ n
  omega

/-- Equality of dimensions upgrades tangent containment to equality of
subspaces, as required in the exceptional eleven-variable branch. -/
theorem eq_ker_of_contained_of_rank_add_finrank
    (A : Matrix (Fin n) (Fin n) K) (T : Submodule K (Fin n → K))
    (contained : T ≤ LinearMap.ker A.mulVecLin)
    (saturated : A.rank + finrank K T = n) :
    T = LinearMap.ker A.mulVecLin := by
  apply Submodule.eq_of_le_of_finrank_eq contained
  have hr := A.mulVecLin.finrank_range_add_finrank_ker
  have hn : finrank K (Fin n → K) = n := by simp
  rw [hn] at hr
  change finrank K (LinearMap.range A.mulVecLin) + finrank K T = n at saturated
  omega

/-- Restricting a linear map to a subspace gives a kernel that injects into
the original kernel. -/
theorem restricted_kernel_finrank_le
    {V W : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] W) (T : Submodule K V) :
    finrank K (LinearMap.ker (A.domRestrict T)) ≤ finrank K (LinearMap.ker A) := by
  let inclusion : LinearMap.ker (A.domRestrict T) →ₗ[K] LinearMap.ker A :=
    { toFun := fun v => ⟨v.1.1, v.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply LinearMap.finrank_le_finrank_of_injective (f := inclusion)
  intro u v h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : LinearMap.ker A => z.1) h

/-- A rank bound on the restriction supplies the full-kernel lower bound
used in the tangent-incidence argument of Lemma 30.1. -/
theorem kernel_finrank_lower_of_restricted_rank
    {V W : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] W) (T : Submodule K V) {h : ℕ}
    (restricted_rank : finrank K (LinearMap.range (A.domRestrict T)) ≤ h) :
    finrank K T ≤ h + finrank K (LinearMap.ker A) := by
  have hi := restricted_kernel_finrank_le A T
  have hr := (A.domRestrict T).finrank_range_add_finrank_ker
  omega

/-- The actual tangent bound for the singular equations of a polynomial. -/
theorem hessian_rank_add_tangent_finrank_le
    (F : MvPolynomial (Fin n) K) (Z : Set (Fin n → K))
    (singular : ∀ y ∈ Z, gradient F y = 0) (x : Fin n → K) :
    (hessian F x).rank + finrank K (affineTangentSpace Z x) ≤ n :=
  matrix_rank_add_finrank_le_of_le_ker _ _
    (affineTangentSpace_le_hessian_ker F Z singular x)

/-- Specialization to the actual geometric singular locus used in Theorem 1.1. -/
theorem singularLocus_hessian_rank_add_tangent_finrank_le
    (F : RationalPolynomial n) (x : GeometricPoint n) :
    (hessian (geometricPolynomial F) x).rank +
      finrank GeometricField (affineTangentSpace (singularLocus F) x) ≤ n := by
  apply hessian_rank_add_tangent_finrank_le
  intro y hy
  exact hy

end

end HessianTheorem11
