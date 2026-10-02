import HessianTheorem11.SmoothCubicPoint
import HessianTheorem11.CubicIdentities
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
The Hessian kernel lies in the actual differential hyperplane of a cubic.
At a nonzero gradient, restricting the Hessian to that hyperplane lowers
its image rank by exactly one. The geometric specialization uses the
proved vanishing-ideal tangent space of the actual irreducible cubic.
No Gauss graph, fiber-dimension estimate, or external AG input is assumed.
-/

noncomputable section
namespace CubicTenVariables.GaussTangentRank

open MvPolynomial HessianTheorem11 Module
open scoped BigOperators Matrix

section Linear
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- If the whole kernel is contained in the restricted domain, restriction
preserves that kernel by the literal subtype inclusion. -/
def kerDomRestrictEquiv (A : V →ₗ[K] W) (T : Submodule K V)
    (h : LinearMap.ker A ≤ T) :
    LinearMap.ker (A.domRestrict T) ≃ₗ[K] LinearMap.ker A where
  toFun v := ⟨v.1.1, v.2⟩
  invFun v := ⟨⟨v.1, h v.2⟩, v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [FiniteDimensional K V]

/-- Rank-nullity for a restriction containing the full kernel, stated
additively so no truncated subtraction obscures its exact dimension. -/
theorem finrank_range_domRestrict_add_finrank (A : V →ₗ[K] W)
    (T : Submodule K V) (h : LinearMap.ker A ≤ T) :
    finrank K (LinearMap.range (A.domRestrict T)) + finrank K V =
      finrank K (LinearMap.range A) + finrank K T := by
  have hk := (kerDomRestrictEquiv A T h).finrank_eq
  have hA := A.finrank_range_add_finrank_ker
  have hT := (A.domRestrict T).finrank_range_add_finrank_ker
  omega

/-- A nonzero functional defines a hyperplane. Restriction lowers image
rank by exactly one whenever this hyperplane contains the original kernel. -/
theorem finrank_range_restrict_ker_add_one (A : V →ₗ[K] W) (ell : V →ₗ[K] K)
    (hell : ell ≠ 0) (h : LinearMap.ker A ≤ LinearMap.ker ell) :
    finrank K (LinearMap.range (A.domRestrict (LinearMap.ker ell))) + 1 =
      finrank K (LinearMap.range A) := by
  have hr := finrank_range_domRestrict_add_finrank A (LinearMap.ker ell) h
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hell
  omega

end Linear

section Cubic
variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-- Euler's Hessian identity and symmetry place every kernel vector in the
actual differential kernel. This does not require `F(x)=0` or smoothness. -/
theorem hessian_ker_le_differential_ker (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous 3) (x : Fin n → K) :
    LinearMap.ker (hessian F x).mulVecLin ≤
      LinearMap.ker (polynomialDifferential F x) := by
  intro v hv
  have hz : (hessian F x).mulVec v = 0 := hv
  have hp : dotProduct ((hessian F x).mulVec x) v = 0 := by
    calc
      _ = dotProduct x ((hessian F x).mulVec v) := by
        rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, hessian_symmetric]
      _ = 0 := by rw [hz, dotProduct_zero]
  rw [hessian_mulVec_self hF] at hp
  have hd : (2 : K) * polynomialDifferential F x v = 0 := by
    simpa [dotProduct, Pi.smul_apply, nsmul_eq_mul, gradient,
      polynomialDifferential_apply, Finset.mul_sum, mul_assoc] using hp
  exact (mul_eq_zero.mp hd).resolve_left (by norm_num)

/-- A nonzero gradient is exactly the nonvanishing needed for the
actual differential to define a hyperplane. -/
theorem polynomialDifferential_ne_zero_of_gradient_ne_zero
    (F : MvPolynomial (Fin n) K) (x : Fin n → K) (hg : gradient F x ≠ 0) :
    polynomialDifferential F x ≠ 0 := by
  intro hz
  apply hg
  ext i
  have hi := LinearMap.congr_fun hz (Pi.single i 1)
  simpa [polynomialDifferential_apply, gradient, Pi.single_apply] using hi

/-- The actual Hessian loses exactly one image dimension on the smooth
differential hyperplane. No hypothesis that the point is on the cubic is needed. -/
theorem hessian_tangent_rank_add_one (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous 3) (x : Fin n → K) (hg : gradient F x ≠ 0) :
    finrank K (LinearMap.range
      ((hessian F x).mulVecLin.domRestrict (LinearMap.ker (polynomialDifferential F x)))) + 1 =
      (hessian F x).rank :=
  finrank_range_restrict_ker_add_one (hessian F x).mulVecLin (polynomialDifferential F x)
    (polynomialDifferential_ne_zero_of_gradient_ne_zero F x hg)
    (hessian_ker_le_differential_ker F hF x)

/-- The equivalent subtraction form; the additive theorem also records
that the full Hessian rank is positive. -/
theorem hessian_tangent_rank_eq_sub_one (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous 3) (x : Fin n → K) (hg : gradient F x ≠ 0) :
    finrank K (LinearMap.range
      ((hessian F x).mulVecLin.domRestrict (LinearMap.ker (polynomialDifferential F x)))) =
      (hessian F x).rank - 1 := by
  have h := hessian_tangent_rank_add_one F hF x hg
  omega

end Cubic

/-- On the literal geometric cubic, the same identity holds for the
vanishing-ideal tangent space, using proved irreducible-hypersurface geometry. -/
theorem hessian_affineTangent_rank_add_one {n : ℕ}
    (F : RationalPolynomial n) (hF : F.IsHomogeneous 3)
    (hirred : Irreducible (geometricPolynomial F))
    (x : GeometricPoint n) (hx : x ∈ cubicLocus F)
    (hg : gradient (geometricPolynomial F) x ≠ 0) :
    finrank GeometricField (LinearMap.range
      ((hessian (geometricPolynomial F) x).mulVecLin.domRestrict
        (affineTangentSpace (cubicLocus F) x))) + 1 =
      (hessian (geometricPolynomial F) x).rank := by
  rw [affineTangentSpace_cubicLocus_eq_ker F hirred x hx]
  exact hessian_tangent_rank_add_one (geometricPolynomial F) (geometric_homogeneous hF) x hg

/-- The actual geometric tangent-space rank in subtraction form. -/
theorem hessian_affineTangent_rank_eq_sub_one {n : ℕ}
    (F : RationalPolynomial n) (hF : F.IsHomogeneous 3)
    (hirred : Irreducible (geometricPolynomial F))
    (x : GeometricPoint n) (hx : x ∈ cubicLocus F)
    (hg : gradient (geometricPolynomial F) x ≠ 0) :
    finrank GeometricField (LinearMap.range
      ((hessian (geometricPolynomial F) x).mulVecLin.domRestrict
        (affineTangentSpace (cubicLocus F) x))) =
      (hessian (geometricPolynomial F) x).rank - 1 := by
  have h := hessian_affineTangent_rank_add_one F hF hirred x hx hg
  omega

end CubicTenVariables.GaussTangentRank
