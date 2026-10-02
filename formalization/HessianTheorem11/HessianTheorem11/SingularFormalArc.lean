import HessianTheorem11.FormalSmoothArc
import HessianTheorem11.Polarization
import HessianTheorem11.GradientIncidence
import Mathlib.Algebra.MvPolynomial.Funext

/-! The second-normal quadratic identity, derived from coefficients of
actual formal arcs in a singular variety. Higher arc terms are retained. -/

noncomputable section
namespace HessianTheorem11.SingularFormalArc
open MvPolynomial Matrix Module

variable {K : Type*} [CommRing K] {n : ℕ}

def evaluateArc (γ : Fin n → PowerSeries K) :
    MvPolynomial (Fin n) K →+* PowerSeries K := eval₂Hom PowerSeries.C γ

def hessianArc (F : MvPolynomial (Fin n) K) (γ : Fin n → PowerSeries K) :
    Matrix (Fin n) (Fin n) (PowerSeries K) :=
  (hessianPolynomial F).map (evaluateArc γ)

theorem coefficient_hessianArc (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (γ : Fin n → PowerSeries K) (d : ℕ) (i j : Fin n) :
    PowerSeries.coeff d (hessianArc F γ i j) = hessian F (arcCoefficient γ d) i j := by
  have he := homogeneous_one_expansion (hessian_entry_homogeneous_one hF i j)
  change PowerSeries.coeff d (evaluateArc γ (hessianPolynomial F i j)) = _
  rw [he]
  simp only [map_sum, map_mul, evaluateArc, eval₂Hom_X', eval₂Hom_C,
    PowerSeries.coeff_mul_C]
  exact (hessian_entry_expansion hF (arcCoefficient γ d) i j).symm

theorem hessianArc_mul_curve_zero (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (γ : Fin n → PowerSeries K) (hγ : ∀ i, evaluateArc γ (pderiv i F) = 0) :
    (hessianArc F γ).mulVec γ = 0 := by
  funext i
  have he := congrArg (evaluateArc γ) (hF.pderiv (i := i)).sum_X_mul_pderiv
  simp only [map_sum, map_mul, map_nsmul, hγ, nsmul_zero] at he
  simpa [hessianArc, Matrix.mulVec, dotProduct, hessianPolynomial, evaluateArc, mul_comm] using he

theorem hessian_coefficient_convolution (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (γ : Fin n → PowerSeries K) (hγ : ∀ i, evaluateArc γ (pderiv i F) = 0) (d : ℕ) :
    ∑ ij ∈ Finset.antidiagonal d,
      (hessian F (arcCoefficient γ ij.1)).mulVec (arcCoefficient γ ij.2) = 0 := by
  ext i
  have he := congrArg (PowerSeries.coeff d)
    (congrFun (hessianArc_mul_curve_zero F hF γ hγ) i)
  simp only [Matrix.mulVec, dotProduct, map_sum, PowerSeries.coeff_mul,
    coefficient_hessianArc F hF γ, Pi.zero_apply, map_zero] at he
  rw [Finset.sum_comm] at he
  simpa only [Finset.sum_apply, Matrix.mulVec, dotProduct, arcCoefficient] using he

theorem second_coefficient_equation
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (γ : Fin n → PowerSeries GeometricField)
    (hγ : ∀ i, evaluateArc γ (pderiv i F) = 0) :
    (hessian F (arcCoefficient γ 0)).mulVec (arcCoefficient γ 2) =
      -gradient F (arcCoefficient γ 1) := by
  have h₂ := hessian_coefficient_convolution F hF γ hγ 2
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero] at h₂
  rw [hessian_polarization hF (arcCoefficient γ 2) (arcCoefficient γ 0),
    hessian_mulVec_self hF] at h₂
  funext i
  have hi := congrFun h₂ i
  simp only [Pi.add_apply, Pi.zero_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply] at hi
  change (hessian F (arcCoefficient γ 0)).mulVec (arcCoefficient γ 2) i =
    -(gradient F (arcCoefficient γ 1) i)
  linear_combination (1 / 2 : GeometricField) * hi

theorem fourth_coefficient_isotropic
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (γ : Fin n → PowerSeries GeometricField)
    (hγ : ∀ i, evaluateArc γ (pderiv i F) = 0)
    (hx : (hessian F (arcCoefficient γ 0)).mulVec (arcCoefficient γ 0) = 0)
    (hv : (hessian F (arcCoefficient γ 0)).mulVec (arcCoefficient γ 1) = 0) :
    dotProduct (arcCoefficient γ 2)
      ((hessian F (arcCoefficient γ 0)).mulVec (arcCoefficient γ 2)) = 0 := by
  let a := arcCoefficient γ
  have h₄ := hessian_coefficient_convolution F hF γ hγ 4
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero] at h₄
  have hs (u v : GeometricPoint n) :
      dotProduct (a 0) ((hessian F u).mulVec v) =
        dotProduct u ((hessian F (a 0)).mulVec v) := by
    exact (polarization_rotate hF (a 0) v u).trans (polarization_swap_last hF u (a 0) v)
  have hz₀ (u : GeometricPoint n) : dotProduct (a 0) ((hessian F u).mulVec (a 0)) = 0 := by
    rw [hs, hx, dotProduct_zero]
  have hz₁ (u : GeometricPoint n) : dotProduct (a 0) ((hessian F u).mulVec (a 1)) = 0 := by
    rw [hs, hv, dotProduct_zero]
  have hdot := congrArg (dotProduct (a 0)) h₄
  simp only [dotProduct_add, dotProduct_zero] at hdot
  change dotProduct (a 0) ((hessian F (a 0)).mulVec (a 4)) +
    (dotProduct (a 0) ((hessian F (a 1)).mulVec (a 3)) +
      (dotProduct (a 0) ((hessian F (a 2)).mulVec (a 2)) +
        (dotProduct (a 0) ((hessian F (a 3)).mulVec (a 1)) +
          dotProduct (a 0) ((hessian F (a 4)).mulVec (a 0))))) = 0 at hdot
  rw [hessian_polarization hF (a 0) (a 4), hessian_polarization hF (a 1) (a 3),
    hz₀, hz₁] at hdot
  simpa only [zero_add, add_zero, hs] using hdot

/-- Every actual tangent direction to a smooth singular subvariety has a
second normal lift satisfying the quadratic isotropy identity. This does
not require the tangent space to equal the full Hessian kernel. -/
theorem exists_second_normal_lift (SA : FormalSmoothArcInput)
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (Z : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z)
    (hirred : GeometricallyIrreducible Z)
    (hsing : ∀ z ∈ Z, gradient F z = 0)
    (x : GeometricPoint n) (hx : x ∈ Z)
    (hdim : affineDimension Z = (finrank GeometricField (affineTangentSpace Z x) : Dimension))
    (v : GeometricPoint n) (hv : v ∈ affineTangentSpace Z x) :
    ∃ a : GeometricPoint n, (hessian F x).mulVec a = -gradient F v ∧
      dotProduct a ((hessian F x).mulVec a) = 0 := by
  obtain ⟨γ, hγ₀, hγ₁, hvan⟩ := SA.lift Z hZ hirred x hx hdim v hv
  have hγ (i : Fin n) : evaluateArc γ (pderiv i F) = 0 := by
    apply hvan
    intro z hz
    exact congrFun (hsing z hz) i
  refine ⟨arcCoefficient γ 2, ?_, ?_⟩
  · simpa only [hγ₀, hγ₁] using second_coefficient_equation F hF γ hγ
  · have hxx : (hessian F x).mulVec x = 0 := by
      rw [hessian_mulVec_self hF, hsing x hx, smul_zero]
    have hxv : (hessian F x).mulVec v = 0 :=
      affineTangentSpace_le_hessian_ker F Z hsing x hv
    have hiso := fourth_coefficient_isotropic F hF γ hγ
      (by rwa [hγ₀]) (by rwa [hγ₀, hγ₁])
    simpa only [hγ₀] using hiso

/-- Any actual generalized inverse of H(x) gives a quadratic relation on
the restricted gradient. Choosing the inverse nondegenerate normal block
recovers the source's `q(p)=0` identity. -/
theorem gradient_quadratic_relation (SA : FormalSmoothArcInput)
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (Z : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z)
    (hirred : GeometricallyIrreducible Z)
    (hsing : ∀ z ∈ Z, gradient F z = 0)
    (x : GeometricPoint n) (hx : x ∈ Z)
    (hdim : affineDimension Z = (finrank GeometricField (affineTangentSpace Z x) : Dimension))
    (N : Matrix (Fin n) (Fin n) GeometricField)
    (hN : hessian F x * N * hessian F x = hessian F x)
    (v : GeometricPoint n) (hv : v ∈ affineTangentSpace Z x) :
    dotProduct (gradient F v) (N.mulVec (gradient F v)) = 0 := by
  obtain ⟨a, hsolve, hiso⟩ := exists_second_normal_lift SA F hF Z hZ hirred hsing x hx hdim v hv
  have hg : gradient F v = -(hessian F x).mulVec a := by rw [hsolve, neg_neg]
  rw [hg, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
  calc
    _ = dotProduct a ((hessian F x).mulVec (N.mulVec ((hessian F x).mulVec a))) := by
      rw [Matrix.dotProduct_mulVec a (hessian F x), ← Matrix.mulVec_transpose, hessian_symmetric]
    _ = dotProduct a ((hessian F x * N * hessian F x).mulVec a) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = 0 := by rw [hN]; exact hiso

/-- The corresponding literal polynomial identity for the actual gradient
restricted along any linear parametrization of the tangent space. -/
theorem restricted_gradient_polynomial_relation (SA : FormalSmoothArcInput)
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (Z : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z)
    (hirred : GeometricallyIrreducible Z)
    (hsing : ∀ z ∈ Z, gradient F z = 0)
    (x : GeometricPoint n) (hx : x ∈ Z)
    (hdim : affineDimension Z = (finrank GeometricField (affineTangentSpace Z x) : Dimension))
    (N : Matrix (Fin n) (Fin n) GeometricField)
    (hN : hessian F x * N * hessian F x = hessian F x)
    {σ : Type*} [Fintype σ] (B : Matrix (Fin n) σ GeometricField)
    (hB : ∀ u : σ → GeometricField, B.mulVec u ∈ affineTangentSpace Z x) :
    (∑ i, ∑ j, C (N i j) * PolynomialRestriction.restrict B (pderiv i F) *
      PolynomialRestriction.restrict B (pderiv j F)) = 0 := by
  apply MvPolynomial.funext
  intro u
  have he := gradient_quadratic_relation SA F hF Z hZ hirred hsing x hx hdim N hN
    (B.mulVec u) (hB u)
  simp only [map_sum, map_mul, eval_C, PolynomialRestriction.eval_restrict, map_zero]
  simpa only [dotProduct, Matrix.mulVec, Finset.mul_sum, gradient, mul_left_comm, mul_assoc] using he

theorem gradient_tangent_mem_hessian_range (SA : FormalSmoothArcInput)
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (Z : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z)
    (hirred : GeometricallyIrreducible Z)
    (hsing : ∀ z ∈ Z, gradient F z = 0)
    (x : GeometricPoint n) (hx : x ∈ Z)
    (hdim : affineDimension Z = (finrank GeometricField (affineTangentSpace Z x) : Dimension))
    (v : GeometricPoint n) (hv : v ∈ affineTangentSpace Z x) :
    gradient F v ∈ LinearMap.range (hessian F x).mulVecLin := by
  obtain ⟨a, ha, _⟩ := exists_second_normal_lift SA F hF Z hZ hirred hsing x hx hdim v hv
  refine ⟨-a, ?_⟩
  change (hessian F x).mulVec (-a) = gradient F v
  rw [Matrix.mulVec_neg, ha, neg_neg]

/-- Every actual tangent vector at a smooth point of a singular component
lies on the cubic. This follows from the second normal equation and Euler,
without identifying the component with its tangent space. -/
theorem eval_tangent_eq_zero (SA : FormalSmoothArcInput)
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (Z : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z)
    (hirred : GeometricallyIrreducible Z)
    (hsing : ∀ z ∈ Z, gradient F z = 0)
    (x : GeometricPoint n) (hx : x ∈ Z)
    (hdim : affineDimension Z = (finrank GeometricField (affineTangentSpace Z x) : Dimension))
    (v : GeometricPoint n) (hv : v ∈ affineTangentSpace Z x) : eval v F = 0 := by
  obtain ⟨a, ha⟩ := gradient_tangent_mem_hessian_range SA F hF Z hZ hirred hsing x hx hdim v hv
  have hk : (hessian F x).mulVec v = 0 :=
    affineTangentSpace_le_hessian_ker F Z hsing x hv
  have he : dotProduct v (gradient F v) = 0 := by
    rw [← ha]
    change dotProduct v ((hessian F x).mulVec a) = 0
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hessian_symmetric, hk]
    simp
  have hEuler := euler_cubic hF v
  change dotProduct v (gradient F v) = 3 * eval v F at hEuler
  rw [he] at hEuler
  exact (mul_eq_zero.mp hEuler.symm).resolve_left (by norm_num)

/-- Polarizing the actual tangent-gradient range statement proves the
compatibility condition for the tangent space of the Hessian-kernel bundle. -/
theorem hessian_tangent_image_le_range (SA : FormalSmoothArcInput)
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (Z : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z)
    (hirred : GeometricallyIrreducible Z)
    (hsing : ∀ z ∈ Z, gradient F z = 0)
    (x : GeometricPoint n) (hx : x ∈ Z)
    (hdim : affineDimension Z = (finrank GeometricField (affineTangentSpace Z x) : Dimension))
    (v : GeometricPoint n) (hv : v ∈ affineTangentSpace Z x) :
    (affineTangentSpace Z x).map (hessian F v).mulVecLin ≤
      LinearMap.range (hessian F x).mulVecLin := by
  rintro _ ⟨u, hu, rfl⟩
  have hp := gradient_tangent_mem_hessian_range SA F hF Z hZ hirred hsing x hx hdim
    (v + u) ((affineTangentSpace Z x).add_mem hv hu)
  have hm := gradient_tangent_mem_hessian_range SA F hF Z hZ hirred hsing x hx hdim
    (v - u) ((affineTangentSpace Z x).sub_mem hv hu)
  have he : (hessian F v).mulVec u = (1 / 2 : GeometricField) •
      (gradient F (v + u) - gradient F (v - u)) := by
    rw [gradient_difference hF]
    ext i
    simp [Pi.smul_apply, nsmul_eq_mul]
  change (hessian F v).mulVec u ∈ LinearMap.range (hessian F x).mulVecLin
  rw [he]
  exact (LinearMap.range (hessian F x).mulVecLin).smul_mem _
    ((LinearMap.range (hessian F x).mulVecLin).sub_mem hp hm)

end HessianTheorem11.SingularFormalArc
