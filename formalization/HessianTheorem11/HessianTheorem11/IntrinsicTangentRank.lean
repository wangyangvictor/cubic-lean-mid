import HessianTheorem11.SymmetricGeneralizedInverse
import HessianTheorem11.SingularFormalArc
import HessianTheorem11.SubmoduleCoordinates
import HessianTheorem11.TangentHessianRankGeometry

/-! Intrinsic Hessian rank bounds on the actual tangent space of a smooth
singular component. A symmetric generalized inverse removes any need to
assume or transport a special cubic normal form. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix Module PolynomialRestriction TangentHessianRank

theorem polynomialJacobian_rank_lt_image_rank
    (MR : GenericMatrixRankInput) {s n : ℕ}
    (H N : Matrix (Fin n) (Fin n) GeometricField) (hH : H.IsSymm)
    (hNsym : N.IsSymm) (hN : H * N * H = H) (hHrank : 0 < H.rank)
    (p : Fin n → GeometricPolynomial s) (hrel : quadraticRelation N p = 0)
    (hvalue : ∀ x, (fun i => eval x (p i)) ∈ LinearMap.range H.mulVecLin)
    (hJac : ∀ x, LinearMap.range (polynomialJacobian p x).mulVecLin ≤
      LinearMap.range H.mulVecLin)
    (x : GeometricPoint s) : (polynomialJacobian p x).rank < H.rank := by
  classical
  by_cases hp0 : p = 0
  · have hj : polynomialJacobian p x = 0 := by ext i j; simp [polynomialJacobian, hp0]
    simpa only [hj, Matrix.rank_zero] using hHrank
  · obtain ⟨i, hi⟩ : ∃ i, p i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hp0 (funext h)
    let I : Ideal (GeometricPolynomial s) := ⊥
    let M : Matrix (Fin n) (Fin s) (GeometricPolynomial s) := fun i j => pderiv j (p i)
    letI : I.IsPrime := Ideal.bot_prime
    obtain ⟨q, hq, hopen⟩ := MR.principal_open I M
    have hq0 : q ≠ 0 := by simpa only [I, Ideal.mem_bot] using hq
    have hprod : q * p i ∉ I := by simpa only [I, Ideal.mem_bot] using mul_ne_zero hq0 hi
    obtain ⟨y, hy, hye⟩ := exists_zeroLocus_eval_ne_zero I (q * p i) hprod
    have hyq : eval y q ≠ 0 := by
      intro he
      exact hye (by rw [map_mul, he, zero_mul])
    have hyp : (fun j => eval y (p j)) ≠ 0 := by
      intro he
      have hei : eval y (p i) = 0 := congrFun he i
      exact hye (by rw [map_mul, hei, mul_zero])
    have hg : genericMatrixRank I M < H.rank := by
      rw [← hopen y hy hyq]
      exact rank_lt_of_generalizedInverse_annihilator H N hH hN (polynomialJacobian p y)
        (hJac y) (fun i => eval y (p i)) (hvalue y) hyp
        (quadratic_relation_jacobian_annihilator N hNsym p hrel y)
    have hxI : x ∈ zeroLocus GeometricField I := by
      intro P hP
      have hP0 : P = 0 := hP
      simp [hP0]
    exact (MR.specialization_le I M x hxI).trans_lt hg

theorem restricted_gradient_jacobian {n s : ℕ}
    (F : GeometricPolynomial n) (B : Matrix (Fin n) (Fin s) GeometricField)
    (u : GeometricPoint s) :
    polynomialJacobian (fun i => restrict B (pderiv i F)) u = hessian F (B.mulVec u) * B := by
  ext i j
  simp [polynomialJacobian, pderiv_restrict, hessian, hessianPolynomial, Matrix.mul_apply, mul_comm]

theorem submoduleCoordinateMatrix_range {n : ℕ}
    (T : Submodule GeometricField (GeometricPoint n)) :
    LinearMap.range (submoduleCoordinateMatrix T).mulVecLin = T := by
  apply SetLike.coe_injective
  change Set.range (submoduleCoordinateMatrix T).mulVec = (T : Set (GeometricPoint n))
  rw [show (submoduleCoordinateMatrix T).mulVec = submoduleCoordinateMap T from
    funext (submoduleCoordinateMatrix_mulVec T)]
  exact submoduleCoordinateMap_range T

/-- The derivative of the restricted actual gradient has rank strictly
less than the nonzero Hessian rank at the base singular point, everywhere
on its actual tangent space. -/
theorem restricted_tangent_hessian_rank_lt
    (SA : FormalSmoothArcInput) (MR : GenericMatrixRankInput) {n : ℕ}
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (Z : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z)
    (hirred : GeometricallyIrreducible Z) (hsing : ∀ z ∈ Z, gradient F z = 0)
    (x : GeometricPoint n) (hx : x ∈ Z)
    (hdim : affineDimension Z = (finrank GeometricField (affineTangentSpace Z x) : Dimension))
    (hr : 0 < (hessian F x).rank)
    (v : GeometricPoint n) (hv : v ∈ affineTangentSpace Z x) :
    finrank GeometricField (LinearMap.range
      ((hessian F v).mulVecLin.domRestrict (affineTangentSpace Z x))) < (hessian F x).rank := by
  let T := affineTangentSpace Z x
  let B := submoduleCoordinateMatrix T
  let p : Fin n → GeometricPolynomial (finrank GeometricField T) :=
    fun i => restrict B (pderiv i F)
  have hB (u : GeometricPoint (finrank GeometricField T)) : B.mulVec u ∈ T := by
    exact (submoduleCoordinateMatrix_range T).le ⟨u, rfl⟩
  obtain ⟨N, hNsym, hN⟩ := exists_symmetric_generalizedInverse (hessian F x) (hessian_symmetric F x)
  have hrel : quadraticRelation N p = 0 :=
    SingularFormalArc.restricted_gradient_polynomial_relation SA F hF Z hZ hirred hsing
      x hx hdim N hN B hB
  have hvalue (u : GeometricPoint (finrank GeometricField T)) :
      (fun i => eval u (p i)) ∈ LinearMap.range (hessian F x).mulVecLin := by
    simpa only [p, eval_restrict, gradient] using
      SingularFormalArc.gradient_tangent_mem_hessian_range SA F hF Z hZ hirred hsing
        x hx hdim (B.mulVec u) (hB u)
  have hJac (u : GeometricPoint (finrank GeometricField T)) :
      LinearMap.range (polynomialJacobian p u).mulVecLin ≤ LinearMap.range (hessian F x).mulVecLin := by
    rw [show polynomialJacobian p u = hessian F (B.mulVec u) * B from restricted_gradient_jacobian F B u,
      Matrix.mulVecLin_mul, LinearMap.range_comp, submoduleCoordinateMatrix_range]
    exact SingularFormalArc.hessian_tangent_image_le_range SA F hF Z hZ hirred hsing
      x hx hdim (B.mulVec u) (hB u)
  obtain ⟨u, hu⟩ : ∃ u, B.mulVec u = v := by
    have hm : v ∈ LinearMap.range B.mulVecLin := by rwa [submoduleCoordinateMatrix_range]
    exact hm
  have hb := polynomialJacobian_rank_lt_image_rank MR (hessian F x) N (hessian_symmetric F x)
    hNsym hN hr p hrel hvalue hJac u
  rw [show polynomialJacobian p u = hessian F (B.mulVec u) * B from restricted_gradient_jacobian F B u,
    hu] at hb
  change finrank GeometricField (LinearMap.range ((hessian F v) * B).mulVecLin) < _ at hb
  rw [Matrix.mulVecLin_mul, LinearMap.range_comp, submoduleCoordinateMatrix_range,
    ← LinearMap.range_domRestrict] at hb
  exact hb

theorem tangent_hessian_rank_le_nine_intrinsic
    (SA : FormalSmoothArcInput) (MR : GenericMatrixRankInput)
    (F : GeometricPolynomial 11) (hF : F.IsHomogeneous 3)
    (Z : Set (GeometricPoint 11)) (hZ : AlgebraicallyClosedSet Z)
    (hirred : GeometricallyIrreducible Z) (hsing : ∀ z ∈ Z, gradient F z = 0)
    (x : GeometricPoint 11) (hx : x ∈ Z)
    (hdim : affineDimension Z = (finrank GeometricField (affineTangentSpace Z x) : Dimension))
    (ht : finrank GeometricField (affineTangentSpace Z x) = 6)
    (hr : (hessian F x).rank = 5)
    (v : GeometricPoint 11) (hv : v ∈ affineTangentSpace Z x) :
    (hessian F v).rank ≤ 9 := by
  have hb := restricted_tangent_hessian_rank_lt SA MR F hF Z hZ hirred hsing x hx hdim
    (by omega) v hv
  have hk := kernel_finrank_lower_of_restricted_rank (hessian F v).mulVecLin
    (affineTangentSpace Z x) (by omega : finrank GeometricField (LinearMap.range
      ((hessian F v).mulVecLin.domRestrict (affineTangentSpace Z x))) ≤ 4)
  have hd := (hessian F v).mulVecLin.finrank_range_add_finrank_ker
  change (hessian F v).rank + _ = finrank GeometricField (GeometricPoint 11) at hd
  rw [show finrank GeometricField (GeometricPoint 11) = 11 by simp] at hd
  omega

end HessianTheorem11
