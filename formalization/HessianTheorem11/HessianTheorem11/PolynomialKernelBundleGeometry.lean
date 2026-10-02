import HessianTheorem11.KernelAnnihilatorGeometry
import HessianTheorem11.LinearEmbeddingGeometry
import HessianTheorem11.AffineOpenSets

/-! Extend the retained linear-pencil kernel-bundle theorem to polynomial
matrices by an explicit closed graph embedding. No additional geometry is
assumed. All bundles remain actual subsets of the two coordinate spaces. -/
noncomputable section
namespace HessianTheorem11.PolynomialKernelBundle
open MvPolynomial Module Matrix
set_option maxHeartbeats 800000

variable {n a b d : ℕ}

def bundle (A : Matrix (Fin a) (Fin b) (GeometricPolynomial n))
    (O : Set (GeometricPoint n)) : Set (PairPoint n b) :=
  {p | pairLeft p ∈ O ∧ (A.map (eval (pairLeft p))).mulVec (pairRight p) = 0}

def equation (A : Matrix (Fin a) (Fin b) (GeometricPolynomial n)) (i : Fin a) :
    MvPolynomial (Fin n ⊕ Fin b) GeometricField :=
  ∑ j, rename Sum.inl (A i j) * X (Sum.inr j)

@[simp] theorem eval_equation (A : Matrix (Fin a) (Fin b) (GeometricPolynomial n))
    (i : Fin a) (p : PairPoint n b) :
    eval p (equation A i) = (A.map (eval (pairLeft p))).mulVec (pairRight p) i := by
  simp [equation, Matrix.mulVec, dotProduct, pairLeft, pairRight, eval_rename]

theorem closure_bundle_subset (A : Matrix (Fin a) (Fin b) (GeometricPolynomial n))
    {U O : Set (GeometricPoint n)} (hU : AlgebraicallyClosedSet U) (hOU : O ⊆ U) :
    geometricClosure (bundle A O) ⊆ bundle A U := by
  intro p hp
  refine ⟨?_, ?_⟩
  · have hh := polynomialMap_image_closure_subset (pairLeftPolynomials n b)
      (bundle A O) (Set.mem_image_of_mem _ hp)
    simp only [polynomialMap_pairLeftPolynomials] at hh
    apply geometricClosure_subset_closed (B := U) ?_ hU hh
    rintro x ⟨q,hq,rfl⟩
    exact hOU hq.1
  · ext i
    have hh := hp (equation A i) (by
      intro q hq
      change eval q (equation A i) = 0
      rw [eval_equation]
      exact congrFun hq.2 i)
    change eval p (equation A i) = 0 at hh
    simpa only [eval_equation, Pi.zero_apply] using hh

theorem closed_preimage {σ τ : Type*}
    (P : τ → MvPolynomial σ GeometricField)
    {Z : Set (τ → GeometricField)} (hZ : AlgebraicallyClosedSet Z) :
    AlgebraicallyClosedSet (polynomialMap P ⁻¹' Z) := by
  apply le_antisymm
  · intro x hx
    have h := polynomialMap_image_closure_subset P (polynomialMap P ⁻¹' Z)
      (Set.mem_image_of_mem (polynomialMap P) hx)
    exact geometricClosure_subset_closed (Set.image_preimage_subset _ _) hZ h
  · exact subset_geometricClosure _

theorem bundle_locally_closed (A : Matrix (Fin a) (Fin b) (GeometricPolynomial n))
    (U O : Set (GeometricPoint n)) (hU : AlgebraicallyClosedSet U)
    (hO : RelativelyOpenSet U O) :
    RelativelyOpenSet (geometricClosure (bundle A O)) (bundle A O) := by
  obtain ⟨C,hC,rfl⟩ := hO
  refine ⟨pairLeft ⁻¹' C, ?_, ?_⟩
  · simpa only [polynomialMap_pairLeftPolynomials] using
      closed_preimage (pairLeftPolynomials n b) hC
  · ext p
    constructor
    · intro hp
      exact ⟨subset_geometricClosure _ hp, hp.1.2⟩
    · rintro ⟨hp,hpC⟩
      have h := closure_bundle_subset A hU Set.diff_subset hp
      exact ⟨⟨h.1,hpC⟩,h.2⟩

theorem open_image {σ τ : Type*} [Fintype σ] [Fintype τ]
    (P : τ → MvPolynomial σ GeometricField)
    (Q : σ → MvPolynomial τ GeometricField)
    (h : Function.LeftInverse (polynomialMap Q) (polynomialMap P))
    {U O : Set (σ → GeometricField)} (hO : RelativelyOpenSet U O) :
    RelativelyOpenSet (polynomialMap P '' U) (polynomialMap P '' O) := by
  obtain ⟨C,hC,rfl⟩ := hO
  refine ⟨polynomialMap P '' C, ?_, ?_⟩
  · change geometricClosure (polynomialMap P '' C) = _
    rw [geometricClosure_image_of_polynomial_leftInverse P Q h C, hC]
  · exact Set.image_diff h.injective U C

def lift (P : Fin d → GeometricPolynomial n) :
    (Fin d ⊕ Fin b) → MvPolynomial (Fin n ⊕ Fin b) GeometricField :=
  Sum.elim (fun i => rename Sum.inl (P i)) (fun j => X (Sum.inr j))

@[simp] theorem map_lift (P : Fin d → GeometricPolynomial n) (p : PairPoint n b) :
    polynomialMap (lift P) p = pairPoint (polynomialMap P (pairLeft p)) (pairRight p) := by
  ext (i|j) <;> simp [polynomialMap, lift, pairPoint, pairLeft, pairRight, eval_rename]

theorem lift_leftInverse (P : Fin d → GeometricPolynomial n)
    (Q : Fin n → GeometricPolynomial d)
    (h : Function.LeftInverse (polynomialMap Q) (polynomialMap P)) :
    Function.LeftInverse (polynomialMap (lift (b := b) Q)) (polynomialMap (lift P)) := by
  intro p
  simp only [map_lift, pairLeft_pairPoint, pairRight_pairPoint]
  rw [h _, pairPoint_projections]

structure Linearization (A : Matrix (Fin a) (Fin b) (GeometricPolynomial n)) where
  size : ℕ
  embedding : Fin size → GeometricPolynomial n
  projection : Fin n → GeometricPolynomial size
  leftInverse : Function.LeftInverse (polynomialMap projection) (polynomialMap embedding)
  pencil : GeometricPoint size →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField
  evaluates : ∀ x, pencil (polynomialMap embedding x) = A.map (eval x)

def linearization (A : Matrix (Fin a) (Fin b) (GeometricPolynomial n)) : Linearization A := by
  classical
  let ι := Fin n ⊕ (Fin a × Fin b)
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let P : Fin (Fintype.card ι) → GeometricPolynomial n :=
    fun j => Sum.elim X (fun ij => A ij.1 ij.2) (e j)
  let Q : Fin n → GeometricPolynomial (Fintype.card ι) :=
    fun i => X (e.symm (Sum.inl i))
  let L : GeometricPoint (Fintype.card ι) →ₗ[GeometricField]
      Matrix (Fin a) (Fin b) GeometricField :=
    LinearMap.pi (fun i => LinearMap.pi (fun j => LinearMap.proj (e.symm (Sum.inr (i,j)))))
  refine ⟨Fintype.card ι,P,Q,?_,L,?_⟩
  · intro x
    ext i
    simp [polynomialMap, P, Q]
  · intro x
    ext i j
    change eval x (P (e.symm (Sum.inr (i,j)))) = eval x (A i j)
    simp [P]

namespace Linearization
variable {A : Matrix (Fin a) (Fin b) (GeometricPolynomial n)} (D : Linearization A)

theorem bundle_image (O : Set (GeometricPoint n)) :
    kernelBundle D.pencil (polynomialMap D.embedding '' O) =
      polynomialMap (lift D.embedding) '' bundle A O := by
  ext p
  constructor
  · rintro ⟨⟨x,hx,hxp⟩,hp⟩
    refine ⟨pairPoint x (pairRight p), ?_, ?_⟩
    · refine ⟨hx, ?_⟩
      change (A.map (eval x)).mulVec (pairRight p) = 0
      rw [← D.evaluates x, hxp]
      exact hp
    · rw [map_lift]
      simp [hxp]
  · rintro ⟨p,hp,rfl⟩
    simp only [map_lift, kernelBundle, Set.mem_setOf_eq, pairLeft_pairPoint, pairRight_pairPoint]
    exact ⟨⟨pairLeft p,hp.1,rfl⟩, by rw [D.evaluates]; exact hp.2⟩

theorem closed_image {U : Set (GeometricPoint n)} (hU : AlgebraicallyClosedSet U) :
    AlgebraicallyClosedSet (polynomialMap D.embedding '' U) := by
  change geometricClosure (polynomialMap D.embedding '' U) = _
  rw [geometricClosure_image_of_polynomial_leftInverse _ _ D.leftInverse, hU]

theorem dense_image {U O : Set (GeometricPoint n)} (hO : geometricClosure O = U) :
    geometricClosure (polynomialMap D.embedding '' O) = polynomialMap D.embedding '' U := by
  rw [geometricClosure_image_of_polynomial_leftInverse _ _ D.leftInverse, hO]

end Linearization

theorem bundle_irreducible (KI : KernelBundleInput)
    (A : Matrix (Fin a) (Fin b) (GeometricPolynomial n))
    (U O : Set (GeometricPoint n)) (hU : AlgebraicallyClosedSet U)
    (hi : GeometricallyIrreducible U) (hO : RelativelyOpenSet U O)
    (hdense : geometricClosure O = U) (ell : ℕ)
    (hnull : ∀ x ∈ O, finrank GeometricField (LinearMap.ker (A.map (eval x)).mulVecLin) = ell) :
    GeometricallyIrreducible (bundle A O) := by
  let D := linearization A
  have h := KI.closure_irreducible D.pencil
    (polynomialMap D.embedding '' U) (polynomialMap D.embedding '' O)
    (D.closed_image hU) (hi.polynomialMap_image D.embedding)
    (open_image D.embedding D.projection D.leftInverse hO) (D.dense_image hdense) ell (by
      rintro _ ⟨x,hx,rfl⟩
      rw [D.evaluates]
      exact hnull x hx)
  have hiB := (geometricallyIrreducible_closure_iff _).mp h
  rw [D.bundle_image] at hiB
  have him : polynomialMap (lift D.projection) ''
      (polynomialMap (lift D.embedding) '' bundle A O) = bundle A O := by
    have hf : (fun p => polynomialMap (lift (b := b) D.projection)
        (polynomialMap (lift D.embedding) p)) = id :=
      funext (lift_leftInverse _ _ D.leftInverse)
    rw [Set.image_image, hf, Set.image_id]
  have hback := hiB.polynomialMap_image (lift D.projection)
  rwa [him] at hback

theorem bundle_dimension (KI : KernelBundleInput)
    (A : Matrix (Fin a) (Fin b) (GeometricPolynomial n))
    (U O : Set (GeometricPoint n)) (hU : AlgebraicallyClosedSet U)
    (hi : GeometricallyIrreducible U) (hO : RelativelyOpenSet U O)
    (hdense : geometricClosure O = U) (t ell : ℕ) (ht : affineDimension U = (t : Dimension))
    (hnull : ∀ x ∈ O, finrank GeometricField (LinearMap.ker (A.map (eval x)).mulVecLin) = ell) :
    affineDimension (bundle A O) = ((t+ell : ℕ) : Dimension) := by
  let D := linearization A
  have h := KI.dimension D.pencil
    (polynomialMap D.embedding '' U) (polynomialMap D.embedding '' O)
    (D.closed_image hU) (hi.polynomialMap_image D.embedding)
    (open_image D.embedding D.projection D.leftInverse hO) (D.dense_image hdense) t ell
    (by rw [affineDimension_image_of_polynomial_leftInverse _ _ D.leftInverse, ht]) (by
      rintro _ ⟨x,hx,rfl⟩
      rw [D.evaluates]
      exact hnull x hx)
  rw [D.bundle_image, affineDimension_image_of_polynomial_leftInverse _ _
    (lift_leftInverse _ _ D.leftInverse)] at h
  exact h

end HessianTheorem11.PolynomialKernelBundle
