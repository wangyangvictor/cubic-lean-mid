import HessianTheorem11.ReducedKernelBundleCharts
import HessianTheorem11.ReducedAffineProductDimension

/-! Differential and kernel calculations for actual polynomial maps
(x,v) ↦ (x,A(x)v). These are algebraic calculations; no smoothness or
bundle input occurs in the helpers. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace HessianTheorem11.ReducedFiberMapDifferential
open MvPolynomial Module Matrix ReducedKernelTangent ReducedGenericImageTangent
  ReducedAffineProductDimension ReducedKernelBundleCharts

/-- An actual affine-line identity determines its differential. -/
theorem differential_of_line {n m : ℕ} (P : Fin m → GeometricPolynomial n)
    (x v : GeometricPoint n) (y w : GeometricPoint m)
    (hline : ∀ a : GeometricField, polynomialMap P (x+a•v)=y+a•w) :
    polynomialMapDifferential P x v = w := by
  let Q : Fin n → GeometricPolynomial 1 := fun i => C (x i)+C (v i)*X 0
  let R : Fin m → GeometricPolynomial 1 := fun i => C (y i)+C (w i)*X 0
  have hQ (a : GeometricPoint 1) : polynomialMap Q a = x+a 0•v := by
    ext i
    simp [Q,polynomialMap,mul_comm]
  have hR (a : GeometricPoint 1) : polynomialMap R a = y+a 0•w := by
    ext i
    simp [R,polynomialMap,mul_comm]
  have he (i) : aeval Q (P i) = R i := by
    apply MvPolynomial.funext
    intro a
    rw [← eval_polynomialMap]
    exact congrFun ((congrArg (polynomialMap P) (hQ a)).trans
      ((hline (a 0)).trans (hR a).symm)) i
  have hdQ : polynomialMapDifferential Q 0 (fun _ => 1) = v := by
    ext i
    simp [polynomialMapDifferential,Q,ReducedTangentRank.differential_add,
      ReducedTangentRank.differential_mul]
  ext i
  have h := differential_aeval Q (P i) 0 (fun _ => 1)
  rw [he,hdQ,hQ] at h
  simpa [R,ReducedTangentRank.differential_add,ReducedTangentRank.differential_mul] using h.symm

def coordinateFiberMap {n b : ℕ}
    (A : Matrix (Fin b) (Fin b) (GeometricPolynomial n)) :
    Fin (n+b) → GeometricPolynomial (n+b) :=
  fun i => rename finSumFinEquiv (fiberMap A (finSumFinEquiv.symm i))

@[simp] theorem map_coordinateFiberMap_pair {n b : ℕ}
    (A : Matrix (Fin b) (Fin b) (GeometricPolynomial n)) (p : PairPoint n b) :
    polynomialMap (coordinateFiberMap A) (pairCoordinateEquiv n b p) =
      pairCoordinateEquiv n b (polynomialMap (fiberMap A) p) := by
  have hcoord (q : PairPoint n b) (i : Fin (n+b)) :
      pairCoordinateEquiv n b q i = q (finSumFinEquiv.symm i) := by
    simp [pairCoordinateEquiv,LinearEquiv.piCongrLeft,
      LinearEquiv.piCongrLeft',Equiv.piCongrLeft']
  have hcomp : (pairCoordinateEquiv n b p) ∘ finSumFinEquiv = p := by
    ext j
    simp only [Function.comp_apply,hcoord,Equiv.symm_apply_apply]
  ext i
  change eval (pairCoordinateEquiv n b p)
    (rename finSumFinEquiv (fiberMap A (finSumFinEquiv.symm i))) = _
  rw [eval_rename,hcomp,hcoord]
  rfl

@[simp] theorem map_coordinateFiberMap {n b : ℕ}
    (A : Matrix (Fin b) (Fin b) (GeometricPolynomial n)) (x : GeometricPoint (n+b)) :
    polynomialMap (coordinateFiberMap A) x = (splitEquiv n b).symm
      (baseProjection n b x,(A.map (eval (baseProjection n b x))).mulVec (fiberProjection n b x)) := by
  obtain ⟨p,rfl⟩ := (pairCoordinateEquiv n b).surjective x
  rw [map_coordinateFiberMap_pair,eval_fiberMap,baseProjection_pair,fiberProjection_pair]
  rfl

/-- The first component is exactly the unchanged base coordinate. -/
theorem differential_base {n b : ℕ}
    (A : Matrix (Fin b) (Fin b) (GeometricPolynomial n)) (x v : GeometricPoint (n+b)) :
    baseProjection n b (polynomialMapDifferential (coordinateFiberMap A) x v) =
      baseProjection n b v := by
  let Q := linearCoordinatePolynomials (baseProjection n b)
  have he (i) : aeval (coordinateFiberMap A) (Q i) = Q i := by
    apply MvPolynomial.funext
    intro z
    rw [← eval_polynomialMap]
    change polynomialMap Q (polynomialMap (coordinateFiberMap A) z) i = polynomialMap Q z i
    simp only [Q,polynomialMap_linearCoordinatePolynomials,map_coordinateFiberMap]
    change ((splitEquiv n b) ((splitEquiv n b).symm _)).1 i = _
    simp
  ext i
  have h := differential_aeval (coordinateFiberMap A) (Q i) x v
  rw [he] at h
  change polynomialMapDifferential Q x v i =
    polynomialMapDifferential Q (polynomialMap (coordinateFiberMap A) x)
      (polynomialMapDifferential (coordinateFiberMap A) x v) i at h
  simpa only [Q,differential_linearCoordinates] using h.symm

/-- The differential on vertical vectors is the literal evaluated matrix. -/
theorem differential_vertical {n b : ℕ}
    (A : Matrix (Fin b) (Fin b) (GeometricPolynomial n))
    (x : GeometricPoint (n+b)) (v : GeometricPoint b) :
    polynomialMapDifferential (coordinateFiberMap A) x (vertical n b v) =
      vertical n b ((A.map (eval (baseProjection n b x))).mulVec v) := by
  apply differential_of_line _ x _ (polynomialMap (coordinateFiberMap A) x)
  intro c
  simp only [map_coordinateFiberMap,map_add,map_smul,base_vertical,fiber_vertical,
    smul_zero,add_zero,Matrix.mulVec_add,Matrix.mulVec_smul]
  change (splitEquiv n b).symm (_, _ + c • _) =
    (splitEquiv n b).symm (_, _) + c • (splitEquiv n b).symm (0,_)
  rw [← map_smul,← map_add]
  congr 1
  simp

/-- The differential kernel on the full product tangent is exactly the
vertical copy of the evaluated matrix kernel. -/
theorem tangent_kernel_dimension {n b : ℕ}
    (A : Matrix (Fin b) (Fin b) (GeometricPolynomial n))
    (Z : Set (GeometricPoint n)) (x : GeometricPoint (n+b))
    (hx : x ∈ affineCylinder Z b) :
    finrank GeometricField (LinearMap.ker
      ((polynomialMapDifferential (coordinateFiberMap A) x).domRestrict
        (affineTangentSpace (affineCylinder Z b) x))) =
      finrank GeometricField (LinearMap.ker (A.map (eval (baseProjection n b x))).mulVecLin) := by
  let T := affineTangentSpace (affineCylinder Z b) x
  let D := (polynomialMapDifferential (coordinateFiberMap A) x).domRestrict T
  let K := LinearMap.ker (A.map (eval (baseProjection n b x))).mulVecLin
  have hbase (u : LinearMap.ker D) : baseProjection n b u.val.val = 0 := by
    have h := congrArg (baseProjection n b) (LinearMap.mem_ker.mp u.property)
    simpa only [D,LinearMap.domRestrict_apply,differential_base,map_zero] using h
  have hrep (u : LinearMap.ker D) : u.val.val = vertical n b (fiberProjection n b u.val.val) := by
    apply (splitEquiv n b).injective
    apply Prod.ext
    · exact (hbase u).trans (base_vertical _).symm
    · exact (fiber_vertical _).symm
  have hmem (u : LinearMap.ker D) : fiberProjection n b u.val.val ∈ K := by
    have h := LinearMap.mem_ker.mp u.property
    change polynomialMapDifferential (coordinateFiberMap A) x u.val.val = 0 at h
    rw [hrep u,differential_vertical] at h
    have h' := congrArg (fiberProjection n b) h
    simpa only [fiber_vertical,map_zero] using h'
  let L : LinearMap.ker D →ₗ[GeometricField] K :=
    { toFun := fun u => ⟨fiberProjection n b u.val.val,hmem u⟩
      map_add' := by intro u v; apply Subtype.ext; simp
      map_smul' := by intro c u; apply Subtype.ext; simp }
  have hL : Function.Bijective L := by
    constructor
    · intro u v h
      apply Subtype.ext
      apply Subtype.ext
      rw [hrep u,hrep v]
      exact congrArg (vertical n b) (congrArg Subtype.val h)
    · intro u
      refine ⟨⟨⟨vertical n b u,vertical_mem_tangent Z x hx u⟩,?_⟩,?_⟩
      · change polynomialMapDifferential (coordinateFiberMap A) x (vertical n b u) = 0
        rw [differential_vertical]
        have h : (A.map (eval (baseProjection n b x))).mulVec u = 0 := u.property
        rw [h,map_zero]
      · apply Subtype.ext
        exact fiber_vertical u.val
  exact (LinearEquiv.ofBijective L hL).finrank_eq

end HessianTheorem11.ReducedFiberMapDifferential
