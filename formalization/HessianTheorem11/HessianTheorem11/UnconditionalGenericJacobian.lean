import HessianTheorem11.ReducedTangentRank
import HessianTheorem11.ReducedDeterminantalDifferential

/-! A fully algebraic generic Jacobian open. The only statements not yet
identified here with Krull dimensions are the two ranks at the generic
point. All opens, density, actual tangent spaces, differential ranks and
maximum matrix-pencil ranks are constructed without geometric inputs. -/

noncomputable section
namespace HessianTheorem11.UnconditionalGeneric
open MvPolynomial Module ReducedTangentRank ReducedDeterminantal

/-- Finite equations for the entire reduced ideal, as an actual tangent
presentation at every point. No smoothness hypothesis is used. -/
structure TangentPresentation {n : ℕ} (U : Set (GeometricPoint n)) where
  count : ℕ
  equations : Fin count → GeometricPolynomial n
  vanishes : ∀ i, equations i ∈ vanishingIdeal GeometricField U
  tangent : ∀ x ∈ U, affineTangentSpace U x =
    LinearMap.ker (polynomialMapDifferential equations x)

theorem exists_tangentPresentation {n : ℕ} (U : Set (GeometricPoint n)) :
    Nonempty (TangentPresentation U) := by
  obtain ⟨c,f,hf,ht⟩ := exists_tangent_equations U
  exact ⟨⟨c,f,hf,ht⟩⟩

def stackedJacobian {n c m : ℕ} (f : Fin c → GeometricPolynomial n)
    (P : Fin m → GeometricPolynomial n) :
    Matrix (Fin (c+m)) (Fin n) (GeometricPolynomial n) :=
  (stackMatrix (jacobian f) (jacobian P)).submatrix
    finSumFinEquiv.symm (Equiv.refl _)

@[simp] theorem evaluated_stacked_rank {n c m : ℕ}
    (f : Fin c → GeometricPolynomial n) (P : Fin m → GeometricPolynomial n)
    (x : GeometricPoint n) :
    (evaluatedMatrix (stackedJacobian f P) x).rank =
      (evaluatedMatrix (jacobian f) x).rank +
      finrank GeometricField (LinearMap.range
        ((polynomialMapDifferential P x).domRestrict
          (LinearMap.ker (polynomialMapDifferential f x)))) := by
  have he : evaluatedMatrix (stackedJacobian f P) x =
      (stackMatrix (evaluatedMatrix (jacobian f) x)
        (evaluatedMatrix (jacobian P) x)).submatrix
          finSumFinEquiv.symm (Equiv.refl _) := by
    ext i j
    change eval x (stackMatrix (jacobian f) (jacobian P) (finSumFinEquiv.symm i) j) = _
    cases h : finSumFinEquiv.symm i <;> simp [Matrix.submatrix, h, stackMatrix, evaluatedMatrix]
  rw [he, Matrix.rank_submatrix, rank_fromRows, evaluated_jacobian, evaluated_jacobian]

def principalOpen {n : ℕ} (U : Set (GeometricPoint n)) (q : GeometricPolynomial n) :=
  {x | x ∈ U ∧ eval x q ≠ 0}

theorem principalOpen_isOpen {n : ℕ} (U : Set (GeometricPoint n))
    (q : GeometricPolynomial n) : RelativelyOpenSet U (principalOpen U q) := by
  refine ⟨zeroLocus GeometricField (Ideal.span {q}),
    algebraicallyClosedSet_zeroLocus _, ?_⟩
  ext x
  simp [principalOpen,zeroLocus_span]

/-- Rank over the actual function field is attained on a dense principal
open. This theorem has no geometric input and allows polynomial matrices. -/
theorem polynomial_matrix_rank_open {n a b : ℕ}
    (U : Set (GeometricPoint n)) (hU : AlgebraicallyClosedSet U)
    (hi : GeometricallyIrreducible U)
    (A : Matrix (Fin a) (Fin b) (GeometricPolynomial n)) :
    ∃ q : GeometricPolynomial n, q ∉ vanishingIdeal GeometricField U ∧
      geometricClosure (principalOpen U q) = U ∧
      (principalOpen U q).Nonempty ∧
      ∀ x ∈ principalOpen U q,
        (evaluatedMatrix A x).rank = genericMatrixRank (vanishingIdeal GeometricField U) A := by
  letI : (vanishingIdeal GeometricField U).IsPrime := hi
  obtain ⟨q,hq,hr⟩ := ReducedGenericRank.principal_open
    (vanishingIdeal GeometricField U) A
  have hz : zeroLocus GeometricField (vanishingIdeal GeometricField U) = U := hU
  obtain ⟨x,hx,hqx⟩ := exists_zeroLocus_eval_ne_zero _ q hq
  have hn : (principalOpen U q).Nonempty := ⟨x,hz ▸ hx,hqx⟩
  exact ⟨q,hq,(principalOpen_isOpen U q).dense_of_nonempty hU hi hn,hn,
    fun x hx => hr x (hz.symm ▸ hx.1) hx.2⟩

/-- The part of generic smoothness and generic differential rank which is
pure minor algebra. The dimensions are explicit differences of the actual
function-field Jacobian ranks, not dimensions assigned by definition. -/
structure JacobianOpen {n m a b : ℕ} (U : Set (GeometricPoint n))
    (P : Fin m → GeometricPolynomial n)
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
    (J : TangentPresentation U) where
  polynomial : GeometricPolynomial n
  not_in_ideal : polynomial ∉ vanishingIdeal GeometricField U
  dense : geometricClosure (principalOpen U polynomial) = U
  nonempty : (principalOpen U polynomial).Nonempty
  tangent_rank : ∀ x ∈ principalOpen U polynomial,
    finrank GeometricField (affineTangentSpace U x) =
      n - genericMatrixRank (vanishingIdeal GeometricField U) (jacobian J.equations)
  differential_rank : ∀ x ∈ principalOpen U polynomial,
    finrank GeometricField (LinearMap.range
      ((polynomialMapDifferential P x).domRestrict (affineTangentSpace U x))) =
      genericMatrixRank (vanishingIdeal GeometricField U) (stackedJacobian J.equations P) -
        genericMatrixRank (vanishingIdeal GeometricField U) (jacobian J.equations)
  kernel_dimension : ∀ x ∈ principalOpen U polynomial,
    finrank GeometricField (LinearMap.ker (M x).mulVecLin) =
      b - genericMatrixRank (vanishingIdeal GeometricField U) (pencilPolynomial M)
  maximal_rank : ∀ x ∈ principalOpen U polynomial, ∀ y ∈ U,
    (M y).rank ≤ (M x).rank

theorem exists_jacobianOpen {n m a b : ℕ}
    (U : Set (GeometricPoint n)) (hU : AlgebraicallyClosedSet U)
    (hi : GeometricallyIrreducible U) (P : Fin m → GeometricPolynomial n)
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
    (J : TangentPresentation U) : Nonempty (JacobianOpen U P M J) := by
  letI : (vanishingIdeal GeometricField U).IsPrime := hi
  let I := vanishingIdeal GeometricField U
  have hz : zeroLocus GeometricField I = U := hU
  obtain ⟨q,hq,_,_,hrq⟩ := polynomial_matrix_rank_open U hU hi (jacobian J.equations)
  obtain ⟨s,hs,_,_,hrs⟩ := polynomial_matrix_rank_open U hU hi
    (stackedJacobian J.equations P)
  obtain ⟨p,hp,_,_,hrp⟩ := polynomial_matrix_rank_open U hU hi (pencilPolynomial M)
  have hprod : q*s*p ∉ I := by
    intro h
    rcases hi.mem_or_mem h with h|h
    · exact (hi.mem_or_mem h).elim hq hs
    · exact hp h
  have hn : (principalOpen U (q*s*p)).Nonempty := by
    obtain ⟨x,hx,hxq⟩ := exists_zeroLocus_eval_ne_zero I (q*s*p) hprod
    exact ⟨x,hz ▸ hx,hxq⟩
  have parts (x) (hx : x ∈ principalOpen U (q*s*p)) :
      x ∈ principalOpen U q ∧ x ∈ principalOpen U s ∧ x ∈ principalOpen U p := by
    have hh : (eval x q * eval x s) * eval x p ≠ 0 := by simpa using hx.2
    exact ⟨⟨hx.1,(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hh).1).1⟩,
      ⟨hx.1,(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hh).1).2⟩,
      ⟨hx.1,(mul_ne_zero_iff.mp hh).2⟩⟩
  have hpencil (x : GeometricPoint n) : evaluatedMatrix (pencilPolynomial M) x = M x := by
    ext i j
    exact eval_pencilPolynomial M x i j
  refine ⟨{ polynomial := q*s*p
            not_in_ideal := hprod
            dense := (principalOpen_isOpen U _).dense_of_nonempty hU hi hn
            nonempty := hn
            tangent_rank := ?_
            differential_rank := ?_
            kernel_dimension := ?_
            maximal_rank := ?_ }⟩
  · intro x hx
    have he := rank_add_ker (evaluatedMatrix (jacobian J.equations) x)
    rw [evaluated_jacobian, ← J.tangent x hx.1] at he
    rw [hrq x (parts x hx).1] at he
    omega
  · intro x hx
    have he := evaluated_stacked_rank J.equations P x
    rw [hrs x (parts x hx).2.1,hrq x (parts x hx).1,← J.tangent x hx.1] at he
    omega
  · intro x hx
    have he := rank_add_ker (M x)
    have hm := hrp x (parts x hx).2.2
    rw [hpencil] at hm
    rw [hm] at he
    omega
  · intro x hx y hy
    have hr := ReducedGenericRank.specialization_le I (pencilPolynomial M) y (hz.symm ▸ hy)
    have hm := hrp x (parts x hx).2.2
    rw [hpencil] at hr hm
    exact hr.trans hm.ge

/-- The entire remaining GR construction reduces to two field-algebra
identities: generic tangent dimension and generic image differential rank. -/
def JacobianOpen.toGenericRankOpen {n m a b : ℕ} {U : Set (GeometricPoint n)}
    {P : Fin m → GeometricPolynomial n}
    {M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField}
    {J : TangentPresentation U} (G : JacobianOpen U P M J)
    (hbase : affineDimension U =
      ((n - genericMatrixRank (vanishingIdeal GeometricField U) (jacobian J.equations) : ℕ) : Dimension))
    (himage : affineDimension (geometricClosure (polynomialMap P '' U)) =
      ((genericMatrixRank (vanishingIdeal GeometricField U) (stackedJacobian J.equations P) -
        genericMatrixRank (vanishingIdeal GeometricField U) (jacobian J.equations) : ℕ) : Dimension)) :
    GenericRankOpen U P M where
  openSet := principalOpen U G.polynomial
  isOpen := principalOpen_isOpen U _
  subset := fun _ hx => hx.1
  dense := G.dense
  nonempty := G.nonempty
  baseDimension := n - genericMatrixRank (vanishingIdeal GeometricField U) (jacobian J.equations)
  imageDimension := genericMatrixRank (vanishingIdeal GeometricField U) (stackedJacobian J.equations P) -
    genericMatrixRank (vanishingIdeal GeometricField U) (jacobian J.equations)
  nullity := b - genericMatrixRank (vanishingIdeal GeometricField U) (pencilPolynomial M)
  dimension_base := hbase
  dimension_image := himage
  smooth := G.tangent_rank
  differential_rank := G.differential_rank
  kernel_dimension := G.kernel_dimension
  maximal_rank := G.maximal_rank

end HessianTheorem11.UnconditionalGeneric
