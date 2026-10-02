import HessianTheorem11.TangentBundleGeometry
import HessianTheorem11.AffineOpenSets
import HessianTheorem11.ReducedGenericRank
import Mathlib.RingTheory.MvPolynomial.Basic

/-! General tangent and differential rank comparisons, deduced from the
retained generic-rank theorem and polynomial minors. -/

noncomputable section
namespace HessianTheorem11.ReducedTangentRank
open MvPolynomial Module MatrixRankMinors

theorem differential_add {n : ℕ} (f g : GeometricPolynomial n)
    (x v : GeometricPoint n) :
    polynomialDifferential (f + g) x v =
      polynomialDifferential f x v + polynomialDifferential g x v := by
  simp [polynomialDifferential_apply, add_mul, Finset.sum_add_distrib]

theorem differential_mul {n : ℕ} (f g : GeometricPolynomial n)
    (x v : GeometricPoint n) :
    polynomialDifferential (f * g) x v =
      eval x g * polynomialDifferential f x v +
        eval x f * polynomialDifferential g x v := by
  simp only [polynomialDifferential_apply, Derivation.leibniz, smul_eq_mul,
    map_add, map_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  rw [add_comm]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

/-- A finite generating family of the reduced vanishing ideal presents all
embedded tangent spaces at points of the set. -/
theorem exists_tangent_equations {n : ℕ} (Z : Set (GeometricPoint n)) :
    ∃ (c : ℕ) (f : Fin c → GeometricPolynomial n),
      (∀ i, f i ∈ vanishingIdeal GeometricField Z) ∧
      ∀ x ∈ Z, affineTangentSpace Z x =
        LinearMap.ker (polynomialMapDifferential f x) := by
  obtain ⟨c, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (vanishingIdeal GeometricField Z))
  have hmem (i) : f i ∈ vanishingIdeal GeometricField Z := by
    rw [← hf]
    exact Submodule.subset_span ⟨i, rfl⟩
  refine ⟨c, f, hmem, ?_⟩
  intro x hx
  ext v
  constructor
  · intro hv
    apply LinearMap.mem_ker.mpr
    ext i
    exact mem_affineTangentSpace.mp hv (f i) (hmem i)
  · intro hv
    apply mem_affineTangentSpace.mpr
    intro p hp
    rw [← hf] at hp
    induction hp using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨i, rfl⟩ := hp
      exact congrFun (LinearMap.mem_ker.mp hv) i
    | zero => simp [polynomialDifferential_apply]
    | add p q hp hq ihp ihq => rw [differential_add, ihp, ihq, add_zero]
    | smul a p hp ih =>
      change polynomialDifferential (a * p) x v = 0
      have hpZ : p ∈ vanishingIdeal GeometricField Z := by rwa [hf] at hp
      rw [differential_mul, show eval x p = 0 from hpZ x hx, ih]
      ring

def jacobian {n c : ℕ} (f : Fin c → GeometricPolynomial n) :
    Matrix (Fin c) (Fin n) (GeometricPolynomial n) :=
  fun i j => pderiv j (f i)

@[simp] theorem evaluated_jacobian {n c : ℕ}
    (f : Fin c → GeometricPolynomial n) (x : GeometricPoint n) :
    (evaluatedMatrix (jacobian f) x).mulVecLin = polynomialMapDifferential f x := by
  ext v i
  simp [jacobian, evaluatedMatrix, polynomialMapDifferential,
    polynomialDifferential_apply, Matrix.mulVec, dotProduct]

/-- A rank present at a point remains present somewhere in any dense set.
This is the elementary nonvanishing-minor argument. -/
theorem exists_rank_ge_in_dense {n : ℕ} {α β : Type*}
    [Fintype α] [Fintype β]
    (M : Matrix α β (GeometricPolynomial n))
    (Z O : Set (GeometricPoint n)) (hdense : geometricClosure O = Z)
    (x : GeometricPoint n) (hx : x ∈ Z) :
    ∃ y ∈ O, (M.map (eval x)).rank ≤ (M.map (eval y)).rank := by
  classical
  obtain ⟨rows, cols, hdet⟩ := exists_rank_minor (M.map (eval x))
  let p : GeometricPolynomial n := (M.submatrix rows cols).det
  have hpx : eval x p ≠ 0 := by
    simpa only [p, RingHom.map_det] using hdet
  have hex : ∃ y ∈ O, eval y p ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hp : p ∈ vanishingIdeal GeometricField O := hn
    exact hpx ((hdense ▸ hx) p hp)
  obtain ⟨y, hy, hp⟩ := hex
  refine ⟨y, hy, minor_size_le_rank _ rows cols ?_⟩
  simpa only [p, RingHom.map_det] using hp

theorem rank_add_ker {n c : ℕ} (A : Matrix (Fin c) (Fin n) GeometricField) :
    A.rank + finrank GeometricField (LinearMap.ker A.mulVecLin) = n := by
  simpa using A.mulVecLin.finrank_range_add_finrank_ker

def stackMatrix {K α β γ : Type*} (A : Matrix α γ K) (B : Matrix β γ K) :
    Matrix (α ⊕ β) γ K := Sum.elim A B

@[simp] theorem stackMatrix_map {K L α β γ : Type*}
    (A : Matrix α γ K) (B : Matrix β γ K) (f : K → L) :
    (stackMatrix A B).map f = stackMatrix (A.map f) (B.map f) := by
  ext (i | i) j <;> rfl

theorem stackMatrix_mulVec {K α β γ : Type*} [Field K] [Fintype γ]
    (A : Matrix α γ K) (B : Matrix β γ K) (v : γ → K) :
    (stackMatrix A B).mulVec v = Sum.elim (A.mulVec v) (B.mulVec v) := by
  ext (i | i) <;> rfl

theorem rank_fromRows {n c m : ℕ}
    (A : Matrix (Fin c) (Fin n) GeometricField)
    (B : Matrix (Fin m) (Fin n) GeometricField) :
    (stackMatrix A B).rank = A.rank +
      finrank GeometricField (LinearMap.range
        (B.mulVecLin.domRestrict (LinearMap.ker A.mulVecLin))) := by
  let S := LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin
  have hs : LinearMap.ker (stackMatrix A B).mulVecLin = S := by
    ext v
    change (stackMatrix A B).mulVec v = 0 ↔ A.mulVec v = 0 ∧ B.mulVec v = 0
    rw [stackMatrix_mulVec]
    exact ⟨fun h => ⟨congrArg (fun f => f ∘ Sum.inl) h,
      congrArg (fun f => f ∘ Sum.inr) h⟩,
      fun ⟨ha, hb⟩ => by rw [ha, hb]; ext (i | i) <;> rfl⟩
  have hk : LinearMap.ker (B.mulVecLin.domRestrict (LinearMap.ker A.mulVecLin)) =
      S.comap (LinearMap.ker A.mulVecLin).subtype := by
    ext v
    simp [S]
  have h1 := (stackMatrix A B).mulVecLin.finrank_range_add_finrank_ker
  have h2 := (B.mulVecLin.domRestrict (LinearMap.ker A.mulVecLin)).finrank_range_add_finrank_ker
  rw [hs] at h1
  rw [hk, (Submodule.comapSubtypeEquivOfLe (show S ≤ LinearMap.ker A.mulVecLin from inf_le_left)).finrank_eq] at h2
  have h3 := rank_add_ker A
  change (stackMatrix A B).rank + finrank GeometricField S = _ at h1
  simp only [Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h1
  omega

/-- An embedded tangent dimension cannot be smaller than the variety's
dimension: specialize a maximal minor of a finite Jacobian presentation. -/
theorem tangent_dimension_lower_bound {n m a b : ℕ}
    {Z : Set (GeometricPoint n)} {P : Fin m → GeometricPolynomial n}
    {M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField}
    (G : GenericRankOpen Z P M) (x : GeometricPoint n) (hx : x ∈ Z) :
    affineDimension Z ≤ (finrank GeometricField (affineTangentSpace Z x) : Dimension) := by
  obtain ⟨c, f, _, hf⟩ := exists_tangent_equations Z
  obtain ⟨y, hy, hr⟩ := exists_rank_ge_in_dense (jacobian f) Z G.openSet G.dense x hx
  have hxrank := rank_add_ker (evaluatedMatrix (jacobian f) x)
  have hyrank := rank_add_ker (evaluatedMatrix (jacobian f) y)
  rw [evaluated_jacobian, ← hf x hx] at hxrank
  rw [evaluated_jacobian, ← hf y (G.subset hy), G.smooth y hy] at hyrank
  have ht : G.baseDimension ≤ finrank GeometricField (affineTangentSpace Z x) := by
    change (evaluatedMatrix (jacobian f) x).rank ≤ (evaluatedMatrix (jacobian f) y).rank at hr
    omega
  rw [G.dimension_base]
  exact_mod_cast ht

/-- At a smooth point, a polynomial differential has rank at most the
dimension of its actual image closure. This follows from generic rank and
nonvanishing minors, not from a separately supplied tangent-image theorem. -/
theorem differential_rank_le_image_dimension {n m a b : ℕ}
    {Z : Set (GeometricPoint n)} {P : Fin m → GeometricPolynomial n}
    {M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField}
    (G : GenericRankOpen Z P M) (x : GeometricPoint n) (hx : x ∈ Z)
    (hsmooth : affineDimension Z =
      (finrank GeometricField (affineTangentSpace Z x) : Dimension)) :
    (finrank GeometricField (LinearMap.range
      ((polynomialMapDifferential P x).domRestrict (affineTangentSpace Z x))) : Dimension)
      ≤ affineDimension (geometricClosure (polynomialMap P '' Z)) := by
  obtain ⟨c, f, _, hf⟩ := exists_tangent_equations Z
  obtain ⟨y, hy, hr⟩ := exists_rank_ge_in_dense
    (stackMatrix (jacobian f) (jacobian P)) Z G.openSet G.dense x hx
  have ht : finrank GeometricField (affineTangentSpace Z x) = G.baseDimension := by
    rw [G.dimension_base] at hsmooth
    exact_mod_cast hsmooth.symm
  have hxrank := rank_add_ker (evaluatedMatrix (jacobian f) x)
  have hyrank := rank_add_ker (evaluatedMatrix (jacobian f) y)
  rw [evaluated_jacobian, ← hf x hx, ht] at hxrank
  rw [evaluated_jacobian, ← hf y (G.subset hy), G.smooth y hy] at hyrank
  have hxy : (evaluatedMatrix (jacobian f) x).rank =
      (evaluatedMatrix (jacobian f) y).rank := by omega
  rw [stackMatrix_map, stackMatrix_map] at hr
  change (stackMatrix (evaluatedMatrix (jacobian f) x)
    (evaluatedMatrix (jacobian P) x)).rank ≤
    (stackMatrix (evaluatedMatrix (jacobian f) y)
    (evaluatedMatrix (jacobian P) y)).rank at hr
  rw [rank_fromRows, rank_fromRows, evaluated_jacobian, evaluated_jacobian,
    evaluated_jacobian, evaluated_jacobian, ← hf x hx,
    ← hf y (G.subset hy), G.differential_rank y hy, hxy] at hr
  rw [G.dimension_image]
  exact_mod_cast (Nat.le_of_add_le_add_left hr)

end HessianTheorem11.ReducedTangentRank
