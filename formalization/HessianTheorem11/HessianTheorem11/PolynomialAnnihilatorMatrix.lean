import HessianTheorem11.KernelAnnihilatorProjector
import HessianTheorem11.ReducedDeterminantalDifferential

/-! Actual polynomial equations for the successive kernel annihilator on
a maximal-minor chart. No generic geometry is assumed here. -/
noncomputable section
namespace HessianTheorem11.KernelAnnihilatorProjector
open Matrix Module MvPolynomial ReducedDeterminantal

variable {n a b c r : ℕ}

def annihilatorMatrix (M : Matrix (Fin a) (Fin b) GeometricField)
    (N : GeometricPoint b →ₗ[GeometricField] Matrix (Fin c) (Fin b) GeometricField)
    (rows : Fin r → Fin a) (cols : Fin r → Fin b) :
    Matrix (Fin a ⊕ (Fin b × Fin c)) (Fin b) GeometricField :=
  Sum.elim M (fun ji => N ((projector M rows cols).col ji.1) ji.2)

def annihilatorPolynomialMatrix
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
    (N : GeometricPoint b →ₗ[GeometricField] Matrix (Fin c) (Fin b) GeometricField)
    (rows : Fin r → Fin a) (cols : Fin r → Fin b) :
    Matrix (Fin a ⊕ (Fin b × Fin c)) (Fin b) (GeometricPolynomial n) :=
  Sum.elim (pencilPolynomial M)
    (fun ji k => ∑ l, C (N ((Pi.basisFun GeometricField (Fin b)) l) ji.2 k) *
      projector (pencilPolynomial M) rows cols l ji.1)

theorem eval_annihilatorPolynomialMatrix
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
    (N : GeometricPoint b →ₗ[GeometricField] Matrix (Fin c) (Fin b) GeometricField)
    (rows : Fin r → Fin a) (cols : Fin r → Fin b) (x : GeometricPoint n) :
    (annihilatorPolynomialMatrix M N rows cols).map (eval x) =
      annihilatorMatrix (M x) N rows cols := by
  have hp : (pencilPolynomial M).map (eval x) = M x := by
    ext i j
    exact eval_pencilPolynomial M x i j
  have hproj := projector_map (eval x) (pencilPolynomial M) rows cols
  rw [hp] at hproj
  ext i k
  rcases i with i | ⟨j,i⟩
  · exact eval_pencilPolynomial M x i k
  · change eval x (∑ l, C (N ((Pi.basisFun GeometricField (Fin b)) l) i k) *
      projector (pencilPolynomial M) rows cols l j) =
        N ((projector (M x) rows cols).col j) i k
    simp only [eval_sum, eval_mul, eval_C]
    have he (l : Fin b) : eval x (projector (pencilPolynomial M) rows cols l j) =
        projector (M x) rows cols l j := congrFun (congrFun hproj l) j
    simp only [he]
    have h := congrArg (fun z => N z i k)
      ((Pi.basisFun GeometricField (Fin b)).sum_repr ((projector (M x) rows cols).col j))
    simpa only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Pi.basisFun_repr, Matrix.col_apply, mul_comm] using h

theorem ker_annihilatorMatrix
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
    (N : GeometricPoint b →ₗ[GeometricField] Matrix (Fin c) (Fin b) GeometricField)
    (rows : Fin r → Fin a) (cols : Fin r → Fin b) (x : GeometricPoint n)
    (hdet : ((M x).submatrix rows cols).det ≠ 0) (hrank : (M x).rank ≤ r) :
    LinearMap.ker (annihilatorMatrix (M x) N rows cols).mulVecLin =
      kernelAnnihilator M N x := by
  ext v
  constructor
  · intro hv
    have hm : (M x).mulVec v = 0 := by
      ext i
      exact congrFun hv (Sum.inl i)
    refine ⟨hm, ?_⟩
    apply (Submodule.mem_iInf _).mpr
    intro u
    change (N u).mulVec v = 0
    apply (successive_annihilator_iff_columns (M x) N rows cols hdet hrank v).mpr ?_
      u u.property
    intro j
    ext i
    exact congrFun hv (Sum.inr (j,i))
  · intro hv
    have hcols : ∀ j, (N ((projector (M x) rows cols).col j)).mulVec v = 0 := by
      apply (successive_annihilator_iff_columns (M x) N rows cols hdet hrank v).mp
      intro u hu
      exact (Submodule.mem_iInf _).mp hv.2 ⟨u,hu⟩
    change (annihilatorMatrix (M x) N rows cols).mulVec v = 0
    ext i
    rcases i with i | ⟨j,i⟩
    · exact congrFun hv.1 i
    · exact congrFun (hcols j) i

end HessianTheorem11.KernelAnnihilatorProjector
