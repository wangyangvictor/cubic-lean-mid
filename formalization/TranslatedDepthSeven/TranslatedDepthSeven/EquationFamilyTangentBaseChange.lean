import TranslatedDepthSeven.EquationFamilyProjectiveTangentSpace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Base change for explicit equation-family tangent spaces

This file extends the literal rational Jacobian of a finite family of
integral equations to an arbitrary field over `ℚ`.  It proves directly,
using selected minors, that matrix rank is unchanged by a field extension.
Consequently the dimension of the displayed tangent kernel is independent
of the characteristic-zero field in which it is computed.

The last group of results identifies the matrix definition with the usual
linearization formula
`z ↦ (∑ᵢ (∂f/∂Xᵢ)(h) zᵢ)ₑ`.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped BigOperators

open Finset MvPolynomial Matrix

namespace TangentBaseChange

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- From `k` independent rows over an arbitrary field, select `k`
coordinates giving a nonsingular square minor. -/
theorem exists_selectedMinor_ne_zero_of_linearIndependent_rows
    {k N : ℕ} (A : Matrix (Fin k) (Fin N) F)
    (hA : LinearIndependent F A.row) :
    ∃ cols : Fin k → Fin N, Function.Injective cols ∧
      (A.submatrix id cols).det ≠ 0 := by
  have hrank : A.rank = k := by
    exact hA.rank_matrix.trans (Fintype.card_fin k)
  have hfinrank : Module.finrank F
      (Submodule.span F (Set.range A.col)) = k := by
    rw [← Matrix.rank_eq_finrank_span_cols, hrank]
  obtain ⟨f, hfmem, _, hfindep⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq F (Set.range A.col)
  let e : Fin k ≃ Fin (Module.finrank F
      (Submodule.span F (Set.range A.col))) :=
    Equiv.cast (congrArg Fin hfinrank.symm)
  let f' : Fin k → (Fin k → F) := fun i ↦ f (e i)
  have hf'mem : ∀ i, f' i ∈ Set.range A.col := fun i ↦ hfmem (e i)
  let cols : Fin k → Fin N := fun i ↦ Classical.choose (hf'mem i)
  have hcols : ∀ i, A.col (cols i) = f' i :=
    fun i ↦ Classical.choose_spec (hf'mem i)
  have hf'indep : LinearIndependent F f' := hfindep.comp e e.injective
  have hcolsInj : Function.Injective cols := by
    intro i j hij
    apply hf'indep.injective
    rw [← hcols i, ← hcols j, hij]
  refine ⟨cols, hcolsInj, ?_⟩
  have hminorCols : LinearIndependent F (A.submatrix id cols).col := by
    have he : LinearIndependent F ((A.col ∘ cols)) := by
      have hrewrite : (A.col ∘ cols) = f' := by
        funext i
        exact hcols i
      rw [hrewrite]
      exact hf'indep
    simpa only [Matrix.col, Matrix.submatrix, id_eq, Function.comp_apply]
      using he
  have hunit : IsUnit (A.submatrix id cols) :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hminorCols
  exact ((A.submatrix id cols).isUnit_iff_isUnit_det.mp hunit).ne_zero

/-- If a displayed `k × k` minor is nonzero, then the ambient row span has
dimension at least `k`. -/
theorem le_rank_of_selectedMinor_ne_zero
    {I : Type*} [Fintype I] {N k : ℕ} (A : Matrix I (Fin N) F)
    (rows : Fin k → I) (cols : Fin k → Fin N)
    (hdet : (Matrix.of (fun i j ↦ A (rows i) (cols j))).det ≠ 0) :
    k ≤ A.rank := by
  let B : Matrix (Fin k) (Fin k) F :=
    Matrix.of (fun i j ↦ A (rows i) (cols j))
  have hminor : LinearIndependent F B.row :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet
  let restrictCols : (Fin N → F) →ₗ[F] (Fin k → F) :=
    LinearMap.funLeft F F cols
  have hselected : LinearIndependent F (fun i ↦ A.row (rows i)) := by
    apply LinearIndependent.of_comp restrictCols
    have heq : restrictCols ∘ (fun i ↦ A.row (rows i)) = B.row := by
      funext i j
      rfl
    rw [heq]
    exact hminor
  have hspan :
      Submodule.span F (Set.range fun i ↦ A.row (rows i)) ≤
        Submodule.span F (Set.range A.row) := by
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨rows i, rfl⟩
  calc
    k = Module.finrank F
        (Submodule.span F (Set.range fun i ↦ A.row (rows i))) := by
      simpa only [Fintype.card_fin, Set.finrank] using
        (linearIndependent_iff_card_eq_finrank_span.mp hselected)
    _ ≤ Module.finrank F (Submodule.span F (Set.range A.row)) :=
      Submodule.finrank_mono hspan
    _ = A.rank := (Matrix.rank_eq_finrank_span_row A).symm

/-- If the ambient matrix has rank below `k`, every displayed `k × k`
minor vanishes. -/
theorem selectedMinor_eq_zero_of_rank_lt
    {I : Type*} [Fintype I] {N k : ℕ} (A : Matrix I (Fin N) F)
    (hrank : A.rank < k) (rows : Fin k → I)
    (cols : Fin k → Fin N) :
    (Matrix.of (fun i j ↦ A (rows i) (cols j))).det = 0 := by
  by_contra hdet
  exact (not_le_of_gt hrank) (le_rank_of_selectedMinor_ne_zero A rows cols hdet)

/-- If a family spans a space of dimension at least `k`, then `k` members
and `k` coordinates determine a nonzero minor. -/
theorem exists_nonzero_minor_of_finrank_span_ge
    {k N : ℕ} {I : Type*} (v : I → Fin N → F)
    (hlarge : k ≤ Module.finrank F
      (Submodule.span F (Set.range v))) :
    ∃ rows : Fin k → I, ∃ cols : Fin k → Fin N,
      Function.Injective rows ∧ Function.Injective cols ∧
      Matrix.det (Matrix.of (fun i j ↦ v (rows i) (cols j))) ≠ 0 := by
  obtain ⟨f, hfmem, _, hfindep⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq F (Set.range v)
  let inc : Fin k → Fin (Module.finrank F
      (Submodule.span F (Set.range v))) := Fin.castLE hlarge
  let f' : Fin k → (Fin N → F) := fun i ↦ f (inc i)
  have hf'mem : ∀ i, f' i ∈ Set.range v := fun i ↦ hfmem (inc i)
  let rows : Fin k → I := fun i ↦ Classical.choose (hf'mem i)
  have hrows : ∀ i, v (rows i) = f' i :=
    fun i ↦ Classical.choose_spec (hf'mem i)
  have hf'indep : LinearIndependent F f' :=
    hfindep.comp inc (Fin.castLE_injective hlarge)
  have hrowsInj : Function.Injective rows := by
    intro i j hij
    apply hf'indep.injective
    rw [← hrows i, ← hrows j, hij]
  let A : Matrix (Fin k) (Fin N) F := fun i j ↦ v (rows i) j
  have hA : LinearIndependent F A.row := by
    have hArows : A.row = f' := by
      funext i j
      simp [A, hrows]
    rw [hArows]
    exact hf'indep
  obtain ⟨cols, hcolsInj, hminor⟩ :=
    exists_selectedMinor_ne_zero_of_linearIndependent_rows A hA
  refine ⟨rows, cols, hrowsInj, hcolsInj, ?_⟩
  simpa [A] using hminor

/-- Vanishing of every selected `k`-minor bounds the dimension of the row
span by `k-1`, over an arbitrary field. -/
theorem finrank_span_lt_of_all_minors_zero
    {k N : ℕ} {I : Type*} (v : I → Fin N → F)
    (hzero : ∀ (rows : Fin k → I) (cols : Fin k → Fin N),
      Matrix.det (Matrix.of (fun i j ↦ v (rows i) (cols j))) = 0) :
    Module.finrank F (Submodule.span F (Set.range v)) < k := by
  by_contra hnot
  have hlarge : k ≤ Module.finrank F
      (Submodule.span F (Set.range v)) := Nat.le_of_not_gt hnot
  obtain ⟨rows, cols, _, _, hminor⟩ :=
    exists_nonzero_minor_of_finrank_span_ge v hlarge
  exact hminor (hzero rows cols)

/-- A finite matrix has the same rank after extension from one field to
another.  The proof is purely determinantal and therefore makes no choice of
row-reduction algorithm. -/
theorem rank_map_algebraMap {I : Type*} [Fintype I]
    {N : ℕ} (A : Matrix I (Fin N) F) :
    (A.map (algebraMap F K)).rank = A.rank := by
  let r := A.rank
  have hrowrank : Module.finrank F
      (Submodule.span F (Set.range A.row)) = r := by
    exact (Matrix.rank_eq_finrank_span_row A).symm
  obtain ⟨rows, cols, _, _, hminor⟩ :=
    exists_nonzero_minor_of_finrank_span_ge (v := A.row) (k := r)
      (by rw [hrowrank])
  have hminorK :
      Matrix.det
        (Matrix.of (fun i j ↦
          algebraMap F K (A (rows i) (cols j)))) ≠ 0 := by
    change ((algebraMap F K).mapMatrix
      (Matrix.of (fun i j ↦ A (rows i) (cols j)))).det ≠ 0
    rw [← (algebraMap F K).map_det]
    simpa [Matrix.row] using
      (FaithfulSMul.algebraMap_injective F K).ne hminor
  have hlower : r ≤ (A.map (algebraMap F K)).rank := by
    exact le_rank_of_selectedMinor_ne_zero
      (A.map (algebraMap F K)) rows cols hminorK
  have hzeroK :
      ∀ (rows' : Fin (r + 1) → I) (cols' : Fin (r + 1) → Fin N),
        Matrix.det (Matrix.of (fun i j ↦
          (A.map (algebraMap F K)) (rows' i) (cols' j))) = 0 := by
    intro rows' cols'
    rw [show Matrix.of (fun i j ↦
          (A.map (algebraMap F K)) (rows' i) (cols' j)) =
        (Matrix.of (fun i j ↦ A (rows' i) (cols' j))).map
          (algebraMap F K) by rfl]
    change ((algebraMap F K).mapMatrix
      (Matrix.of (fun i j ↦ A (rows' i) (cols' j)))).det = 0
    rw [← (algebraMap F K).map_det]
    rw [selectedMinor_eq_zero_of_rank_lt A (Nat.lt_succ_self r) rows' cols', map_zero]
  have hupper' :
      Module.finrank K
          (Submodule.span K (Set.range (A.map (algebraMap F K)).row)) <
        r + 1 :=
    finrank_span_lt_of_all_minors_zero _ hzeroK
  have hupper : (A.map (algebraMap F K)).rank ≤ r := by
    rw [Matrix.rank_eq_finrank_span_row]
    omega
  exact le_antisymm hupper hlower

end TangentBaseChange

/-! ## The extended Jacobian and its standard linearization -/

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- The displayed rational Jacobian after entrywise scalar extension to
`K`. -/
def equationFamilyJacobianMatrixOver {n : ℕ}
    (equations : Finset (MvPolynomial (Fin n) ℤ)) (h : IntVector n) :
    Matrix {f // f ∈ equations} (Fin n) K :=
  (equationFamilyRationalJacobianMatrix equations h).map (algebraMap ℚ K)

/-- The extended Jacobian as a `K`-linear map. -/
def equationFamilyJacobianLinearMapOver {n : ℕ}
    (equations : Finset (MvPolynomial (Fin n) ℤ)) (h : IntVector n) :
    (Fin n → K) →ₗ[K] ({f // f ∈ equations} → K) :=
  (equationFamilyJacobianMatrixOver (K := K) equations h).mulVecLin

/-- The displayed tangent kernel over `K`. -/
def equationFamilyTangentKernelOver {n : ℕ}
    (equations : Finset (MvPolynomial (Fin n) ℤ)) (h : IntVector n) :
    Submodule K (Fin n → K) :=
  LinearMap.ker (equationFamilyJacobianLinearMapOver (K := K) equations h)

/-- The usual derivation-linearization formula for the common equations,
written directly after coefficient and point extension to `K`. -/
def equationFamilyDerivationLinearizationOver {n : ℕ}
    (equations : Finset (MvPolynomial (Fin n) ℤ)) (h : IntVector n) :
    (Fin n → K) →ₗ[K] ({f // f ∈ equations} → K) where
  toFun z f := ∑ i,
    MvPolynomial.eval (fun j ↦ algebraMap ℚ K (h j : ℚ))
      (MvPolynomial.pderiv i
        (MvPolynomial.map (Int.castRingHom K) f.1)) * z i
  map_add' z w := by
    funext f
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a z := by
    funext f
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Each extended Jacobian entry is exactly the corresponding partial
derivative of the coefficient-extended equation at the extended point. -/
theorem equationFamilyJacobianMatrixOver_apply {n : ℕ}
    (equations : Finset (MvPolynomial (Fin n) ℤ)) (h : IntVector n)
    (f : {f // f ∈ equations}) (i : Fin n) :
    equationFamilyJacobianMatrixOver (K := K) equations h f i =
      MvPolynomial.eval (fun j ↦ algebraMap ℚ K (h j : ℚ))
        (MvPolynomial.pderiv i
          (MvPolynomial.map (Int.castRingHom K) f.1)) := by
  have hpoint :
      (fun j ↦ algebraMap ℚ K (h j : ℚ)) = (fun j ↦ (h j : K)) := by
    funext j
    norm_num
  rw [hpoint, MvPolynomial.pderiv_map, eval_map_intCast]
  simp [equationFamilyJacobianMatrixOver,
    equationFamilyRationalJacobianMatrix]

/-- The matrix linear map is literally the standard derivation
linearization, not merely isomorphic to it. -/
theorem equationFamilyJacobianLinearMapOver_eq_derivationLinearization
    {n : ℕ} (equations : Finset (MvPolynomial (Fin n) ℤ))
    (h : IntVector n) :
    equationFamilyJacobianLinearMapOver (K := K) equations h =
      equationFamilyDerivationLinearizationOver (K := K) equations h := by
  apply LinearMap.ext
  intro z
  funext f
  change ∑ i, equationFamilyJacobianMatrixOver (K := K) equations h f i * z i = _
  simp only [equationFamilyJacobianMatrixOver_apply,
    equationFamilyDerivationLinearizationOver]
  rfl

/-- Membership in the extended tangent kernel is exactly simultaneous
vanishing of the standard directional derivatives. -/
theorem mem_equationFamilyTangentKernelOver_iff {n : ℕ}
    (equations : Finset (MvPolynomial (Fin n) ℤ)) (h : IntVector n)
    (z : Fin n → K) :
    z ∈ equationFamilyTangentKernelOver (K := K) equations h ↔
      ∀ f : {f // f ∈ equations},
        ∑ i,
          MvPolynomial.eval (fun j ↦ algebraMap ℚ K (h j : ℚ))
            (MvPolynomial.pderiv i
              (MvPolynomial.map (Int.castRingHom K) f.1)) * z i = 0 := by
  rw [equationFamilyTangentKernelOver, LinearMap.mem_ker]
  rw [equationFamilyJacobianLinearMapOver_eq_derivationLinearization]
  constructor
  · intro hz f
    exact congrFun hz f
  · intro hz
    funext f
    exact hz f

/-- The extended displayed Jacobian has exactly the same rank as the
rational one. -/
theorem rank_equationFamilyJacobianMatrixOver {n : ℕ}
    (equations : Finset (MvPolynomial (Fin n) ℤ)) (h : IntVector n) :
    (equationFamilyJacobianMatrixOver (K := K) equations h).rank =
      (equationFamilyRationalJacobianMatrix equations h).rank := by
  exact TangentBaseChange.rank_map_algebraMap
    (K := K) (equationFamilyRationalJacobianMatrix equations h)

/-- Rank--nullity over `K`, combined with rank preservation, gives the same
tangent dimension as over `ℚ`. -/
theorem finrank_equationFamilyTangentKernelOver {n : ℕ}
    (equations : Finset (MvPolynomial (Fin n) ℤ)) (h : IntVector n) :
    Module.finrank K (equationFamilyTangentKernelOver (K := K) equations h) =
      n - (equationFamilyRationalJacobianMatrix equations h).rank := by
  have hrankNullity :=
    LinearMap.finrank_range_add_finrank_ker
      (equationFamilyJacobianLinearMapOver (K := K) equations h)
  have hsum :
      (equationFamilyJacobianMatrixOver (K := K) equations h).rank +
          Module.finrank K
            (equationFamilyTangentKernelOver (K := K) equations h) = n := by
    simpa [equationFamilyJacobianLinearMapOver,
      equationFamilyTangentKernelOver, Matrix.rank] using hrankNullity
  rw [rank_equationFamilyJacobianMatrixOver] at hsum
  omega

/-- A rational vector lies in the rational tangent kernel exactly when its
coordinatewise image lies in the tangent kernel over `K`. -/
theorem algebraMap_mem_equationFamilyTangentKernelOver_iff {n : ℕ}
    (equations : Finset (MvPolynomial (Fin n) ℤ)) (h : IntVector n)
    (z : Fin n → ℚ) :
    (fun i ↦ algebraMap ℚ K (z i)) ∈
        equationFamilyTangentKernelOver (K := K) equations h ↔
      z ∈ equationFamilyRationalTangentKernel equations h := by
  rw [equationFamilyTangentKernelOver, equationFamilyRationalTangentKernel,
    LinearMap.mem_ker, LinearMap.mem_ker]
  constructor
  · intro hz
    funext f
    apply (FaithfulSMul.algebraMap_injective ℚ K)
    have hf :
        (equationFamilyJacobianLinearMapOver (K := K) equations h)
          (fun i ↦ algebraMap ℚ K (z i)) f = 0 := congrFun hz f
    change (∑ i,
      algebraMap ℚ K
        (equationFamilyRationalJacobianMatrix equations h f i) *
          algebraMap ℚ K (z i)) = 0 at hf
    change algebraMap ℚ K
      (∑ i, equationFamilyRationalJacobianMatrix equations h f i * z i) =
        algebraMap ℚ K 0
    rw [map_zero]
    rw [map_sum]
    convert hf using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul]
  · intro hz
    funext f
    have hf :
        (equationFamilyRationalJacobianLinearMap equations h) z f = 0 :=
      congrFun hz f
    change ∑ i,
      algebraMap ℚ K
        (equationFamilyRationalJacobianMatrix equations h f i) *
          algebraMap ℚ K (z i) = 0
    calc
      ∑ i,
          algebraMap ℚ K
            (equationFamilyRationalJacobianMatrix equations h f i) *
            algebraMap ℚ K (z i) =
          algebraMap ℚ K
            (∑ i, equationFamilyRationalJacobianMatrix equations h f i * z i) := by
              rw [map_sum]
              apply Finset.sum_congr rfl
              intro i _
              rw [map_mul]
      _ = algebraMap ℚ K
          ((equationFamilyRationalJacobianLinearMap equations h) z f) := rfl
      _ = 0 := by rw [hf, map_zero]

end

end TranslatedDepthSeven
