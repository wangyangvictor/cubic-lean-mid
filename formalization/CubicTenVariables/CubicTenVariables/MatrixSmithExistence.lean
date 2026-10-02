import CubicTenVariables.MatrixSmithKernel
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Matrix.Basis

/-! Actual source bases lifting Smith bases of an integral matrix image.
No injectivity of the matrix is required: its kernel supplies the remaining
basis vectors. The construction takes place over the PID ℤ, never over a
residue ring. -/

noncomputable section
namespace CubicTenVariables.MatrixSmithExistence
open Module Matrix

/-- A split surjection onto the actual image identifies the original module
with image × kernel. The forward map is literally `(u,v) ↦ g u + v`. -/
def rangeKernelEquiv {n : ℕ} (f : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ))
    (g : LinearMap.range f →ₗ[ℤ] (Fin n → ℤ))
    (hg : f.rangeRestrict.comp g = LinearMap.id) :
    (LinearMap.range f × LinearMap.ker f) ≃ₗ[ℤ] (Fin n → ℤ) := by
  have hfg (u : LinearMap.range f) : f (g u) = u :=
    congrArg Subtype.val (LinearMap.congr_fun hg u)
  refine LinearEquiv.ofBijective (g.coprod (LinearMap.ker f).subtype) ⟨?_, ?_⟩
  · rintro ⟨u, v⟩ ⟨u', v'⟩ he
    have hu : u = u' := by
      apply Subtype.ext
      have hh := congrArg f he
      simpa only [LinearMap.coprod_apply, Submodule.subtype_apply, map_add, hfg, LinearMap.map_coe_ker,
        add_zero] using hh
    subst u'
    have hv : v = v' := by
      apply Subtype.ext
      exact add_left_cancel he
    exact Prod.ext rfl hv
  · intro x
    let u : LinearMap.range f := f.rangeRestrict x
    have hv : x - g u ∈ LinearMap.ker f := by
      change f (x - g u) = 0
      rw [map_sub, hfg]
      exact sub_self _
    refine ⟨(u, ⟨x - g u, hv⟩), ?_⟩
    change g u + (x - g u) = x
    abel

@[simp] theorem rangeKernelEquiv_apply {n : ℕ}
    (f : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ))
    (g : LinearMap.range f →ₗ[ℤ] (Fin n → ℤ))
    (hg : f.rangeRestrict.comp g = LinearMap.id)
    (u : LinearMap.range f) (v : LinearMap.ker f) :
    rangeKernelEquiv f g hg (u,v) = g u + v := rfl

theorem map_rangeKernelEquiv {n : ℕ}
    (f : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ))
    (g : LinearMap.range f →ₗ[ℤ] (Fin n → ℤ))
    (hg : f.rangeRestrict.comp g = LinearMap.id)
    (u : LinearMap.range f) (v : LinearMap.ker f) :
    f (rangeKernelEquiv f g hg (u,v)) = u := by
  rw [rangeKernelEquiv_apply, map_add, LinearMap.map_coe_ker, add_zero]
  exact congrArg Subtype.val (LinearMap.congr_fun hg u)

/-- An actual basis of the source with one vector for each nonzero Smith
image direction and the rest in the matrix kernel. This includes the zero
matrix and zero-dimensional case. -/
theorem exists_source_smith_basis {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    ∃ (r k : ℕ) (hrk : r + k = n)
      (b : Basis (Fin n) ℤ (Fin n → ℤ))
      (c : Basis (Fin r ⊕ Fin k) ℤ (Fin n → ℤ))
      (f : Fin r ↪ Fin n) (d : Fin r → ℤ),
      (∀ i, d i ≠ 0) ∧
      (∀ i, B.mulVec (c (Sum.inl i)) = d i • b (f i)) ∧
      (∀ j, B.mulVec (c (Sum.inr j)) = 0) := by
  classical
  obtain ⟨r, hr, b, c, emb, d, hd, hsmith⟩ := MatrixSmithKernel.exists_image_smith_data B
  let f := B.mulVecLin
  letI : Module.Free ℤ (LinearMap.range f) := Module.Free.of_basis c
  obtain ⟨g, hg⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  obtain ⟨k, bk⟩ := (LinearMap.ker f).basisOfPid (Pi.basisFun ℤ (Fin n))
  let e := rangeKernelEquiv f g hg
  let bc := (c.prod bk).map e
  have hrk : r + k = n := by
    have h := bc.indexEquiv (Pi.basisFun ℤ (Fin n))
    simpa using Fintype.card_congr h
  refine ⟨r, k, hrk, b, bc, emb, d, hd, ?_, ?_⟩
  · intro i
    change f (e ((c.prod bk) (Sum.inl i))) = _
    have hh := map_rangeKernelEquiv f g hg (c i) 0
    simpa only [Basis.prod_apply, Sum.elim_inl, LinearMap.inl_apply, e] using
      hh.trans (hsmith i)
  · intro j
    change f (e ((c.prod bk) (Sum.inr j))) = _
    have hh := map_rangeKernelEquiv f g hg 0 (bk j)
    simpa only [Basis.prod_apply, Sum.elim_inr, LinearMap.inr_apply, e, Submodule.coe_zero] using hh

/-- Extend the indexing embedding of nonzero image directions by the
remaining kernel indices. No ordering of the diagonal factors is required. -/
theorem exists_index_extension {r k n : ℕ} (hrk : r + k = n)
    (f : Fin r ↪ Fin n) :
    ∃ e : (Fin r ⊕ Fin k) ≃ Fin n, ∀ i, e (Sum.inl i) = f i := by
  classical
  let er : Fin r ≃ Set.range f := Equiv.ofInjective f f.injective
  have hcr : Fintype.card (Set.range f) = r := by
    simpa using (Fintype.card_congr er).symm
  have hcc : Fintype.card {i : Fin n // i ∉ Set.range f} = k := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, hcr, ← hrk]
    exact Nat.add_sub_cancel_left r k
  let ec : Fin k ≃ {i : Fin n // i ∉ Set.range f} :=
    Fintype.equivOfCardEq (by simpa using hcc.symm)
  refine ⟨(Equiv.sumCongr er ec).trans (Equiv.Set.sumCompl (Set.range f)), ?_⟩
  intro i
  rfl

/-- Actual integral bases in which an arbitrary integer matrix is diagonal.
The coefficients may be zero. No full-rank hypothesis is used. -/
theorem exists_diagonal_bases {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    ∃ (b c : Basis (Fin n) ℤ (Fin n → ℤ)) (d : Fin n → ℤ),
      ∀ j, B.mulVec (c j) = d j • b j := by
  classical
  obtain ⟨r, k, hrk, b, c, f, d, hd, hi, hz⟩ := exists_source_smith_basis B
  obtain ⟨e, he⟩ := exists_index_extension hrk f
  let D : Fin n → ℤ := fun j => Sum.elim d (fun _ => 0) (e.symm j)
  refine ⟨b, c.reindex e, D, ?_⟩
  intro j
  obtain ⟨j, rfl⟩ := e.surjective j
  cases j with
  | inl i =>
    simp only [Basis.reindex_apply, Equiv.symm_apply_apply, D, Sum.elim_inl]
    rw [he i]
    exact hi i
  | inr l => simpa [Basis.reindex_apply, D] using hz l

/-- Every integer matrix admits actual integral unimodular row and column
changes making it diagonal, including singular and zero matrices.
The diagonal is not asserted to have its factors ordered by divisibility. -/
theorem exists_integer_diagonalization {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    ∃ (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ) (d : Fin n → ℤ),
      (U : Matrix (Fin n) (Fin n) ℤ) * B * V = Matrix.diagonal d := by
  classical
  obtain ⟨b, c, d, hd⟩ := exists_diagonal_bases B
  let std := Pi.basisFun ℤ (Fin n)
  let U : (Matrix (Fin n) (Fin n) ℤ)ˣ :=
    ⟨b.toMatrix std, std.toMatrix b, b.toMatrix_mul_toMatrix_flip std,
      std.toMatrix_mul_toMatrix_flip b⟩
  let V : (Matrix (Fin n) (Fin n) ℤ)ˣ :=
    ⟨std.toMatrix c, c.toMatrix std, std.toMatrix_mul_toMatrix_flip c,
      c.toMatrix_mul_toMatrix_flip std⟩
  refine ⟨U, V, d, ?_⟩
  change b.toMatrix std * B * std.toMatrix c = Matrix.diagonal d
  have hB : LinearMap.toMatrix std std B.mulVecLin = B := by
    simpa only [std, Matrix.toLin_eq_toLin'] using LinearMap.toMatrix_toLin std std B
  rw [← hB, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
  ext i j
  rw [LinearMap.toMatrix_apply]
  change b.repr (B.mulVec (c j)) i = _
  rw [hd j, map_smul]
  simp only [Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst j
    simp [Matrix.diagonal_apply]
  · simp [Matrix.diagonal_apply, hij, Ne.symm hij]

end CubicTenVariables.MatrixSmithExistence
