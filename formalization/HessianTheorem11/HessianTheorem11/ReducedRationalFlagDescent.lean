import HessianTheorem11.ReducedGaloisSubspace
import Mathlib.LinearAlgebra.Multilinear.Basis

/-! Rational splitting of an actual Galois-fixed weighted flag. Rational
bases of its steps supply a simultaneous basis by determinant multilinearity.
The original integer weights, with their original indexing, are retained. -/
noncomputable section
namespace HessianTheorem11.ReducedRationalDescent
open Matrix Module RationalDescent

theorem rationalFlag_stable {n : ℕ} (f : WeightFrame GeometricField n)
    (hf : f.RationalFlag) (a : ℤ)
    (σ : GeometricField ≃ₐ[ℚ] GeometricField) (x : GeometricPoint n)
    (hx : x ∈ f.flag a) : (fun i => σ (x i)) ∈ f.flag a := by
  rw [← congrFun (hf σ) a]
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i,hi,rfl⟩ := hx
      exact Submodule.subset_span ⟨i,hi,rfl⟩
  | zero =>
      simpa only [Pi.zero_apply, map_zero] using
        ((f.conjugate σ.toRingEquiv).flag a).zero_mem
  | add x y hx hy hix hiy =>
      simpa only [map_add, Pi.add_apply] using
        ((f.conjugate σ.toRingEquiv).flag a).add_mem hix hiy
  | smul c x hx hi =>
      simpa only [Pi.smul_apply, smul_eq_mul, map_mul] using
        ((f.conjugate σ.toRingEquiv).flag a).smul_mem (σ c) hi

theorem weightFlag_finrank {K : Type*} [Field K] {n : ℕ}
    (B : Matrix (Fin n) (Fin n) K) (hB : Function.Injective B.mulVec)
    (w : Fin n → ℤ) (a : ℤ) :
    finrank K (weightFlag B w a) = Fintype.card {i : Fin n // w i ≤ a} := by
  classical
  have hs : {v | ∃ i, w i ≤ a ∧ v = fun j => B j i} =
      Set.range (fun i : {i : Fin n // w i ≤ a} => B.col i.val) := by
    ext v
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,hi⟩,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨i.val,i.property,rfl⟩
  have hli := Matrix.linearIndependent_cols_iff_isUnit.mpr
    (Matrix.mulVec_injective_iff_isUnit.mp hB)
  unfold weightFlag
  rw [hs]
  exact finrank_span_eq_card (hli.comp Subtype.val Subtype.val_injective)

theorem weightFlag_mono {K : Type*} [Field K] {n : ℕ}
    (B : Matrix (Fin n) (Fin n) K) (w : Fin n → ℤ) : Monotone (weightFlag B w) := by
  intro a b hab
  apply Submodule.span_mono
  rintro x ⟨i,hi,hx⟩
  exact ⟨i,hi.trans hab,hx⟩

theorem exists_rational_flag_frame {n : ℕ}
    (f : WeightFrame GeometricField n) (hf : f.RationalFlag) :
    ∃ B : Matrix (Fin n) (Fin n) ℚ,
      Function.Injective B.mulVec ∧
      Function.Injective (B.map (algebraMap ℚ GeometricField)).mulVec ∧
      ∀ i, (fun j => algebraMap ℚ GeometricField (B j i)) ∈ f.flag (f.weight i) := by
  classical
  let T : Fin n → Submodule GeometricField (GeometricPoint n) :=
    fun i => f.flag (f.weight i)
  have hb (i : Fin n) := invariant_subspace_rational_basis (T i)
    (fun σ x hx => rationalFlag_stable f hf (f.weight i) σ x hx)
  choose b hb using hb
  choose q hq using hb
  let D : MultilinearMap GeometricField (fun i => T i) GeometricField :=
    Matrix.detRowAlternating.toMultilinearMap.compLinearMap (fun i => (T i).subtype)
  have hfdet : f.matrix.det ≠ 0 := isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp f.injective))
  have hD : D ≠ 0 := by
    intro hz
    let v : ∀ i, T i := fun i =>
      ⟨fun j => f.matrix j i, Submodule.subset_span ⟨i,le_rfl,rfl⟩⟩
    have he := congrArg (fun E : MultilinearMap GeometricField (fun i => T i) GeometricField => E v) hz
    change f.matrix.transpose.det = 0 at he
    exact hfdet ((Matrix.det_transpose f.matrix).symm.trans he)
  obtain ⟨v,hv⟩ : ∃ v : ∀ i, Fin (finrank GeometricField (T i)),
      D (fun i => b i (v i)) ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hD
    apply Module.Basis.ext_multilinear b
    intro v
    simpa using hn v
  let B : Matrix (Fin n) (Fin n) ℚ := fun j i => q i (v i) j
  have hBmap : B.map (algebraMap ℚ GeometricField) =
      Matrix.transpose (fun i j => (b i (v i)).val j) := by
    ext i j
    exact hq j (v j) i
  have hdet : (B.map (algebraMap ℚ GeometricField)).det ≠ 0 := by
    rw [hBmap, Matrix.det_transpose]
    exact hv
  have hdetQ : B.det ≠ 0 := by
    intro hz
    apply hdet
    change ((algebraMap ℚ GeometricField).mapMatrix B).det = 0
    rw [← RingHom.map_det, hz, map_zero]
  refine ⟨B, Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdetQ)),
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)), ?_⟩
  intro i
  have he : (fun j => algebraMap ℚ GeometricField (B j i)) = (b i (v i)).val := by
    ext j
    exact hq i (v i) j
  rw [he]
  exact (b i (v i)).property

/-- The full formerly external rational weighted-flag descent package. -/
theorem rationalFlagDescent : TextbookRationalFlagDescent where
  split f hf := by
    obtain ⟨B,hB,hBG,hmem⟩ := exists_rational_flag_frame f hf
    refine ⟨⟨B,hB,f.weight,f.sum_zero⟩,rfl,?_⟩
    funext a
    change weightFlag (B.map (algebraMap ℚ GeometricField)) f.weight a =
      weightFlag f.matrix f.weight a
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.mpr
      rintro x ⟨i,hi,rfl⟩
      exact weightFlag_mono f.matrix f.weight hi (hmem i)
    · rw [weightFlag_finrank _ hBG, weightFlag_finrank _ f.injective]

end HessianTheorem11.ReducedRationalDescent
