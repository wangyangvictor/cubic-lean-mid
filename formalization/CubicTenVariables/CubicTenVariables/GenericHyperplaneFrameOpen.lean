import CubicTenVariables.GenericReducedProjectiveHyperplane
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! A nonempty polynomial open in full-frame space meets the literal full
parameter-generic hyperplane. The frame is constructed by eliminating its
first row; no compatibility or generic-frame witness is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace CubicTenVariables.GenericHyperplaneFrameOpen
open MvPolynomial
open scoped Matrix

variable {k : Type*} [Field k] {n : ℕ}

/-- A division-free frame annihilated by the normal `u`. -/
def chartFrame {R : Type*} [CommRing R] (u : Fin (n+1) → R)
    (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n+1)) (Fin n) R :=
  Fin.cons (fun j => -(∑ i, u i.succ * M i j)) (fun i j => u 0 * M i j)

/-- Pullback of a frame polynomial along the literal elimination frame. -/
def pullback (Δ : MvPolynomial (Fin (n+1) × Fin n) k) :
    MvPolynomial (Fin n × Fin n) (MvPolynomial (Fin (n+1)) k) :=
  eval₂Hom ((C : MvPolynomial (Fin (n+1)) k →+*
      MvPolynomial (Fin n × Fin n) (MvPolynomial (Fin (n+1)) k)).comp C)
    (fun ij : Fin (n+1) × Fin n => chartFrame (fun i => C (X i)) (fun i j => X (i,j)) ij.1 ij.2) Δ

theorem eval_pullback {R : Type*} [CommRing R]
    (φ : MvPolynomial (Fin (n+1)) k →+* R)
    (M : Matrix (Fin n) (Fin n) R)
    (Δ : MvPolynomial (Fin (n+1) × Fin n) k) :
    eval₂Hom φ (fun ij => M ij.1 ij.2) (pullback Δ) =
      eval₂Hom (φ.comp C) (fun ij => chartFrame (fun i => φ (X i)) M ij.1 ij.2) Δ := by
  have he : (eval₂Hom φ (fun ij : Fin n × Fin n => M ij.1 ij.2)).comp
      (eval₂Hom ((C : MvPolynomial (Fin (n+1)) k →+*
        MvPolynomial (Fin n × Fin n) (MvPolynomial (Fin (n+1)) k)).comp C)
        (fun ij : Fin (n+1) × Fin n =>
        chartFrame (fun i => C (X i)) (fun i j => X (i,j)) ij.1 ij.2)) =
      eval₂Hom (φ.comp C) (fun ij => chartFrame (fun i => φ (X i)) M ij.1 ij.2) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro ij
      rcases ij with ⟨i,j⟩
      refine Fin.cases ?_ (fun i => ?_) i <;>
        simp [chartFrame, map_sum]
  exact congrArg (fun f => f Δ) he

private theorem exists_eval_ne_zero [Infinite k] {σ : Type*}
    (P : MvPolynomial σ k) (hP : P ≠ 0) : ∃ x, eval x P ≠ 0 := by
  by_contra! h
  apply hP
  apply MvPolynomial.funext
  intro x
  simpa only [map_zero] using h x

/-- The lower square minor is a nonzero polynomial. -/
theorem lowerMinor_ne_zero :
    Matrix.det (fun i j : Fin n => (X (i.succ,j) : MvPolynomial (Fin (n+1) × Fin n) k)) ≠ 0 := by
  intro h
  let B : Matrix (Fin (n+1)) (Fin n) k := Fin.cons 0 (1 : Matrix (Fin n) (Fin n) k)
  have he := congrArg (eval (fun ij => B ij.1 ij.2)) h
  rw [map_zero, RingHom.map_det] at he
  have hm : (fun i j : Fin n =>
      eval (fun ij => B ij.1 ij.2) (X (i.succ,j))) = (1 : Matrix (Fin n) (Fin n) k) := by
    ext i j
    simp [B]
  change Matrix.det (fun i j : Fin n => eval (fun ij => B ij.1 ij.2) (X (i.succ,j))) = 0 at he
  rw [hm, Matrix.det_one] at he
  exact one_ne_zero he

/-- Elimination dominates the full-frame space, over an infinite field. -/
theorem pullback_ne_zero [Infinite k]
    (Δ : MvPolynomial (Fin (n+1) × Fin n) k) (hΔ : Δ ≠ 0) :
    pullback Δ ≠ 0 := by
  intro hz
  let D : MvPolynomial (Fin (n+1) × Fin n) k :=
    Matrix.det (fun i j : Fin n => X (i.succ,j))
  have hprod : Δ * D ≠ 0 := mul_ne_zero hΔ lowerMinor_ne_zero
  obtain ⟨b,hb⟩ := exists_eval_ne_zero (Δ * D) hprod
  have hb' : eval b Δ ≠ 0 ∧ eval b D ≠ 0 :=
    mul_ne_zero_iff.mp (by simpa only [map_mul] using hb)
  let M : Matrix (Fin n) (Fin n) k := fun i j => b (i.succ,j)
  have hM : M.det ≠ 0 := by
    have he : eval b D = M.det := by
      dsimp only [D]
      rw [RingHom.map_det]
      congr 1
      ext i j
      simp [M]
    exact he ▸ hb'.2
  have hsurj : Function.Surjective M.vecMul :=
    Matrix.vecMul_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hM))
  obtain ⟨a,ha⟩ := hsurj (fun j => -b (0,j))
  let u : Fin (n+1) → k := Fin.cons 1 a
  have hframe : chartFrame u M = fun i j => b (i,j) := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i
    · have hh := congrFun ha j
      simp only [Matrix.vecMul, dotProduct] at hh
      simpa [chartFrame, u, hh] using congrArg Neg.neg hh
    · simp [chartFrame, u, M]
  have he := eval_pullback (eval u) M Δ
  have hc : (eval u : MvPolynomial (Fin (n+1)) k →+* k).comp C = RingHom.id k := by
    ext a
    simp
  rw [hc] at he
  have hu : (fun i => eval u (X i)) = u := by funext i; simp
  rw [hu, hframe, hz, map_zero] at he
  exact hb'.1 he.symm

/-- A nonzero polynomial open admits a frame in the kernel of the actual
full generic normal. The chosen square matrix may depend on the open. -/
theorem exists_frame_in_generic_hyperplane
    [Infinite k] (L : Type*) [Field L] [Algebra k L]
    [Algebra (GenericReducedProjectiveHyperplane.ParameterRing k n) L]
    [IsScalarTower k (GenericReducedProjectiveHyperplane.ParameterRing k n) L]
    [IsFractionRing (GenericReducedProjectiveHyperplane.ParameterRing k n) L]
    (Δ : MvPolynomial (Fin (n+1) × Fin n) k) (hΔ : Δ ≠ 0) :
    ∃ B : Matrix (Fin (n+1)) (Fin n) L,
      eval₂Hom (algebraMap k L) (fun ij => B ij.1 ij.2) Δ ≠ 0 ∧
      ∀ j, ∑ i, algebraMap (GenericReducedProjectiveHyperplane.ParameterRing k n) L
        (X i) * B i j = 0 := by
  let A := GenericReducedProjectiveHyperplane.ParameterRing k n
  let φ : A →+* L := algebraMap A L
  letI : Infinite L := Infinite.of_injective (algebraMap k L) (algebraMap k L).injective
  have hP : map φ (pullback Δ) ≠ 0 := by
    exact fun hz => pullback_ne_zero Δ hΔ
      ((map_injective φ (IsFractionRing.injective A L)) (by simpa using hz))
  obtain ⟨m,hm⟩ := exists_eval_ne_zero (map φ (pullback Δ)) hP
  let M : Matrix (Fin n) (Fin n) L := fun i j => m (i,j)
  let u : Fin (n+1) → L := fun i => φ (X i)
  refine ⟨chartFrame u M, ?_, ?_⟩
  · have he := eval_pullback φ M Δ
    have hcoef : φ.comp C = algebraMap k L :=
      (IsScalarTower.algebraMap_eq k A L).symm
    rw [hcoef] at he
    rw [eval_map] at hm
    exact fun h => hm (he.trans h)
  · intro j
    change ∑ i, u i * chartFrame u M i j = 0
    rw [Fin.sum_univ_succ]
    simp only [chartFrame, Fin.cons_zero, Fin.cons_succ]
    rw [mul_neg, Finset.mul_sum]
    have hsum : (∑ i, u i.succ * (u 0 * M i j)) = ∑ i, u 0 * (u i.succ * M i j) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsum, neg_add_cancel]

end CubicTenVariables.GenericHyperplaneFrameOpen
