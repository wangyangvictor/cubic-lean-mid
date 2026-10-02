import CubicTenVariables.ExponentialSums
import HessianTheorem11.HessianLinearity
import HessianTheorem11.MatrixRankMinors
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-!
A fixed homogeneous integral cubic has a single coefficient-dependent bound
for every Hessian minor in an integer box. At its actual rational Hessian
rank, one can choose injected rows and columns with a nonzero integral
minor. No anisotropy, counting estimate or literature result is assumed.
The rank-zero case uses the actual empty determinant, equal to one.
-/

noncomputable section
namespace CubicTenVariables.HessianMinorBoxBound

open MvPolynomial HessianTheorem11
open scoped BigOperators

/-- One plus the largest absolute coefficient sum of a Hessian entry. -/
def entryConstant {n : ℕ} (F : MvPolynomial (Fin n) ℤ) : ℕ :=
  1 + Finset.univ.sup (fun ij : Fin n × Fin n =>
    ∑ k, (coeff 0 (pderiv k (pderiv ij.2 (pderiv ij.1 F)))).natAbs)

/-- A single bound for all minor sizes, including size zero. -/
def minorConstant {n : ℕ} (F : MvPolynomial (Fin n) ℤ) : ℕ :=
  n.factorial * entryConstant F ^ n

theorem one_le_entryConstant {n : ℕ} (F : MvPolynomial (Fin n) ℤ) :
    1 ≤ entryConstant F := by unfold entryConstant; omega

theorem one_le_minorConstant {n : ℕ} (F : MvPolynomial (Fin n) ℤ) :
    1 ≤ minorConstant F := by
  exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (Nat.factorial_ne_zero n)
    (pow_ne_zero _ (Nat.ne_of_gt (one_le_entryConstant F))))

theorem hessian_entry_natAbs_le {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (B : ℕ) (x : Fin n → ℤ)
    (hx : ∀ i, (x i).natAbs ≤ B) (i j : Fin n) :
    (hessian F x i j).natAbs ≤ entryConstant F * B := by
  have hsum : (∑ k, (coeff 0 (pderiv k (pderiv j (pderiv i F)))).natAbs) ≤
      entryConstant F := by
    exact (Finset.le_sup (f := fun ij : Fin n × Fin n =>
      ∑ k, (coeff 0 (pderiv k (pderiv ij.2 (pderiv ij.1 F)))).natAbs)
      (Finset.mem_univ (i,j))).trans (by unfold entryConstant; omega)
  have habs (k : Fin n) : |x k| ≤ (B : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hx k
  have hsum' : (∑ k, |coeff 0 (pderiv k (pderiv j (pderiv i F)))|) ≤
      (entryConstant F : ℤ) := by
    have hh : ((∑ k, (coeff 0 (pderiv k (pderiv j (pderiv i F)))).natAbs : ℕ) : ℤ) ≤
        (entryConstant F : ℤ) := by exact_mod_cast hsum
    simpa only [Nat.cast_sum, Int.natCast_natAbs] using hh
  have hb : |hessian F x i j| ≤ (entryConstant F : ℤ) * B := by
    rw [hessian_entry_expansion hF]
    calc
      _ ≤ ∑ k, |x k * coeff 0 (pderiv k (pderiv j (pderiv i F)))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, (B : ℤ) * |coeff 0 (pderiv k (pderiv j (pderiv i F)))| := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (habs k) (abs_nonneg _)
      _ = (B : ℤ) * ∑ k, |coeff 0 (pderiv k (pderiv j (pderiv i F)))| :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ (B : ℤ) * entryConstant F := mul_le_mul_of_nonneg_left hsum' (by positivity)
      _ = _ := mul_comm _ _
  rw [← Int.natCast_natAbs] at hb
  exact_mod_cast hb

theorem minor_natAbs_le {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (B : ℕ) (x : Fin n → ℤ)
    (hx : ∀ i, (x i).natAbs ≤ B) (j : ℕ) (hj : j ≤ n)
    (rows cols : Fin j → Fin n) :
    ((hessian F x).submatrix rows cols).det.natAbs ≤ minorConstant F * B ^ j := by
  have he (a b : Fin j) : |((hessian F x).submatrix rows cols) a b| ≤
      ((entryConstant F * B : ℕ) : ℤ) := by
    change |hessian F x (rows a) (cols b)| ≤ _
    rw [← Int.natCast_natAbs]
    exact_mod_cast hessian_entry_natAbs_le F hF B x hx (rows a) (cols b)
  have hd := Matrix.det_le (abv := (AbsoluteValue.abs : AbsoluteValue ℤ ℤ)) he
  have hd' : ((hessian F x).submatrix rows cols).det.natAbs ≤
      j.factorial * (entryConstant F * B) ^ j := by
    have hd'' : |((hessian F x).submatrix rows cols).det| ≤
        (j.factorial : ℤ) * (entryConstant F * B : ℕ) ^ j := by
      simpa only [Fintype.card_fin, nsmul_eq_mul, AbsoluteValue.abs_apply] using hd
    rw [← Int.natCast_natAbs] at hd''
    exact_mod_cast hd''
  calc
    _ ≤ j.factorial * (entryConstant F * B) ^ j := hd'
    _ = (j.factorial * entryConstant F ^ j) * B ^ j := by rw [mul_pow, Nat.mul_assoc]
    _ ≤ minorConstant F * B ^ j := by
      apply Nat.mul_le_mul_right
      exact Nat.mul_le_mul (Nat.factorial_le hj)
        (Nat.pow_le_pow_right (one_le_entryConstant F) hj)

/-- The rational rank uses coefficient extension and the same evaluated
integral Hessian, rather than an unrelated matrix. -/
theorem integerHessianRank_eq_rank_map {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (x : Fin n → ℤ) :
    integerHessianRank F x = ((hessian F x).map (Int.castRingHom ℚ)).rank := by
  unfold integerHessianRank
  congr 1
  ext i j
  simp only [hessian, hessianPolynomial, pderiv_map, Matrix.map_apply]
  rw [eval_map]
  exact (eval₂_comp (Int.castRingHom ℚ) x _).symm

/-- Every integral matrix admits a nonzero minor of its rational rank,
with both index selections constructed as embeddings. -/
theorem exists_integral_rank_minor {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) :
    ∃ (rows cols : Fin (M.map (Int.castRingHom ℚ)).rank ↪ Fin n),
      (M.submatrix rows cols).det ≠ 0 := by
  classical
  obtain ⟨rows, cols, hd⟩ := MatrixRankMinors.exists_rank_minor
    (M.map (Int.castRingHom ℚ))
  have hdet : (M.submatrix rows cols).det ≠ 0 := by
    intro hz
    apply hd
    change ((M.submatrix rows cols).map (Int.castRingHom ℚ)).det = 0
    have he := (Int.castRingHom ℚ).map_det (M.submatrix rows cols)
    rw [hz, map_zero] at he
    exact he.symm
  have hr : Function.Injective rows := by
    intro a b hab
    by_contra hne
    exact hdet (Matrix.det_zero_of_row_eq hne (by ext c; simp [Matrix.submatrix, hab]))
  have hc : Function.Injective cols := by
    intro a b hab
    by_contra hne
    exact hdet (Matrix.det_zero_of_column_eq hne (by intro c; simp [Matrix.submatrix, hab]))
  exact ⟨⟨rows, hr⟩, ⟨cols, hc⟩, hdet⟩

/-- One explicitly constructed natural constant controls an actual nonzero
rank-sized Hessian minor, uniformly in the box, its point and the rank. -/
theorem exists_uniform_rank_minor_bound {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (B : ℕ), 1 ≤ B → ∀ (x : Fin n → ℤ),
      (∀ i, (x i).natAbs ≤ B) → ∀ (j : ℕ), integerHessianRank F x = j →
      ∃ (rows cols : Fin j ↪ Fin n),
        ((hessian F x).submatrix rows cols).det ≠ 0 ∧
        ((hessian F x).submatrix rows cols).det.natAbs ≤ C * B ^ j := by
  refine ⟨minorConstant F, one_le_minorConstant F, fun B _hB x hx j hj => ?_⟩
  rw [integerHessianRank_eq_rank_map] at hj
  subst j
  obtain ⟨rows, cols, hd⟩ := exists_integral_rank_minor (hessian F x)
  refine ⟨rows, cols, hd, minor_natAbs_le F hF B x hx _ ?_ rows cols⟩
  simpa using Matrix.rank_le_card_width ((hessian F x).map (Int.castRingHom ℚ))

/-- The same endpoint with the project's actual integer-box predicate. -/
theorem exists_uniform_rank_minor_bound_in_integerBox {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (B : ℕ), 1 ≤ B → ∀ (x : Fin n → ℤ),
      x ∈ integerBox n B → ∀ (j : ℕ), integerHessianRank F x = j →
      ∃ (rows cols : Fin j ↪ Fin n),
        ((hessian F x).submatrix rows cols).det ≠ 0 ∧
        ((hessian F x).submatrix rows cols).det.natAbs ≤ C * B ^ j := by
  obtain ⟨C, hC, h⟩ := exists_uniform_rank_minor_bound F hF
  refine ⟨C, hC, fun B hB x hx j hj => h B hB x ?_ j hj⟩
  intro i
  have hi := (mem_integerBox.mp hx) i
  rw [← Int.natCast_natAbs] at hi
  exact_mod_cast hi

end CubicTenVariables.HessianMinorBoxBound
