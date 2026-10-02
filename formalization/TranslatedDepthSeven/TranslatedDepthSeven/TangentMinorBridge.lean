import TranslatedDepthSeven.TangentMinors
import TranslatedDepthSeven.TangentTaylor

/-!
# From integral Taylor expansion to tangent-minor divisibility

This file connects the concrete polynomial congruence in `TangentTaylor` to
the concrete matrix divisibility in `TangentMinors`.  Every object occurring
in the statements is an explicit polynomial, point, matrix, or modulus.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped BigOperators

/-- The Jacobian matrix of an explicit finite family of integral
polynomials, evaluated at an integral point and reduced modulo `p`. -/
def jacobianMatrix {c N : ℕ} (F : Fin c → MvPolynomial (Fin N) ℤ)
    (y : Fin N → ℤ) (p : ℕ) : Matrix (Fin c) (Fin N) (ZMod p) :=
  fun r j ↦ (MvPolynomial.eval y (MvPolynomial.pderiv j (F r)) : ZMod p)

/-- If the points `y_i` lie on every equation in `F` and
`y_(i+1)-y_0=qz_i`, then the displacement rows annihilate the transposed
Jacobian modulo every divisor `p` of `q`. -/
theorem displacement_mul_jacobian_transpose_eq_zero
    {c k N q p : ℕ} (hq0 : q ≠ 0) (hpq : p ∣ q)
    (F : Fin c → MvPolynomial (Fin N) ℤ)
    (y : Fin (k + 1) → Fin N → ℤ)
    (z : Matrix (Fin k) (Fin N) ℤ)
    (hy : ∀ i r, MvPolynomial.eval (y i) (F r) = 0)
    (hdiff : ∀ i j, y i.succ j - y 0 j = (q : ℤ) * z i j) :
    z.map (Int.castRingHom (ZMod p)) * (jacobianMatrix F (y 0) p).transpose = 0 := by
  ext i r
  simp only [Matrix.mul_apply, Matrix.transpose_apply, jacobianMatrix,
    Matrix.zero_apply, Matrix.map_apply]
  have hpoint : ∀ j, y i.succ j = y 0 j + (q : ℤ) * z i j := by
    intro j
    linarith [hdiff i j]
  have hpoint_fun : (fun j ↦ y 0 j + (q : ℤ) * z i j) = y i.succ := by
    funext j
    exact (hpoint j).symm
  have htangent := tangent_zmod_of_two_zeros (F r) (y 0) (z i)
    (show (q : ℤ) ≠ 0 by exact_mod_cast hq0)
    (show (p : ℤ) ∣ (q : ℤ) by exact_mod_cast hpq)
    (hy 0 r)
    (by rw [hpoint_fun]; exact hy i.succ r)
  simpa only [mul_comm] using htangent

/-- A Jacobian rank lower bound gives the required rank upper bound for the
matrix of normalized point differences. -/
theorem displacement_rank_le_of_jacobian_rank
    {c k N q p d : ℕ} (hp : p.Prime) (hd : d ≤ N)
    (hq0 : q ≠ 0) (hpq : p ∣ q)
    (F : Fin c → MvPolynomial (Fin N) ℤ)
    (y : Fin (k + 1) → Fin N → ℤ)
    (z : Matrix (Fin k) (Fin N) ℤ)
    (hy : ∀ i r, MvPolynomial.eval (y i) (F r) = 0)
    (hdiff : ∀ i j, y i.succ j - y 0 j = (q : ℤ) * z i j)
    (hJac : N - d ≤ (jacobianMatrix F (y 0) p).rank) :
    (z.map (Int.castRingHom (ZMod p))).rank ≤ d := by
  letI : Fact p.Prime := ⟨hp⟩
  have hzero := displacement_mul_jacobian_transpose_eq_zero
    hq0 hpq F y z hy hdiff
  have hranks := Matrix.rank_add_rank_le_card_of_mul_eq_zero hzero
  rw [Matrix.rank_transpose, Fintype.card_fin] at hranks
  omega

/-- Direct Taylor-to-minor consequence.  If the explicit Jacobian has rank at
least `N-d` modulo every prime factor of the square-free modulus, then every
selected `k`-minor of the point-difference matrix is divisible by
`q^(2k-d)`.

The assumption `d ≤ k` is the range needed by the exponent in the minor
lemma; `d ≤ N` is the geometric tangent-dimension range.
-/
theorem selectedMinor_dvd_of_jacobian_rank
    {c k N q d : ℕ} (hq0 : q ≠ 0) (hq : Squarefree q)
    (hdk : d ≤ k) (hdN : d ≤ N)
    (F : Fin c → MvPolynomial (Fin N) ℤ)
    (y : Fin (k + 1) → Fin N → ℤ)
    (z : Matrix (Fin k) (Fin N) ℤ)
    (hy : ∀ i r, MvPolynomial.eval (y i) (F r) = 0)
    (hdiff : ∀ i j, y i.succ j - y 0 j = (q : ℤ) * z i j)
    (hJac : ∀ p, p.Prime → p ∣ q →
      N - d ≤ (jacobianMatrix F (y 0) p).rank)
    (cols : Fin k → Fin N) :
    (q : ℤ) ^ (2 * k - d) ∣
      TangentMinors.selectedMinor (TangentMinors.differenceMatrix y) cols := by
  apply TangentMinors.selectedMinor_dvd_pow_two_mul_sub_of_squarefree_rank
    hdk hq y z hdiff cols
  intro p hp hpq
  exact displacement_rank_le_of_jacobian_rank hp hdN hq0 hpq F y z hy hdiff
    (hJac p hp hpq)

end

end TranslatedDepthSeven
