import TranslatedDepthSeven.TangentMinorBridge

/-!
# An explicit integral Jacobian-minor certificate

The certificate in this file is an actual determinant in `ℤ`.  If a prime
does not divide that determinant, its reduction is a nonzero minor of the
reduced Jacobian and therefore supplies the rank hypothesis used by
`selectedMinor_dvd_of_jacobian_rank`.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- The integral Jacobian matrix of the displayed equations at the displayed
integral point. -/
def integralJacobianMatrix {c N : ℕ}
    (F : Fin c → MvPolynomial (Fin N) ℤ) (y : Fin N → ℤ) :
    Matrix (Fin c) (Fin N) ℤ :=
  fun r j ↦ MvPolynomial.eval y (MvPolynomial.pderiv j (F r))

/-- Reduction of the integral Jacobian is definitionally the Jacobian matrix
used in `TangentMinorBridge`. -/
theorem integralJacobianMatrix_map_zmod {c N p : ℕ}
    (F : Fin c → MvPolynomial (Fin N) ℤ) (y : Fin N → ℤ) :
    (integralJacobianMatrix F y).map (Int.castRingHom (ZMod p)) =
      jacobianMatrix F y p := by
  rfl

/-- A chosen integral Jacobian minor.  The row and column maps are explicit;
nonvanishing itself forces them to be injective. -/
def integralJacobianMinor {c N r : ℕ}
    (F : Fin c → MvPolynomial (Fin N) ℤ) (y : Fin N → ℤ)
    (rows : Fin r → Fin c) (cols : Fin r → Fin N) : ℤ :=
  ((integralJacobianMatrix F y).submatrix rows cols).det

/-- Determinants commute with reduction modulo `p`, including after selecting
the indicated rows and columns. -/
theorem integralJacobianMinor_cast_zmod {c N r p : ℕ}
    (F : Fin c → MvPolynomial (Fin N) ℤ) (y : Fin N → ℤ)
    (rows : Fin r → Fin c) (cols : Fin r → Fin N) :
    (integralJacobianMinor F y rows cols : ZMod p) =
      ((jacobianMatrix F y p).submatrix rows cols).det := by
  change (Int.castRingHom (ZMod p))
      ((integralJacobianMatrix F y).submatrix rows cols).det = _
  rw [RingHom.map_det]
  rfl

/-- A nonzero square submatrix over a field gives a lower bound for the rank
of the ambient matrix. -/
theorem rank_ge_card_of_submatrix_det_ne_zero
    {K : Type*} [Field K] {c N r : ℕ}
    (A : Matrix (Fin c) (Fin N) K)
    (rows : Fin r → Fin c) (cols : Fin r → Fin N)
    (hdet : (A.submatrix rows cols).det ≠ 0) :
    r ≤ A.rank := by
  let B : Matrix (Fin r) (Fin N) K :=
    A.submatrix rows (Equiv.refl (Fin N))
  let C : Matrix (Fin r) (Fin r) K :=
    B.transpose.submatrix cols (Equiv.refl (Fin r))
  have hCeq : C = (A.submatrix rows cols).transpose := by
    ext i j
    rfl
  have hCrank : C.rank = r := by
    have hCunit : IsUnit C := (Matrix.isUnit_iff_isUnit_det C).mpr <|
      (isUnit_iff_ne_zero).2 (by
      rw [hCeq, Matrix.det_transpose]
      exact hdet)
    simpa using Matrix.rank_of_isUnit C hCunit
  have hCB : C.rank ≤ B.transpose.rank := by
    exact Matrix.rank_submatrix_le cols (Equiv.refl (Fin r)) B.transpose
  have hBA : B.rank ≤ A.rank := by
    exact Matrix.rank_submatrix_le rows (Equiv.refl (Fin N)) A
  rw [Matrix.rank_transpose] at hCB
  omega

/-- Nondivisibility of the chosen integral minor by `p` gives the desired
rank lower bound for the reduced Jacobian. -/
theorem jacobian_rank_ge_of_minor_not_dvd
    {c N r p : ℕ} (hp : p.Prime)
    (F : Fin c → MvPolynomial (Fin N) ℤ) (y : Fin N → ℤ)
    (rows : Fin r → Fin c) (cols : Fin r → Fin N)
    (hminor : ¬(p : ℤ) ∣ integralJacobianMinor F y rows cols) :
    r ≤ (jacobianMatrix F y p).rank := by
  letI : Fact p.Prime := ⟨hp⟩
  apply rank_ge_card_of_submatrix_det_ne_zero
      (jacobianMatrix F y p) rows cols
  rw [← integralJacobianMinor_cast_zmod]
  intro hzero
  apply hminor
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd
    (integralJacobianMinor F y rows cols) p).mp hzero

/-- If `q` is coprime to the absolute value of an integer certificate, no
prime divisor of `q` divides that certificate in `ℤ`. -/
theorem prime_not_dvd_int_of_coprime_natAbs
    {q p : ℕ} {Δ : ℤ} (hp : p.Prime) (hpq : p ∣ q)
    (hcop : Nat.Coprime q Δ.natAbs) :
    ¬(p : ℤ) ∣ Δ := by
  intro hpΔ
  have hpAbs : p ∣ Δ.natAbs := Int.natCast_dvd.mp hpΔ
  exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpq hpAbs) hcop

/-- A single integral minor coprime to `q` certifies the required Jacobian
rank at every prime divisor of `q`.  Squarefreeness is not needed for this
rank statement itself. -/
theorem jacobian_rank_ge_for_prime_divisors_of_coprime_minor
    {c N r q : ℕ}
    (F : Fin c → MvPolynomial (Fin N) ℤ) (y : Fin N → ℤ)
    (rows : Fin r → Fin c) (cols : Fin r → Fin N)
    (hcop : Nat.Coprime q (integralJacobianMinor F y rows cols).natAbs) :
    ∀ p, p.Prime → p ∣ q → r ≤ (jacobianMatrix F y p).rank := by
  intro p hp hpq
  exact jacobian_rank_ge_of_minor_not_dvd hp F y rows cols
    (prime_not_dvd_int_of_coprime_natAbs hp hpq hcop)

/-- Explicit-nondivisibility version of the final tangent-minor conclusion.
The chosen Jacobian minor has size `N-d`; nondivisibility at every prime
factor of the squarefree modulus supplies exactly the rank assumptions of
`selectedMinor_dvd_of_jacobian_rank`. -/
theorem selectedMinor_dvd_of_integralJacobianMinor_nondivisibility
    {c k N q d : ℕ} (hq0 : q ≠ 0) (hq : Squarefree q)
    (hdk : d ≤ k) (hdN : d ≤ N)
    (F : Fin c → MvPolynomial (Fin N) ℤ)
    (y : Fin (k + 1) → Fin N → ℤ)
    (z : Matrix (Fin k) (Fin N) ℤ)
    (hy : ∀ i r, MvPolynomial.eval (y i) (F r) = 0)
    (hdiff : ∀ i j, y i.succ j - y 0 j = (q : ℤ) * z i j)
    (rows : Fin (N - d) → Fin c) (jacCols : Fin (N - d) → Fin N)
    (hminor : ∀ p, p.Prime → p ∣ q →
      ¬(p : ℤ) ∣ integralJacobianMinor F (y 0) rows jacCols)
    (minorCols : Fin k → Fin N) :
    (q : ℤ) ^ (2 * k - d) ∣
      TangentMinors.selectedMinor
        (TangentMinors.differenceMatrix y) minorCols := by
  apply selectedMinor_dvd_of_jacobian_rank
    hq0 hq hdk hdN F y z hy hdiff _ minorCols
  intro p hp hpq
  exact jacobian_rank_ge_of_minor_not_dvd hp F (y 0) rows jacCols
    (hminor p hp hpq)

/-- Coprime-certificate version of the final tangent-minor conclusion.  This
is the form used after deleting the prime divisors of one explicit nonzero
integer Jacobian minor from the auxiliary-prime pool. -/
theorem selectedMinor_dvd_of_integralJacobianMinor_coprime
    {c k N q d : ℕ} (hq0 : q ≠ 0) (hq : Squarefree q)
    (hdk : d ≤ k) (hdN : d ≤ N)
    (F : Fin c → MvPolynomial (Fin N) ℤ)
    (y : Fin (k + 1) → Fin N → ℤ)
    (z : Matrix (Fin k) (Fin N) ℤ)
    (hy : ∀ i r, MvPolynomial.eval (y i) (F r) = 0)
    (hdiff : ∀ i j, y i.succ j - y 0 j = (q : ℤ) * z i j)
    (rows : Fin (N - d) → Fin c) (jacCols : Fin (N - d) → Fin N)
    (hcop : Nat.Coprime q
      (integralJacobianMinor F (y 0) rows jacCols).natAbs)
    (minorCols : Fin k → Fin N) :
    (q : ℤ) ^ (2 * k - d) ∣
      TangentMinors.selectedMinor
        (TangentMinors.differenceMatrix y) minorCols := by
  apply selectedMinor_dvd_of_integralJacobianMinor_nondivisibility
    hq0 hq hdk hdN F y z hy hdiff rows jacCols _ minorCols
  intro p hp hpq
  exact prime_not_dvd_int_of_coprime_natAbs hp hpq hcop

end

end TranslatedDepthSeven
