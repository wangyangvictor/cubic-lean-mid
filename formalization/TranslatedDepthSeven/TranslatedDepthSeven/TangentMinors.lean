import Mathlib

/-!
# The elementary algebra in the tangent-minor argument

This file contains only finite-dimensional matrix algebra over `ℤ` and
`ZMod p`.  In particular, it does not introduce a packaged determinant-method
hypothesis.
-/

namespace TranslatedDepthSeven

noncomputable section

namespace TangentMinors

/-- The matrix whose rows are the differences `y_(i+1) - y_0`. -/
def differenceMatrix {k N : ℕ} (y : Fin (k + 1) → Fin N → ℤ) :
    Matrix (Fin k) (Fin N) ℤ :=
  fun i j ↦ y i.succ j - y 0 j

/-- A square determinant obtained by selecting `k` columns of a `k × N`
matrix.  Injectivity of `cols` is not needed for any theorem below (a repeated
column simply gives determinant zero). -/
def selectedMinor {k N : ℕ} (M : Matrix (Fin k) (Fin N) ℤ)
    (cols : Fin k → Fin N) : ℤ :=
  (M.submatrix id cols).det

/-- Extracting a common factor `q` from all point differences extracts
`q^k` from every selected `k`-minor. -/
theorem selectedMinor_eq_pow_mul_of_difference_eq_mul {k N : ℕ}
    (y : Fin (k + 1) → Fin N → ℤ) (z : Matrix (Fin k) (Fin N) ℤ)
    (q : ℤ) (h : ∀ i j, y i.succ j - y 0 j = q * z i j)
    (cols : Fin k → Fin N) :
    selectedMinor (differenceMatrix y) cols =
      q ^ k * selectedMinor z cols := by
  have hmatrix : differenceMatrix y = q • z := by
    ext i j
    simp only [differenceMatrix, h]
    rfl
  rw [selectedMinor, hmatrix]
  change (q • z.submatrix id cols).det =
    q ^ k * (z.submatrix id cols).det
  rw [Matrix.det_smul]
  simp

/-- If all entries in the rows indexed by `s` are divisible by `p`, then the
determinant is divisible by one factor of `p` for every such row. -/
theorem pow_card_dvd_det_of_rows_dvd {k : ℕ} (A : Matrix (Fin k) (Fin k) ℤ)
    (p : ℤ) (s : Finset (Fin k))
    (h : ∀ i ∈ s, ∀ j, p ∣ A i j) :
    p ^ s.card ∣ A.det := by
  classical
  let B : Matrix (Fin k) (Fin k) ℤ := fun i j ↦
    if hi : i ∈ s then Classical.choose (h i hi j) else A i j
  let c : Fin k → ℤ := fun i ↦ if i ∈ s then p else 1
  have hA : A = Matrix.of (fun i j ↦ c i * B i j) := by
    ext i j
    by_cases hi : i ∈ s
    · have hij := Classical.choose_spec (h i hi j)
      change A i j = (if i ∈ s then p else 1) *
        (if hi' : i ∈ s then Classical.choose (h i hi' j) else A i j)
      rw [if_pos hi, dif_pos hi]
      exact hij
    · change A i j = (if i ∈ s then p else 1) *
        (if hi' : i ∈ s then Classical.choose (h i hi' j) else A i j)
      rw [if_neg hi, dif_neg hi, one_mul]
  rw [hA, Matrix.det_mul_column]
  have hc : ∏ i, c i = p ^ s.card := by
    simp [c]
  rw [hc]
  exact dvd_mul_right _ _

/-- The entrywise least-nonnegative integral lift of a matrix over `ZMod p`. -/
def zmodLiftMatrix {k : ℕ} (p : ℕ)
    (A : Matrix (Fin k) (Fin k) (ZMod p)) : Matrix (Fin k) (Fin k) ℤ :=
  fun i j ↦ (A i j).val

@[simp]
theorem zmodLiftMatrix_map {k p : ℕ} [NeZero p]
    (A : Matrix (Fin k) (Fin k) (ZMod p)) :
    (zmodLiftMatrix p A).map (Int.castRingHom (ZMod p)) = A := by
  ext i j
  simp [zmodLiftMatrix, ZMod.natCast_val]

/-- Concrete row-reduction form of the local tangent-space divisibility.

The matrix `Ubar` is an invertible row operation modulo `p`; the rows in `s`
of `Ubar * (A mod p)` vanish.  Therefore one can extract `p` from those rows,
and invertibility of `Ubar` prevents the auxiliary determinant from absorbing
any factor of `p`. -/
theorem pow_card_dvd_det_of_invertible_row_reduction {k p : ℕ}
    (hp : p.Prime) (A : Matrix (Fin k) (Fin k) ℤ)
    (Ubar : Matrix (Fin k) (Fin k) (ZMod p))
    (s : Finset (Fin k)) (hU : Ubar.det ≠ 0)
    (hzero : ∀ i ∈ s, ∀ j,
      (Ubar * A.map (Int.castRingHom (ZMod p))) i j = 0) :
    (p : ℤ) ^ s.card ∣ A.det := by
  let U : Matrix (Fin k) (Fin k) ℤ := zmodLiftMatrix p Ubar
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hmapU : U.map (Int.castRingHom (ZMod p)) = Ubar := by
    exact zmodLiftMatrix_map Ubar
  have hnot : ¬(p : ℤ) ∣ U.det := by
    intro hdvd
    have hcast : ((U.det : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd U.det p).2 hdvd
    have hdetmap :
        (U.map (Int.castRingHom (ZMod p))).det =
          ((U.det : ℤ) : ZMod p) := by
      exact ((Int.castRingHom (ZMod p)).map_det U).symm
    apply hU
    rw [← hmapU, hdetmap, hcast]
  have hrows : ∀ i ∈ s, ∀ j, (p : ℤ) ∣ (U * A) i j := by
    intro i hi j
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd ((U * A) i j) p).1
    have hmapmul :
        (U * A).map (Int.castRingHom (ZMod p)) =
          Ubar * A.map (Int.castRingHom (ZMod p)) := by
      rw [Matrix.map_mul, hmapU]
    change ((U * A).map (Int.castRingHom (ZMod p))) i j = 0
    rw [hmapmul]
    exact hzero i hi j
  have hpow : (p : ℤ) ^ s.card ∣ (U * A).det :=
    pow_card_dvd_det_of_rows_dvd (U * A) p s hrows
  rw [Matrix.det_mul] at hpow
  exact (Nat.prime_iff_prime_int.mp hp).pow_dvd_of_dvd_mul_left s.card hnot hpow

/-- Basis form of the local lemma.  If the basis vectors indexed by `s` are
left-kernel vectors of the reduction of `A` modulo `p`, then `p^|s|` divides
the determinant. -/
theorem pow_card_dvd_det_of_kernel_basis_rows {k p : ℕ}
    (hp : p.Prime) (A : Matrix (Fin k) (Fin k) ℤ)
    (b : Module.Basis (Fin k) (ZMod p) (Fin k → ZMod p))
    (s : Finset (Fin k))
    (hker : ∀ i ∈ s,
      (A.map (Int.castRingHom (ZMod p))).vecMulLinear (b i) = 0) :
    (p : ℤ) ^ s.card ∣ A.det := by
  letI : Fact p.Prime := ⟨hp⟩
  let Ubar : Matrix (Fin k) (Fin k) (ZMod p) := Matrix.of (fun i j ↦ b i j)
  have hU : Ubar.det ≠ 0 := by
    have hu := (Pi.basisFun (ZMod p) (Fin k)).isUnit_det b
    have hne : (Matrix.of (fun i j ↦ b i j)).det ≠ 0 := by
      rw [← Pi.basisFun_det_apply]
      exact hu.ne_zero
    exact hne
  apply pow_card_dvd_det_of_invertible_row_reduction hp A Ubar s hU
  intro i hi j
  have hij := congrFun (hker i hi) j
  simpa [Ubar, Matrix.mul_apply, Matrix.vecMulLinear_apply, Matrix.vecMul,
    dotProduct] using hij

/-- Rank form of the local tangent-space divisibility.  A rank loss of
`k-d` modulo the prime `p` forces at least `k-d` factors of `p` in the
integral determinant. -/
theorem primePower_dvd_det_of_rank_le {k p d : ℕ}
    (hp : p.Prime) (A : Matrix (Fin k) (Fin k) ℤ)
    (hrank : (A.map (Int.castRingHom (ZMod p))).rank ≤ d) :
    (p : ℤ) ^ (k - d) ∣ A.det := by
  letI : Fact p.Prime := ⟨hp⟩
  let Abar : Matrix (Fin k) (Fin k) (ZMod p) :=
    A.map (Int.castRingHom (ZMod p))
  let K : Submodule (ZMod p) (Fin k → ZMod p) :=
    LinearMap.ker Abar.vecMulLinear
  let bk := Module.finBasis (ZMod p) K
  let v : Fin (Module.finrank (ZMod p) K) → (Fin k → ZMod p) :=
    fun i ↦ (bk i : Fin k → ZMod p)
  have hv : LinearIndependent (ZMod p) v := by
    exact bk.linearIndependent.map' K.subtype (Submodule.ker_subtype K)
  let hs := hv.linearIndepOn_id
  let bExt := Module.Basis.extend hs
  letI : Fintype (hs.extend (Set.subset_univ _)) :=
    FiniteDimensional.fintypeBasisIndex bExt
  have hcard : Fintype.card (hs.extend (Set.subset_univ _)) = k := by
    rw [← Module.finrank_eq_card_basis bExt]
    simp
  let e : (hs.extend (Set.subset_univ _)) ≃ Fin k :=
    Fintype.equivOfCardEq (by simpa using hcard)
  let b : Module.Basis (Fin k) (ZMod p) (Fin k → ZMod p) :=
    bExt.reindex e
  let kerIndex : Fin (Module.finrank (ZMod p) K) →
      hs.extend (Set.subset_univ _) := fun i ↦
    ⟨v i, hs.subset_extend (Set.subset_univ _) ⟨i, rfl⟩⟩
  have hkerIndex : Function.Injective kerIndex := by
    intro i j hij
    apply hv.injective
    simpa [kerIndex] using congrArg Subtype.val hij
  let s : Finset (Fin k) :=
    Finset.univ.image (fun i ↦ e (kerIndex i))
  have hsCard : s.card = Module.finrank (ZMod p) K := by
    have hinj : Function.Injective (fun i ↦ e (kerIndex i)) :=
      e.injective.comp hkerIndex
    simpa [s] using Finset.card_image_of_injective Finset.univ hinj
  have hbasisKer : ∀ i ∈ s, Abar.vecMulLinear (b i) = 0 := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨j, -, rfl⟩
    rw [Module.Basis.reindex_apply]
    simp only [Equiv.symm_apply_apply]
    rw [Module.Basis.extend_apply_self]
    exact (bk j).property
  have hlarge : (p : ℤ) ^ (Module.finrank (ZMod p) K) ∣ A.det := by
    rw [← hsCard]
    exact pow_card_dvd_det_of_kernel_basis_rows hp A b s (by
      simpa [Abar] using hbasisKer)
  have hrange :
      Module.finrank (ZMod p) (LinearMap.range Abar.vecMulLinear) = Abar.rank := by
    rw [range_vecMulLinear, ← Matrix.rank_eq_finrank_span_row]
  have hnull : Abar.rank + Module.finrank (ZMod p) K = k := by
    have h := Abar.vecMulLinear.finrank_range_add_finrank_ker
    rw [hrange] at h
    simpa [K] using h
  have hle : k - d ≤ Module.finrank (ZMod p) K := by
    have hrank' : Abar.rank ≤ d := by simpa [Abar] using hrank
    omega
  exact (pow_dvd_pow (p : ℤ) hle).trans hlarge

/-- The prime-power divisibilities combine without loss over a square-free
modulus. -/
theorem squarefreePower_dvd_det_of_prime_ranks {k q d : ℕ}
    (hq : Squarefree q) (A : Matrix (Fin k) (Fin k) ℤ)
    (hrank : ∀ p, p.Prime → p ∣ q →
      (A.map (Int.castRingHom (ZMod p))).rank ≤ d) :
    (q : ℤ) ^ (k - d) ∣ A.det := by
  let r := k - d
  let f : ℕ → ℤ := fun p ↦ (p : ℤ) ^ r
  have hpair : (q.primeFactors : Set ℕ).Pairwise
      (Function.onFun IsCoprime f) := by
    intro p hpMem p' hp'Mem hne
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpMem
    have hp' : p'.Prime := Nat.prime_of_mem_primeFactors hp'Mem
    have hcop : p.Coprime p' := (Nat.coprime_primes hp hp').2 hne
    exact (Nat.Coprime.pow r r hcop).isCoprime
  have heach : ∀ p ∈ q.primeFactors, f p ∣ A.det := by
    intro p hpMem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpMem
    have hpq : p ∣ q := Nat.dvd_of_mem_primeFactors hpMem
    exact primePower_dvd_det_of_rank_le hp A (hrank p hp hpq)
  have hprod : (∏ p ∈ q.primeFactors, f p) ∣ A.det :=
    Finset.prod_dvd_of_coprime hpair heach
  have hprodEq : ∏ p ∈ q.primeFactors, f p = (q : ℤ) ^ r := by
    change (∏ p ∈ q.primeFactors, (p : ℤ) ^ r) = (q : ℤ) ^ r
    rw [Finset.prod_pow]
    congr 1
    simpa only [Nat.cast_prod] using congrArg (fun m : ℕ ↦ (m : ℤ))
      (Nat.prod_primeFactors_of_squarefree hq)
  rw [hprodEq] at hprod
  exact hprod

/-- Selecting `k` columns from a `k × N` matrix cannot increase its rank. -/
theorem selectedColumns_rank_le {F : Type*} [Field F] {k N : ℕ}
    (M : Matrix (Fin k) (Fin N) F) (cols : Fin k → Fin N) :
    (M.submatrix id cols).rank ≤ M.rank := by
  calc
    (M.submatrix id cols).rank =
        (Matrix.transpose (M.submatrix id cols)).rank :=
      (Matrix.rank_transpose (M.submatrix id cols)).symm
    _ = ((Matrix.transpose M).submatrix cols id).rank := by
      rw [Matrix.transpose_submatrix]
    _ ≤ (Matrix.transpose M).rank :=
      Matrix.rank_submatrix_le cols (Equiv.refl _) (Matrix.transpose M)
    _ = M.rank := Matrix.rank_transpose M

/-- Full algebraic `q^(2k-d)` tangent-minor divisibility.  The first `q^k`
comes from congruence of the points; the remaining `q^(k-d)` comes from the
rank bound modulo every prime factor of the square-free modulus. -/
theorem selectedMinor_dvd_pow_two_mul_sub_of_squarefree_rank {k N q d : ℕ}
    (hd : d ≤ k) (hq : Squarefree q)
    (y : Fin (k + 1) → Fin N → ℤ) (z : Matrix (Fin k) (Fin N) ℤ)
    (hdiff : ∀ i j, y i.succ j - y 0 j = (q : ℤ) * z i j)
    (cols : Fin k → Fin N)
    (hrank : ∀ p, p.Prime → p ∣ q →
      (z.map (Int.castRingHom (ZMod p))).rank ≤ d) :
    (q : ℤ) ^ (2 * k - d) ∣ selectedMinor (differenceMatrix y) cols := by
  let Z : Matrix (Fin k) (Fin k) ℤ := z.submatrix id cols
  have hlocal : (q : ℤ) ^ (k - d) ∣ Z.det :=
    squarefreePower_dvd_det_of_prime_ranks hq Z (by
      intro p hp hpq
      letI : Fact p.Prime := ⟨hp⟩
      change ((z.submatrix id cols).map
        (Int.castRingHom (ZMod p))).rank ≤ d
      rw [← Matrix.submatrix_map]
      exact (selectedColumns_rank_le
        (z.map (Int.castRingHom (ZMod p))) cols).trans (hrank p hp hpq))
  have hmul : (q : ℤ) ^ k * (q : ℤ) ^ (k - d) ∣
      (q : ℤ) ^ k * Z.det :=
    mul_dvd_mul_left ((q : ℤ) ^ k) hlocal
  have hexp : k + (k - d) = 2 * k - d := by omega
  rw [← pow_add, hexp] at hmul
  rw [selectedMinor_eq_pow_mul_of_difference_eq_mul y z q hdiff cols]
  exact hmul

/-- A nonzero integer cannot be divisible by an integer of strictly larger
absolute value. -/
theorem eq_zero_of_dvd_of_natAbs_lt {D a : ℤ}
    (hdiv : D ∣ a) (hlt : a.natAbs < D.natAbs) : a = 0 := by
  by_contra ha
  have hle : D.natAbs ≤ a.natAbs := Int.natAbs_le_of_dvd_ne_zero hdiv ha
  omega

/-- Determinant form of `eq_zero_of_dvd_of_natAbs_lt`. -/
theorem det_eq_zero_of_large_divisor {k : ℕ}
    (A : Matrix (Fin k) (Fin k) ℤ) (D : ℤ)
    (hdiv : D ∣ A.det) (hlt : A.det.natAbs < D.natAbs) :
    A.det = 0 :=
  eq_zero_of_dvd_of_natAbs_lt hdiv hlt

end TangentMinors

end

end TranslatedDepthSeven
