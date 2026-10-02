import CubicTenVariables.PrimePowerKernelProfile
import CubicTenVariables.PrimeFieldKernelRank
import CubicTenVariables.HessianSmithProfile

/-!
# Intrinsic cumulative Smith profiles of integral matrices

An actual integral diagonalization defines a cumulative valuation profile.
Consecutive literal modular-kernel cardinalities show that the profile is
independent of every diagonalization choice and of representatives modulo
the relevant prime power. No ordering of the diagonal factors is needed.
-/

noncomputable section
namespace CubicTenVariables.MatrixSmithProfileInvariant
open Matrix PrimePowerKernelProfile SmithProfileMultiplicity
open scoped BigOperators

variable {n : ℕ}

/-- The cumulative count for an integral diagonal. Zero entries do not
contribute to any finite valuation threshold. -/
def diagonalEntry (d : Fin n → ℤ) (p i : ℕ) : ℕ :=
  (Finset.univ.filter fun ν => d ν ≠ 0 ∧ (d ν).natAbs.factorization p ≤ i).card

/-- Sum of actual valuations truncated at the modulus exponent. -/
def diagonalExponent (d : Fin n → ℤ) (p t : ℕ) : ℕ :=
  ∑ ν, truncatedValuation p t (d ν)

theorem diagonalEntry_le (d : Fin n → ℤ) (p i : ℕ) : diagonalEntry d p i ≤ n :=
  (Finset.card_filter_le _ _).trans (by simp)

theorem diagonalEntry_mono (d : Fin n → ℤ) (p : ℕ) : Monotone (diagonalEntry d p) := by
  intro i j hij
  apply Finset.card_le_card
  intro ν hν
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hν ⊢
  exact ⟨hν.1, hν.2.trans hij⟩

/-- The cumulative count agrees with the existing truncated-valuation
profile at every index below the truncation level. -/
theorem diagonalEntry_eq_truncated_profile (d : Fin n → ℤ) (p : ℕ)
    {i a : ℕ} (hi : i < a) :
    diagonalEntry d p i = profile (fun ν => truncatedValuation p a (d ν)) i := by
  classical
  unfold diagonalEntry profile
  congr 1
  apply Finset.filter_congr
  intro ν _
  by_cases h : d ν = 0
  · simp [truncatedValuation, h, Nat.not_le.mpr hi]
  · simp only [truncatedValuation, h, ↓reduceIte, ne_eq, not_false_eq_true, true_and]
    omega

/-- Additive consecutive-exponent formula; no natural subtraction is used. -/
theorem diagonalExponent_succ_add_entry (d : Fin n → ℤ) (p t : ℕ) :
    diagonalExponent d p (t+1) + diagonalEntry d p t =
      diagonalExponent d p t + n := by
  classical
  have hν (ν : Fin n) : truncatedValuation p (t+1) (d ν) +
      (if d ν ≠ 0 ∧ (d ν).natAbs.factorization p ≤ t then 1 else 0) =
      truncatedValuation p t (d ν) + 1 := by
    by_cases h : d ν = 0
    · simp [truncatedValuation, h]
    · simp only [truncatedValuation, if_neg h]
      split_ifs <;> omega
  unfold diagonalExponent diagonalEntry
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, ← Finset.sum_add_distrib]
  simp_rw [hν]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]

@[simp] theorem diagonalExponent_zero (d : Fin n → ℤ) (p : ℕ) :
    diagonalExponent d p 0 = 0 := by
  simp [diagonalExponent, truncatedValuation]

private theorem exists_diagonal (B : Matrix (Fin n) (Fin n) ℤ) :
    ∃ d : Fin n → ℤ, ∃ U V : (Matrix (Fin n) (Fin n) ℤ)ˣ,
      (U : Matrix (Fin n) (Fin n) ℤ) * B * V = Matrix.diagonal d := by
  obtain ⟨U, V, d, hd⟩ := MatrixSmithExistence.exists_integer_diagonalization B
  exact ⟨d, U, V, hd⟩

/-- One actual integral diagonal, chosen before any prime or level. -/
def canonicalDiagonal (B : Matrix (Fin n) (Fin n) ℤ) : Fin n → ℤ :=
  Classical.choose (exists_diagonal B)

theorem canonicalDiagonal_spec (B : Matrix (Fin n) (Fin n) ℤ) :
    ∃ U V : (Matrix (Fin n) (Fin n) ℤ)ˣ,
      (U : Matrix (Fin n) (Fin n) ℤ) * B * V = Matrix.diagonal (canonicalDiagonal B) :=
  Classical.choose_spec (exists_diagonal B)

/-- The cumulative number of Smith valuations at most `i`. Its independence
of the displayed diagonal and of residue representatives is proved below. -/
def entry (B : Matrix (Fin n) (Fin n) ℤ) (p i : ℕ) : ℕ :=
  diagonalEntry (canonicalDiagonal B) p i

/-- The exponent of the literal kernel at modulus `p^t`. -/
def kernelExponent (B : Matrix (Fin n) (Fin n) ℤ) (p t : ℕ) : ℕ :=
  diagonalExponent (canonicalDiagonal B) p t

/-- Actual kernel cardinality, including the modulus-one boundary. -/
def kernelCard (B : Matrix (Fin n) (Fin n) ℤ) (p t : ℕ) : ℕ :=
  Nat.card {x : Fin n → ZMod (p^t) //
    (B.map (Int.castRingHom (ZMod (p^t)))).mulVec x = 0}

theorem entry_le (B : Matrix (Fin n) (Fin n) ℤ) (p i : ℕ) : entry B p i ≤ n :=
  diagonalEntry_le _ _ _

theorem entry_mono (B : Matrix (Fin n) (Fin n) ℤ) (p : ℕ) : Monotone (entry B p) :=
  diagonalEntry_mono _ _

theorem kernelExponent_succ_add_entry (B : Matrix (Fin n) (Fin n) ℤ) (p t : ℕ) :
    kernelExponent B p (t+1) + entry B p t = kernelExponent B p t + n :=
  diagonalExponent_succ_add_entry _ _ _

@[simp] theorem kernelExponent_zero (B : Matrix (Fin n) (Fin n) ℤ) (p : ℕ) :
    kernelExponent B p 0 = 0 := diagonalExponent_zero _ _

theorem kernelExponent_add_sum_entry (B : Matrix (Fin n) (Fin n) ℤ) (p t : ℕ) :
    kernelExponent B p t + ∑ i ∈ Finset.range t, entry B p i = n*t := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Finset.sum_range_succ, Nat.mul_succ]
      have h := kernelExponent_succ_add_entry B p t
      omega

theorem kernelExponent_eq_sub_sum_entry (B : Matrix (Fin n) (Fin n) ℤ) (p t : ℕ) :
    kernelExponent B p t = n*t - ∑ i ∈ Finset.range t, entry B p i := by
  have h := kernelExponent_add_sum_entry B p t
  omega

theorem kernelCard_eq_pow_of_diagonalization (B : Matrix (Fin n) (Fin n) ℤ)
    (d : Fin n → ℤ) (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ)
    (hD : (U : Matrix (Fin n) (Fin n) ℤ) * B * V = Matrix.diagonal d)
    (p : ℕ) (hp : p.Prime) (t : ℕ) :
    kernelCard B p t = p ^ diagonalExponent d p t := by
  letI : NeZero (p^t) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [kernelCard, SmithKernelFormula.card_kernel_eq_prod_gcd_of_int_equivalence
    (p^t) B d U V hD]
  simp only [gcd_primePower p t hp]
  exact Finset.prod_pow_eq_pow_sum Finset.univ _ p

theorem kernelCard_eq_pow (B : Matrix (Fin n) (Fin n) ℤ)
    (p : ℕ) (hp : p.Prime) (t : ℕ) :
    kernelCard B p t = p ^ kernelExponent B p t := by
  obtain ⟨U, V, hD⟩ := canonicalDiagonal_spec B
  exact kernelCard_eq_pow_of_diagonalization B _ U V hD p hp t

theorem kernelCard_eq_pow_profile (B : Matrix (Fin n) (Fin n) ℤ)
    (p : ℕ) (hp : p.Prime) (t : ℕ) :
    kernelCard B p t = p^(n*t - ∑ i ∈ Finset.range t, entry B p i) := by
  rw [kernelCard_eq_pow B p hp t, kernelExponent_eq_sub_sum_entry]

/-- The exponent also agrees with every actual integral diagonalization. -/
theorem kernelExponent_eq_of_diagonalization (B : Matrix (Fin n) (Fin n) ℤ)
    (d : Fin n → ℤ) (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ)
    (hD : (U : Matrix (Fin n) (Fin n) ℤ) * B * V = Matrix.diagonal d)
    (p : ℕ) (hp : p.Prime) (t : ℕ) :
    kernelExponent B p t = diagonalExponent d p t := by
  apply Nat.pow_right_injective hp.two_le
  exact (kernelCard_eq_pow B p hp t).symm.trans
    (kernelCard_eq_pow_of_diagonalization B d U V hD p hp t)

/-- Literal diagonal valuation count for any actual integral row/column
diagonalization; no ordering or divisibility chain is required. -/
theorem entry_eq_of_diagonalization (B : Matrix (Fin n) (Fin n) ℤ)
    (d : Fin n → ℤ) (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ)
    (hD : (U : Matrix (Fin n) (Fin n) ℤ) * B * V = Matrix.diagonal d)
    (p : ℕ) (hp : p.Prime) (i : ℕ) :
    entry B p i = diagonalEntry d p i := by
  have h := kernelExponent_succ_add_entry B p i
  rw [kernelExponent_eq_of_diagonalization B d U V hD p hp (i+1),
    kernelExponent_eq_of_diagonalization B d U V hD p hp i] at h
  have hd := diagonalExponent_succ_add_entry d p i
  omega

theorem entry_eq_truncated_profile_of_diagonalization (B : Matrix (Fin n) (Fin n) ℤ)
    (d : Fin n → ℤ) (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ)
    (hD : (U : Matrix (Fin n) (Fin n) ℤ) * B * V = Matrix.diagonal d)
    (p : ℕ) (hp : p.Prime) {i a : ℕ} (hi : i < a) :
    entry B p i = profile (fun ν => truncatedValuation p a (d ν)) i :=
  (entry_eq_of_diagonalization B d U V hD p hp i).trans
    (diagonalEntry_eq_truncated_profile d p hi)

/-- Exact consecutive kernel growth. This is suitable for recovering the
next profile entry from a direct one-digit kernel calculation. -/
theorem kernelCard_succ (B : Matrix (Fin n) (Fin n) ℤ)
    (p : ℕ) (hp : p.Prime) (t : ℕ) :
    kernelCard B p (t+1) = kernelCard B p t * p^(n-entry B p t) := by
  rw [kernelCard_eq_pow B p hp (t+1), kernelCard_eq_pow B p hp t, ← pow_add]
  congr 1
  have h := kernelExponent_succ_add_entry B p t
  have he := entry_le B p t
  omega

theorem kernelCard_succ_mul_pow_entry (B : Matrix (Fin n) (Fin n) ℤ)
    (p : ℕ) (hp : p.Prime) (t : ℕ) :
    kernelCard B p (t+1) * p^(entry B p t) = kernelCard B p t * p^n := by
  rw [kernelCard_eq_pow B p hp (t+1), kernelCard_eq_pow B p hp t,
    ← pow_add, ← pow_add, kernelExponent_succ_add_entry]

/-- Recover a profile entry from any independently proved one-step kernel
growth formula. The candidate cumulative rank is bounded explicitly. -/
theorem entry_eq_of_kernel_growth (B : Matrix (Fin n) (Fin n) ℤ)
    (p : ℕ) (hp : p.Prime) (t c : ℕ) (hc : c ≤ n)
    (h : kernelCard B p (t+1) = kernelCard B p t * p^(n-c)) :
    entry B p t = c := by
  have hpos : 0 < kernelCard B p t := by
    rw [kernelCard_eq_pow B p hp t]
    exact pow_pos hp.pos _
  have he := Nat.eq_of_mul_eq_mul_left hpos ((kernelCard_succ B p hp t).symm.trans h)
  have hexp := Nat.pow_right_injective hp.two_le he
  have hle := entry_le B p t
  omega

/-- Congruence at a higher prime power implies the literal matrix equality
at every lower level, including modulus one. -/
theorem map_eq_of_map_eq (A B : Matrix (Fin n) (Fin n) ℤ) (p : ℕ)
    {a t : ℕ} (ht : t ≤ a)
    (h : A.map (Int.castRingHom (ZMod (p^a))) =
      B.map (Int.castRingHom (ZMod (p^a)))) :
    A.map (Int.castRingHom (ZMod (p^t))) = B.map (Int.castRingHom (ZMod (p^t))) := by
  ext i j
  have hij := congrArg (ZMod.castHom (pow_dvd_pow p ht) (ZMod (p^t)))
    (congrFun (congrFun h i) j)
  simpa only [Matrix.map_apply, Int.coe_castRingHom, map_intCast] using hij

theorem kernelExponent_eq_of_congr_mod (A B : Matrix (Fin n) (Fin n) ℤ)
    (p : ℕ) (hp : p.Prime) {a t : ℕ} (ht : t ≤ a)
    (h : A.map (Int.castRingHom (ZMod (p^a))) =
      B.map (Int.castRingHom (ZMod (p^a)))) :
    kernelExponent A p t = kernelExponent B p t := by
  apply Nat.pow_right_injective hp.two_le
  change p ^ kernelExponent A p t = p ^ kernelExponent B p t
  rw [← kernelCard_eq_pow A p hp t, ← kernelCard_eq_pow B p hp t]
  unfold kernelCard
  rw [map_eq_of_map_eq A B p ht h]

/-- Every entry below the precision is intrinsic to the residue matrix. -/
theorem entry_eq_of_congr_mod (A B : Matrix (Fin n) (Fin n) ℤ)
    (p : ℕ) (hp : p.Prime) {a i : ℕ} (hi : i < a)
    (h : A.map (Int.castRingHom (ZMod (p^a))) =
      B.map (Int.castRingHom (ZMod (p^a)))) : entry A p i = entry B p i := by
  have hA := kernelExponent_succ_add_entry A p i
  have hB := kernelExponent_succ_add_entry B p i
  rw [kernelExponent_eq_of_congr_mod A B p hp (by omega : i+1 ≤ a) h,
    kernelExponent_eq_of_congr_mod A B p hp (by omega : i ≤ a) h] at hA
  omega

theorem entry_eq_of_dvd_sub (A B : Matrix (Fin n) (Fin n) ℤ)
    (p : ℕ) (hp : p.Prime) {a i : ℕ} (hi : i < a)
    (h : ∀ j k, ((p^a : ℕ) : ℤ) ∣ A j k - B j k) : entry A p i = entry B p i := by
  apply entry_eq_of_congr_mod A B p hp hi
  ext j k
  change (A j k : ZMod (p^a)) = (B j k : ZMod (p^a))
  rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact h j k

/-- The initial cumulative Smith entry is the rank of the actual reduced
matrix, in every prime characteristic. -/
theorem entry_zero_eq_rank (B : Matrix (Fin n) (Fin n) ℤ)
    (p : ℕ) (hp : p.Prime) :
    entry B p 0 = (B.map (Int.castRingHom (ZMod p))).rank := by
  letI : Fact p.Prime := ⟨hp⟩
  have hk : kernelCard B p 1 = p^(n-(B.map (Int.castRingHom (ZMod p))).rank) := by
    unfold kernelCard
    rw [_root_.pow_one]
    exact PrimeFieldKernelRank.card_kernel_eq_pow (B.map (Int.castRingHom (ZMod p)))
  have he : kernelExponent B p 1 = n-(B.map (Int.castRingHom (ZMod p))).rank :=
    Nat.pow_right_injective hp.two_le ((kernelCard_eq_pow B p hp 1).symm.trans hk)
  have h := kernelExponent_succ_add_entry B p 0
  rw [kernelExponent_zero, zero_add] at h
  have hr := Matrix.rank_le_width (B.map (Int.castRingHom (ZMod p)))
  omega

/-- Canonical integer representatives are used only for defining a residue
matrix's profile; every other integral lift gives the same entries. -/
def integerLift {q : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod q)) :
    Matrix (Fin n) (Fin n) ℤ := fun i j => (M i j).val

theorem integerLift_map {q : ℕ} [NeZero q] (M : Matrix (Fin n) (Fin n) (ZMod q)) :
    (integerLift M).map (Int.castRingHom (ZMod q)) = M := by
  ext i j
  simp [integerLift, Matrix.map_apply]

/-- Cumulative Smith entry of the actual residue matrix. -/
def residueEntry (p a : ℕ) (M : Matrix (Fin n) (Fin n) (ZMod (p^a))) (i : ℕ) : ℕ :=
  entry (integerLift M) p i

theorem residueEntry_eq_of_lift (p : ℕ) (hp : p.Prime) (a : ℕ)
    (M : Matrix (Fin n) (Fin n) (ZMod (p^a))) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : A.map (Int.castRingHom (ZMod (p^a))) = M) {i : ℕ} (hi : i < a) :
    residueEntry p a M i = entry A p i := by
  letI : NeZero (p^a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  exact entry_eq_of_congr_mod (integerLift M) A p hp hi
    ((integerLift_map M).trans hA.symm)

theorem residueEntry_map_int (A : Matrix (Fin n) (Fin n) ℤ)
    (p : ℕ) (hp : p.Prime) {a i : ℕ} (hi : i < a) :
    residueEntry p a (A.map (Int.castRingHom (ZMod (p^a)))) i = entry A p i :=
  residueEntry_eq_of_lift p hp a _ A rfl hi

/-- Reduction of an actual residue matrix preserves its earlier profile. -/
theorem residueEntry_reduction (p : ℕ) (hp : p.Prime) {a b i : ℕ}
    (hb : b ≤ a) (hi : i < b) (M : Matrix (Fin n) (Fin n) (ZMod (p^a))) :
    residueEntry p b (M.map (ZMod.castHom (pow_dvd_pow p hb) (ZMod (p^b)))) i =
      residueEntry p a M i := by
  letI : NeZero (p^a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  apply residueEntry_eq_of_lift p hp b _ (integerLift M) _ hi
  ext j k
  have h := congrArg (ZMod.castHom (pow_dvd_pow p hb) (ZMod (p^b)))
    (congrFun (congrFun (integerLift_map M) j) k)
  simpa only [Matrix.map_apply, Int.coe_castRingHom, map_intCast] using h

/-- The actual matrix profile, in the existing ten-variable finite profile type. -/
def toProfile (B : Matrix (Fin 10) (Fin 10) ℤ) (p a : ℕ) :
    SmithProfileNumerics.Profile a := HessianSmithProfile.ofDiagonal p a (canonicalDiagonal B)

theorem entry_toProfile (B : Matrix (Fin 10) (Fin 10) ℤ) (p : ℕ)
    {a i : ℕ} (hi : i < a) :
    SmithProfileNumerics.entry (toProfile B p a) i = entry B p i := by
  rw [toProfile, HessianSmithProfile.entry_ofDiagonal p a _ i hi]
  exact (diagonalEntry_eq_truncated_profile _ p hi).symm

end CubicTenVariables.MatrixSmithProfileInvariant
