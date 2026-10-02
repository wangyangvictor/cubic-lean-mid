import TranslatedDepthSeven.AffinePolynomialChange
import TranslatedDepthSeven.PublishedCountingTheorems
import TranslatedDepthSeven.StandardGradedQuotientFiltration
import Mathlib.NumberTheory.BernoulliPolynomials

/-!
# Hilbert functions under an invertible affine change

The degree filtration on an affine coordinate ring is preserved, with equal
filtered dimensions, by the literal automorphism `X i ↦ y₀ i + r X i` when
`r ≠ 0`.  This is an internal algebraic bridge; it assumes no geometric
counting statement.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace Published

variable {K : Type u} [Field K] {N : ℕ}

/-- The quotient equivalence induced by an invertible affine change carries
the degree-at-most-`k` filtration onto the corresponding filtration of the
transformed ideal. -/
theorem affineHilbertFiltration_map_affinePolynomialChange
    (I : Ideal (MvPolynomial (Fin N) K)) (y₀ : Fin N → K)
    (r : K) (hr : r ≠ 0) (k : ℕ) :
    (affineHilbertFiltration K N I k).map
        (affinePolynomialChangeQuotientAlgEquiv y₀ r hr I).toLinearMap =
      affineHilbertFiltration K N
        (I.map (affinePolynomialChangeAlgEquiv y₀ r hr)) k := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨f, hf, rfl⟩
    refine ⟨affinePolynomialChangeAlgEquiv y₀ r hr f, ?_, ?_⟩
    · exact (MvPolynomial.mem_restrictTotalDegree (Fin N) k _).2 <|
        (totalDegree_affinePolynomialChange y₀ r hr f).trans_le
          ((MvPolynomial.mem_restrictTotalDegree (Fin N) k f).1 hf)
    · rfl
  · intro hz
    rcases hz with ⟨g, hg, rfl⟩
    let f := (affinePolynomialChangeAlgEquiv y₀ r hr).symm g
    refine ⟨Ideal.Quotient.mk I f, ?_, ?_⟩
    · refine ⟨f, ?_, rfl⟩
      have hdegree : f.totalDegree = g.totalDegree := by
        rw [← totalDegree_affinePolynomialChange y₀ r hr f]
        simp [f]
      exact (MvPolynomial.mem_restrictTotalDegree (Fin N) k _).2 <|
        hdegree.trans_le
          ((MvPolynomial.mem_restrictTotalDegree (Fin N) k g).1 hg)
    · change (Ideal.Quotient.mkₐ K _)
          (affinePolynomialChangeAlgEquiv y₀ r hr f) =
        (Ideal.Quotient.mkₐ K _) g
      simp [f]

/-- Every filtered affine Hilbert space has the same dimension after an
invertible affine change of coordinates. -/
theorem affineHilbertFiltration_finrank_affinePolynomialChange
    (I : Ideal (MvPolynomial (Fin N) K)) (y₀ : Fin N → K)
    (r : K) (hr : r ≠ 0) (k : ℕ) :
    Module.finrank K (affineHilbertFiltration K N I k) =
      Module.finrank K (affineHilbertFiltration K N
        (I.map (affinePolynomialChangeAlgEquiv y₀ r hr)) k) := by
  rw [← affineHilbertFiltration_map_affinePolynomialChange I y₀ r hr k]
  exact (LinearEquiv.finrank_map_eq
    (affinePolynomialChangeQuotientAlgEquiv y₀ r hr I).toLinearEquiv
    (affineHilbertFiltration K N I k)).symm

/-- The literal affine dimension-and-degree predicate is invariant under an
invertible affine change. -/
theorem hasAffineDimensionDegree_map_affinePolynomialChange_iff
    (I : Ideal (MvPolynomial (Fin N) K)) (y₀ : Fin N → K)
    (r : K) (hr : r ≠ 0) (n d : ℕ) :
    HasAffineDimensionDegree
        (I.map (affinePolynomialChangeAlgEquiv y₀ r hr)) n d ↔
      HasAffineDimensionDegree I n d := by
  constructor
  · rintro ⟨hprime, hdim, hd, P, hPdeg, hPlc, k₀, hP⟩
    refine ⟨?_, ?_, hd, P, hPdeg, hPlc, k₀, ?_⟩
    · rw [← affinePolynomialChange_comap_map y₀ r hr I]
      exact hprime.comap _
    · simpa [affinePolynomialChange_quotient_ringKrullDim_eq y₀ r hr I] using hdim
    · intro k hk
      rw [affineHilbertFiltration_finrank_affinePolynomialChange I y₀ r hr k]
      exact hP k hk
  · rintro ⟨hprime, hdim, hd, P, hPdeg, hPlc, k₀, hP⟩
    refine ⟨?_, ?_, hd, P, hPdeg, hPlc, k₀, ?_⟩
    · letI : I.IsPrime := hprime
      exact affinePolynomialChange_map_isPrime y₀ r hr I
    · simpa [← affinePolynomialChange_quotient_ringKrullDim_eq y₀ r hr I] using hdim
    · intro k hk
      rw [← affineHilbertFiltration_finrank_affinePolynomialChange I y₀ r hr k]
      exact hP k hk

/-- The Hilbert-polynomial-only affine dimension-and-degree predicate is
likewise invariant under an invertible affine change. -/
theorem hasAffineHilbertDimensionDegree_map_affinePolynomialChange_iff
    (I : Ideal (MvPolynomial (Fin N) K)) (y₀ : Fin N → K)
    (r : K) (hr : r ≠ 0) (n d : ℕ) :
    HasAffineHilbertDimensionDegree
        (I.map (affinePolynomialChangeAlgEquiv y₀ r hr)) n d ↔
      HasAffineHilbertDimensionDegree I n d := by
  constructor
  · rintro ⟨hprime, hd, P, hPdeg, hPlc, k₀, hP⟩
    refine ⟨?_, hd, P, hPdeg, hPlc, k₀, ?_⟩
    · rw [← affinePolynomialChange_comap_map y₀ r hr I]
      exact hprime.comap _
    · intro k hk
      rw [affineHilbertFiltration_finrank_affinePolynomialChange I y₀ r hr k]
      exact hP k hk
  · rintro ⟨hprime, hd, P, hPdeg, hPlc, k₀, hP⟩
    refine ⟨?_, hd, P, hPdeg, hPlc, k₀, ?_⟩
    · letI : I.IsPrime := hprime
      exact affinePolynomialChange_map_isPrime y₀ r hr I
    · intro k hk
      rw [← affineHilbertFiltration_finrank_affinePolynomialChange I y₀ r hr k]
      exact hP k hk

/-! ## Cumulative Hilbert polynomials of homogeneous quotients -/

/-- The polynomial whose value at `n` is `∑_{k<n} k^j`. -/
def powerSumPolynomial (j : ℕ) : Polynomial ℚ :=
  Polynomial.C ((j + 1 : ℚ)⁻¹) *
    (Polynomial.bernoulli (j + 1) - Polynomial.C (_root_.bernoulli (j + 1)))

/-- The Bernoulli polynomial has exactly its displayed degree and is monic.
This is extracted directly from the coefficient formula in Mathlib. -/
theorem bernoulliPolynomial_monic (j : ℕ) :
    (Polynomial.bernoulli j).Monic := by
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one j
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [Polynomial.coeff_bernoulli]
    simp [Nat.not_le_of_lt hm]
  · rw [Polynomial.coeff_bernoulli]
    simp

theorem bernoulliPolynomial_natDegree (j : ℕ) :
    (Polynomial.bernoulli j).natDegree = j := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [Polynomial.coeff_bernoulli]
    simp [Nat.not_le_of_lt hm]
  · rw [Polynomial.coeff_bernoulli]
    simp

theorem powerSumPolynomial_eval (j n : ℕ) :
    (powerSumPolynomial j).eval (n : ℚ) =
      ∑ k ∈ Finset.range n, (k : ℚ) ^ j := by
  rw [powerSumPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_C]
  rw [← Polynomial.sum_range_pow_eq_bernoulli_sub n j]
  field_simp

theorem powerSumPolynomial_natDegree (j : ℕ) :
    (powerSumPolynomial j).natDegree = j + 1 := by
  rw [powerSumPolynomial]
  have hdegree :
      (Polynomial.bernoulli (j + 1) -
        Polynomial.C (_root_.bernoulli (j + 1))).natDegree = j + 1 := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · exact (Polynomial.natDegree_sub_le _ _).trans <|
        max_le (bernoulliPolynomial_natDegree (j + 1)).le (by simp)
    · rw [Polynomial.coeff_sub, Polynomial.coeff_bernoulli]
      simp
  rw [Polynomial.natDegree_C_mul]
  · exact hdegree
  · positivity

theorem powerSumPolynomial_leadingCoeff (j : ℕ) :
    (powerSumPolynomial j).leadingCoeff = (j + 1 : ℚ)⁻¹ := by
  rw [Polynomial.leadingCoeff, powerSumPolynomial_natDegree, powerSumPolynomial,
    Polynomial.coeff_C_mul, Polynomial.coeff_sub]
  rw [Polynomial.coeff_bernoulli]
  simp

/-- Coefficientwise discrete integration of a rational polynomial. -/
def discreteIntegralPolynomial (P : Polynomial ℚ) : Polynomial ℚ :=
  ∑ j ∈ Finset.range (P.natDegree + 1),
    Polynomial.C (P.coeff j) * powerSumPolynomial j

theorem discreteIntegralPolynomial_eval (P : Polynomial ℚ) (n : ℕ) :
    (discreteIntegralPolynomial P).eval (n : ℚ) =
      ∑ k ∈ Finset.range n, P.eval (k : ℚ) := by
  rw [discreteIntegralPolynomial, Polynomial.eval_finset_sum]
  simp_rw [Polynomial.eval_mul, Polynomial.eval_C, powerSumPolynomial_eval]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.eval_eq_sum_range]

theorem discreteIntegralPolynomial_natDegree_le (P : Polynomial ℚ) :
    (discreteIntegralPolynomial P).natDegree ≤ P.natDegree + 1 := by
  rw [discreteIntegralPolynomial]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  refine (Polynomial.natDegree_mul_le).trans ?_
  rw [powerSumPolynomial_natDegree]
  simp only [Polynomial.natDegree_C, zero_add]
  have hjlt : j < P.natDegree + 1 := Finset.mem_range.mp hj
  omega

theorem discreteIntegralPolynomial_coeff_succ_natDegree (P : Polynomial ℚ) :
    (discreteIntegralPolynomial P).coeff (P.natDegree + 1) =
      P.leadingCoeff * (P.natDegree + 1 : ℚ)⁻¹ := by
  rw [discreteIntegralPolynomial, Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single P.natDegree]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_natDegree,
      ← powerSumPolynomial_natDegree P.natDegree,
      Polynomial.coeff_natDegree, powerSumPolynomial_leadingCoeff]
  · intro j hj hne
    rw [Polynomial.coeff_C_mul]
    have hj : j < P.natDegree :=
      (Nat.le_of_lt_succ (Finset.mem_range.mp hj)).lt_of_ne hne
    have hdegree : (powerSumPolynomial j).natDegree < P.natDegree + 1 := by
      rw [powerSumPolynomial_natDegree]
      omega
    simp [Polynomial.coeff_eq_zero_of_natDegree_lt hdegree]
  · simp

theorem discreteIntegralPolynomial_natDegree
    (P : Polynomial ℚ) (hP : P ≠ 0) :
    (discreteIntegralPolynomial P).natDegree = P.natDegree + 1 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (discreteIntegralPolynomial_natDegree_le P)
  rw [discreteIntegralPolynomial_coeff_succ_natDegree]
  exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hP)
    (inv_ne_zero (by positivity))

theorem discreteIntegralPolynomial_leadingCoeff
    (P : Polynomial ℚ) (hP : P ≠ 0) :
    (discreteIntegralPolynomial P).leadingCoeff =
      P.leadingCoeff / (P.natDegree + 1 : ℚ) := by
  rw [Polynomial.leadingCoeff, discreteIntegralPolynomial_natDegree P hP,
    discreteIntegralPolynomial_coeff_succ_natDegree, div_eq_mul_inv]

/-- Add the endpoint `n` and an arbitrary constant correction to a discrete
integral.  This is the form needed for a cumulative Hilbert function. -/
def cumulativePolynomial (P : Polynomial ℚ) (A : ℚ) : Polynomial ℚ :=
  (discreteIntegralPolynomial P).comp
    (Polynomial.X + Polynomial.C 1) + Polynomial.C A

theorem cumulativePolynomial_eval (P : Polynomial ℚ) (A : ℚ) (n : ℕ) :
    (cumulativePolynomial P A).eval (n : ℚ) =
      (∑ k ∈ Finset.range (n + 1), P.eval (k : ℚ)) + A := by
  rw [cumulativePolynomial, Polynomial.eval_add, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  simp only [Polynomial.eval_C]
  congr 1
  convert discreteIntegralPolynomial_eval P (n + 1) using 1
  norm_num

theorem cumulativePolynomial_natDegree
    (P : Polynomial ℚ) (A : ℚ) (hP : P ≠ 0) :
    (cumulativePolynomial P A).natDegree = P.natDegree + 1 := by
  rw [cumulativePolynomial, Polynomial.natDegree_add_C,
    Polynomial.natDegree_comp, discreteIntegralPolynomial_natDegree P hP,
    Polynomial.natDegree_X_add_C]
  omega

theorem cumulativePolynomial_leadingCoeff
    (P : Polynomial ℚ) (A : ℚ) (hP : P ≠ 0) :
    (cumulativePolynomial P A).leadingCoeff =
      P.leadingCoeff / (P.natDegree + 1 : ℚ) := by
  let S := (discreteIntegralPolynomial P).comp
    (Polynomial.X + Polynomial.C 1)
  have hlinearDegree :
      (Polynomial.X + Polynomial.C (1 : ℚ)).natDegree = 1 :=
    Polynomial.natDegree_X_add_C 1
  have hSdegree : S.natDegree = P.natDegree + 1 := by
    dsimp only [S]
    rw [Polynomial.natDegree_comp,
      discreteIntegralPolynomial_natDegree P hP, hlinearDegree]
    omega
  have hSdegree_ne : S.natDegree ≠ 0 := by rw [hSdegree]; omega
  have hSlc : S.leadingCoeff =
      P.leadingCoeff / (P.natDegree + 1 : ℚ) := by
    dsimp only [S]
    rw [Polynomial.leadingCoeff_comp (by omega :
      (Polynomial.X + Polynomial.C (1 : ℚ)).natDegree ≠ 0)]
    rw [Polynomial.leadingCoeff_X_add_C, one_pow, mul_one,
      discreteIntegralPolynomial_leadingCoeff P hP]
  rw [cumulativePolynomial]
  change (S + Polynomial.C A).leadingCoeff = _
  rw [Polynomial.leadingCoeff, Polynomial.natDegree_add_C,
    Polynomial.coeff_add, Polynomial.coeff_C, if_neg hSdegree_ne,
    add_zero, Polynomial.coeff_natDegree, hSlc]

/-- The finite ordered set `{0,...,n}` is identified with `Fin (n+1)`. -/
def natIicEquivFin (n : ℕ) : Set.Iic n ≃ Fin (n + 1) where
  toFun k := ⟨k.1, Nat.lt_succ_iff.mpr k.2⟩
  invFun k := ⟨k.1, Nat.le_of_lt_succ k.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sum_Iic_eq_sum_range_succ {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (n : ℕ) :
    (∑ k : Set.Iic n, f k.1) = ∑ k ∈ Finset.range (n + 1), f k := by
  calc
    (∑ k : Set.Iic n, f k.1) = ∑ k : Fin (n + 1), f k.1 :=
      Fintype.sum_equiv (natIicEquivFin n) _ _ (fun _ ↦ rfl)
    _ = ∑ k ∈ Finset.range (n + 1), f k := Fin.sum_univ_eq_sum_range f (n + 1)

/-- For a homogeneous ideal, the affine cumulative filtration is the sum of
the literal projective Hilbert pieces. -/
theorem affineHilbertFiltration_finrank_eq_sum_projectiveHilbertPiece
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K))
    (n : ℕ) :
    Module.finrank K (affineHilbertFiltration K (N + 1) I n) =
      ∑ k ∈ Finset.range (n + 1),
        Module.finrank K (projectiveHilbertPiece K N I k) := by
  have h := finrank_quotientTotalDegreeFiltration_eq_sum_homogeneousComponent
    K (Fin (N + 1)) I hI n
  change Module.finrank K (affineHilbertFiltration K (N + 1) I n) =
    ∑ k : Set.Iic n, Module.finrank K (projectiveHilbertPiece K N I k.1) at h
  calc
    Module.finrank K (affineHilbertFiltration K (N + 1) I n) =
        ∑ k : Set.Iic n,
          Module.finrank K (projectiveHilbertPiece K N I k.1) := h
    _ = ∑ k ∈ Finset.range (n + 1),
          Module.finrank K (projectiveHilbertPiece K N I k) :=
      sum_Iic_eq_sum_range_succ
        (fun k ↦ Module.finrank K (projectiveHilbertPiece K N I k)) n

/-- Summing an eventually polynomial sequence gives the explicitly
constructed cumulative polynomial; the finitely many initial values merely
alter its constant term. -/
theorem sum_range_succ_eq_cumulativePolynomial_eval_of_eventually
    (f : ℕ → ℚ) (P : Polynomial ℚ) (k₀ n : ℕ)
    (hn : k₀ ≤ n) (hf : ∀ k ≥ k₀, f k = P.eval (k : ℚ)) :
    ∑ k ∈ Finset.range (n + 1), f k =
      (cumulativePolynomial P
        ((∑ k ∈ Finset.range k₀, f k) -
          ∑ k ∈ Finset.range k₀, P.eval (k : ℚ))).eval (n : ℚ) := by
  have hk₀ : k₀ ≤ n + 1 := hn.trans (Nat.le_succ n)
  have htail :
      (∑ k ∈ Finset.Ico k₀ (n + 1), f k) =
        ∑ k ∈ Finset.Ico k₀ (n + 1), P.eval (k : ℚ) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hf k (Finset.mem_Ico.mp hk).1
  rw [cumulativePolynomial_eval]
  calc
    (∑ k ∈ Finset.range (n + 1), f k) =
        (∑ k ∈ Finset.range k₀, f k) +
          ∑ k ∈ Finset.Ico k₀ (n + 1), f k :=
      (Finset.sum_range_add_sum_Ico f hk₀).symm
    _ = (∑ k ∈ Finset.range k₀, f k) +
          ∑ k ∈ Finset.Ico k₀ (n + 1), P.eval (k : ℚ) := by rw [htail]
    _ = (∑ k ∈ Finset.range (n + 1), P.eval (k : ℚ)) +
          ((∑ k ∈ Finset.range k₀, f k) -
            ∑ k ∈ Finset.range k₀, P.eval (k : ℚ)) := by
      rw [← Finset.sum_range_add_sum_Ico
        (fun k ↦ P.eval (k : ℚ)) hk₀]
      ring

/-- Positivity of the degree is part of the literal projective
dimension-and-degree predicate. -/
theorem projectiveDegree_pos_of_hasProjectiveDimensionDegree
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (r d : ℕ)
    (hproj : HasProjectiveDimensionDegree I r d) : 0 < d :=
  hproj.2.1

/-- Cumulative Hilbert-polynomial passage without the redundant separate
Krull-dimension conjunct. -/
theorem hasAffineHilbertDimensionDegree_of_homogeneous_hasProjectiveHilbertDimensionDegree
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K))
    (hprime : I.IsPrime) (r d : ℕ)
    (hproj : HasProjectiveHilbertDimensionDegree I r d) :
    HasAffineHilbertDimensionDegree I (r + 1) d := by
  rcases hproj with ⟨hd, P, hPdegree, hPlc, k₀, hPeventual⟩
  have hPne : P ≠ 0 := by
    rw [← Polynomial.leadingCoeff_ne_zero, hPlc]
    exact div_ne_zero (by exact_mod_cast hd.ne') (by
      exact_mod_cast Nat.factorial_ne_zero r)
  let A : ℚ :=
    (∑ k ∈ Finset.range k₀,
      (Module.finrank K (projectiveHilbertPiece K N I k) : ℚ)) -
      ∑ k ∈ Finset.range k₀, P.eval (k : ℚ)
  let Q := cumulativePolynomial P A
  refine ⟨hprime, hd, Q, ?_, ?_, k₀, ?_⟩
  · dsimp only [Q]
    rw [cumulativePolynomial_natDegree P A hPne, hPdegree]
  · dsimp only [Q]
    rw [cumulativePolynomial_leadingCoeff P A hPne, hPdegree, hPlc,
      Nat.factorial_succ]
    norm_num [div_eq_mul_inv]
    ring
  · intro n hn
    rw [affineHilbertFiltration_finrank_eq_sum_projectiveHilbertPiece I hI n]
    push_cast
    dsimp only [Q, A]
    exact sum_range_succ_eq_cumulativePolynomial_eval_of_eventually
      (fun k ↦ (Module.finrank K
        (projectiveHilbertPiece K N I k) : ℚ)) P k₀ n hn hPeventual

/-- Passing from a homogeneous prime project's Hilbert polynomial to the
cumulative affine Hilbert polynomial raises the dimension by one and leaves
the degree unchanged. -/
private theorem hasAffineDimensionDegree_of_homogeneous_hasProjectiveDimensionDegree_of_pos
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K))
    (hprime : I.IsPrime) (r d : ℕ) (hd : 0 < d)
    (hproj : HasProjectiveDimensionDegree I r d) :
    HasAffineDimensionDegree I (r + 1) d := by
  rcases hproj with ⟨hdim, _hd, P, hPdegree, hPlc, k₀, hPeventual⟩
  have hPne : P ≠ 0 := by
    rw [← Polynomial.leadingCoeff_ne_zero, hPlc]
    exact div_ne_zero (by exact_mod_cast hd.ne') (by
      exact_mod_cast Nat.factorial_ne_zero r)
  let A : ℚ :=
    (∑ k ∈ Finset.range k₀,
      (Module.finrank K (projectiveHilbertPiece K N I k) : ℚ)) -
      ∑ k ∈ Finset.range k₀, P.eval (k : ℚ)
  let Q := cumulativePolynomial P A
  refine ⟨hprime, hdim, hd, Q, ?_, ?_, k₀, ?_⟩
  · dsimp only [Q]
    rw [cumulativePolynomial_natDegree P A hPne, hPdegree]
  · dsimp only [Q]
    rw [cumulativePolynomial_leadingCoeff P A hPne, hPdegree, hPlc,
      Nat.factorial_succ]
    norm_num [div_eq_mul_inv]
    ring
  · intro n hn
    rw [affineHilbertFiltration_finrank_eq_sum_projectiveHilbertPiece I hI n]
    push_cast
    dsimp only [Q, A]
    exact sum_range_succ_eq_cumulativePolynomial_eval_of_eventually
      (fun k ↦ (Module.finrank K
        (projectiveHilbertPiece K N I k) : ℚ)) P k₀ n hn hPeventual

/-- A homogeneous prime ideal has the same degree as its affine cone, while
the cumulative affine Hilbert polynomial has degree one larger than the
projective Hilbert polynomial. -/
theorem hasAffineDimensionDegree_of_homogeneous_hasProjectiveDimensionDegree
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K))
    (hprime : I.IsPrime) (r d : ℕ)
    (hproj : HasProjectiveDimensionDegree I r d) :
    HasAffineDimensionDegree I (r + 1) d :=
  hasAffineDimensionDegree_of_homogeneous_hasProjectiveDimensionDegree_of_pos
    I hI hprime r d
      (projectiveDegree_pos_of_hasProjectiveDimensionDegree
        I r d hproj) hproj

end Published

end

end TranslatedDepthSeven
