import CubicTenVariables.CubicMassEquations
import CubicTenVariables.FixedEquationPrimeCount
import CubicTenVariables.HessianRankOneReduction

/-! Fixed integral equation families for actual on-cubic Hessian rank
loci. All primes are included in the resulting ten-variable rank-two
and rank-three counts; the constants precede the prime. -/

noncomputable section
namespace CubicTenVariables.OnCubicLowRankEquations
open MvPolynomial HessianTheorem11

/-- A finite list of every possible minor size up to the matrix size,
with one additional index for the cubic equation itself. Repeated rows
and columns are harmless. -/
abbrev EquationIndex (n : ℕ) :=
  Option (Σ k : Fin (n+1), (Fin k.val → Fin n) × (Fin k.val → Fin n))

variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

/-- Minors of size at most r contribute the zero polynomial. In particular,
the empty determinant never adds an unintended unit equation. -/
def equation (F : MvPolynomial (Fin n) R) (r : ℕ) :
    EquationIndex n → MvPolynomial (Fin n) R
  | none => F
  | some ⟨k, rows, cols⟩ =>
      if r < k.val then ((hessianPolynomial F).submatrix rows cols).det else 0

/-- Reindex the finite family for the uniform fixed-equation count API. -/
def equations (F : MvPolynomial (Fin n) R) (r : ℕ)
    (i : Fin (Fintype.card (EquationIndex n))) : MvPolynomial (Fin n) R :=
  equation F r ((Fintype.equivFin (EquationIndex n)).symm i)

theorem map_equation (f : R →+* S) (F : MvPolynomial (Fin n) R)
    (r : ℕ) (i : EquationIndex n) :
    map f (equation F r i) = equation (map f F) r i := by
  cases i with
  | none => rfl
  | some i =>
    rcases i with ⟨k, rows, cols⟩
    by_cases hk : r < k.val
    · simp only [equation, hk, if_true]
      rw [(map f).map_det]
      congr 1
      ext a b
      simp [hessianPolynomial, pderiv_map]
    · simp [equation, hk]

theorem map_equations (f : R →+* S) (F : MvPolynomial (Fin n) R)
    (r : ℕ) (i : Fin (Fintype.card (EquationIndex n))) :
    map f (equations F r i) = equations (map f F) r i :=
  map_equation f F r _

/-- Literal common zeros are exactly F=0 and the actual Hessian rank bound. -/
theorem equation_zero_iff {K : Type*} [Field K]
    (f : R →+* K) (F : MvPolynomial (Fin n) R) (r : ℕ) (x : Fin n → K) :
    (∀ i, eval₂ f x (equation F r i) = 0) ↔
      eval₂ f x F = 0 ∧ (hessian (map f F) x).rank ≤ r := by
  constructor
  · intro hx
    refine ⟨hx none, ?_⟩
    by_contra hr
    have hrr : r < (hessian (map f F) x).rank := Nat.lt_of_not_ge hr
    obtain ⟨rows, cols, hd⟩ := MatrixRankMinors.exists_rank_minor (hessian (map f F) x)
    let k : Fin (n+1) := ⟨(hessian (map f F) x).rank,
      Nat.lt_succ_of_le (Matrix.rank_le_width _)⟩
    have he := hx (some ⟨k, rows, cols⟩)
    have hk : r < k.val := hrr
    simp only [equation, hk, if_true] at he
    rw [HessianRankOneReduction.eval₂_minor] at he
    exact hd he
  · rintro ⟨hF, hr⟩ i
    cases i with
    | none => exact hF
    | some i =>
      rcases i with ⟨k, rows, cols⟩
      by_cases hk : r < k.val
      · simp only [equation, hk, if_true]
        rw [HessianRankOneReduction.eval₂_minor]
        by_contra hd
        have hs := MatrixRankMinors.minor_size_le_rank
          (hessian (map f F) x) rows cols hd
        omega
      · simp [equation, hk]

theorem equations_zero_iff {K : Type*} [Field K]
    (f : R →+* K) (F : MvPolynomial (Fin n) R) (r : ℕ) (x : Fin n → K) :
    (∀ i, eval₂ f x (equations F r i) = 0) ↔
      eval₂ f x F = 0 ∧ (hessian (map f F) x).rank ≤ r := by
  rw [← equation_zero_iff f F r x]
  constructor
  · intro h i
    simpa [equations] using h ((Fintype.equivFin (EquationIndex n)) i)
  · intro h i
    exact h _

/-- The actual integral family, mapped to the rational coefficient field. -/
def rationalIdeal (F : MvPolynomial (Fin n) ℤ) (r : ℕ) :
    Ideal (MvPolynomial (Fin n) ℚ) :=
  Ideal.span (Set.range (fun i => map (Int.castRingHom ℚ) (equations F r i)))

theorem rationalIdeal_ne_top (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (r : ℕ) : rationalIdeal F r ≠ ⊤ := by
  apply CubicMassEquations.equationIdeal_ne_top_of_zero _ 0
  have hzero := (equations_zero_iff (Int.castRingHom ℚ) F r 0).mpr
    (show eval₂ (Int.castRingHom ℚ) 0 F = 0 ∧
      (hessian (map (Int.castRingHom ℚ) F) 0).rank ≤ r from
      ⟨by rw [eval₂_eq_eval_map]
          exact eval_origin_of_positive_homogeneous (hF.map _) (by norm_num),
        by rw [hessian_zero (hF.map _), Matrix.rank_zero]; omega⟩)
  intro i
  simpa only [eval_map] using hzero i

/-- Actual geometric identification, including the cubic equation. -/
theorem geometric_zeroLocus_eq (F : MvPolynomial (Fin n) ℤ) (r : ℕ) :
    zeroLocus GeometricField ((rationalIdeal F r).map
      (map (algebraMap ℚ GeometricField))) =
      BibleLowRank.onCubicRankLocus
        (geometricPolynomial (map (Int.castRingHom ℚ) F)) r := by
  change zeroLocus GeometricField
    ((CubicMassEquations.equationIdeal
      (fun i => map (Int.castRingHom ℚ) (equations F r i))).map _) = _
  rw [CubicMassEquations.map_equationIdeal]
  ext x
  rw [CubicMassEquations.mem_zeroLocus_equationIdeal]
  simp only [map_equations]
  have he := equations_zero_iff (RingHom.id GeometricField)
    (geometricPolynomial (map (Int.castRingHom ℚ) F)) r x
  simpa only [geometricPolynomial, eval₂_id, map_id,
    BibleLowRank.onCubicRankLocus, Set.mem_setOf_eq] using he

/-- The proved radial geometry gives the rational equation quotient bound. -/
theorem quotient_dimension_le (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F))
    (r : ℕ) (hr : 1 ≤ r) :
    ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸ rationalIdeal F r) ≤
      ((2*r-2 : ℕ) : Dimension) := by
  rw [← RationalEquationDimension.rational_quotient_dimension_eq_geometric_zeroLocus
    _ (rationalIdeal_ne_top F hF r), geometric_zeroLocus_eq]
  let Q : AnisotropicCubic 10 := ⟨map (Int.castRingHom ℚ) F, hF.map _, hA⟩
  exact BibleLowRank.on_cubic_rank_dimension_le
    Unconditional.concentrationGeometry.toAffineComponentsInput
    Unconditional.genericConePointSelection provedSymmetricDeterminantalTangent
    (geometricPolynomial Q.polynomial) (geometric_homogeneous Q.homogeneous)
    (UnconditionalWeightDescent.anisotropic_geometric_weightSemistable Q (by norm_num)) r hr

/-- Finite-prime common zeros are the literal on-cubic rank locus. -/
theorem zeroCount_eq (F : MvPolynomial (Fin n) ℤ) (r p : ℕ) [Fact p.Prime] :
    IntegralEquationCounts.zeroCount (equations F r) p =
      Nat.card {x : Fin n → ZMod p //
        eval₂ (Int.castRingHom (ZMod p)) x F = 0 ∧
        (hessian (map (Int.castRingHom (ZMod p)) F) x).rank ≤ r} := by
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun x => equations_zero_iff _ F r x

/-- One constant precedes every prime, including exceptional primes. -/
theorem exists_uniform_rank_count_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) (r : ℕ) (hr : 1 ≤ r) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) [Fact p.Prime],
      Nat.card {x : Fin 10 → ZMod p //
        eval₂ (Int.castRingHom (ZMod p)) x F = 0 ∧
        (hessian (map (Int.castRingHom (ZMod p)) F) x).rank ≤ r} ≤ C*p^(2*r-2) := by
  obtain ⟨C, hC, hc⟩ := FixedEquationPrimeCount.exists_uniform_bound
    (equations F r) (rationalIdeal_ne_top F hF r) (quotient_dimension_le F hF hA r hr)
  refine ⟨C, hC, ?_⟩
  intro p hp
  rw [← zeroCount_eq]
  exact hc p hp.out

theorem exists_uniform_rank_two_count_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) [Fact p.Prime],
      Nat.card {x : Fin 10 → ZMod p //
        eval₂ (Int.castRingHom (ZMod p)) x F = 0 ∧
        (hessian (map (Int.castRingHom (ZMod p)) F) x).rank ≤ 2} ≤ C*p^2 := by
  simpa using exists_uniform_rank_count_bound F hF hA 2 (by norm_num)

theorem exists_uniform_rank_three_count_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) [Fact p.Prime],
      Nat.card {x : Fin 10 → ZMod p //
        eval₂ (Int.castRingHom (ZMod p)) x F = 0 ∧
        (hessian (map (Int.castRingHom (ZMod p)) F) x).rank ≤ 3} ≤ C*p^4 := by
  simpa using exists_uniform_rank_count_bound F hF hA 3 (by norm_num)

/-- Exact rank is a subset of the closed rank-at-most locus. -/
theorem exact_rank_count_le (F : MvPolynomial (Fin n) ℤ) (r p : ℕ) [Fact p.Prime] :
    Nat.card {x : Fin n → ZMod p //
      eval₂ (Int.castRingHom (ZMod p)) x F = 0 ∧
      (hessian (map (Int.castRingHom (ZMod p)) F) x).rank = r} ≤
    Nat.card {x : Fin n → ZMod p //
      eval₂ (Int.castRingHom (ZMod p)) x F = 0 ∧
      (hessian (map (Int.castRingHom (ZMod p)) F) x).rank ≤ r} := by
  apply Nat.card_le_card_of_injective
    (fun x => ⟨x.val, x.property.1, x.property.2.le⟩)
  intro x y h
  simpa only [Subtype.ext_iff] using h

theorem exists_uniform_exact_rank_count_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) (r : ℕ) (hr : 1 ≤ r) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) [Fact p.Prime],
      Nat.card {x : Fin 10 → ZMod p //
        eval₂ (Int.castRingHom (ZMod p)) x F = 0 ∧
        (hessian (map (Int.castRingHom (ZMod p)) F) x).rank = r} ≤ C*p^(2*r-2) := by
  obtain ⟨C, hC, hc⟩ := exists_uniform_rank_count_bound F hF hA r hr
  exact ⟨C, hC, fun p _ => (exact_rank_count_le F r p).trans (hc p)⟩

theorem exists_uniform_exact_rank_two_count_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) [Fact p.Prime],
      Nat.card {x : Fin 10 → ZMod p //
        eval₂ (Int.castRingHom (ZMod p)) x F = 0 ∧
        (hessian (map (Int.castRingHom (ZMod p)) F) x).rank = 2} ≤ C*p^2 := by
  simpa using exists_uniform_exact_rank_count_bound F hF hA 2 (by norm_num)

theorem exists_uniform_exact_rank_three_count_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) [Fact p.Prime],
      Nat.card {x : Fin 10 → ZMod p //
        eval₂ (Int.castRingHom (ZMod p)) x F = 0 ∧
        (hessian (map (Int.castRingHom (ZMod p)) F) x).rank = 3} ≤ C*p^4 := by
  simpa using exists_uniform_exact_rank_count_bound F hF hA 3 (by norm_num)

theorem exists_uniform_exact_rank_four_count_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) [Fact p.Prime],
      Nat.card {x : Fin 10 → ZMod p //
        eval₂ (Int.castRingHom (ZMod p)) x F = 0 ∧
        (hessian (map (Int.castRingHom (ZMod p)) F) x).rank = 4} ≤ C*p^6 := by
  simpa using exists_uniform_exact_rank_count_bound F hF hA 4 (by norm_num)

end CubicTenVariables.OnCubicLowRankEquations
