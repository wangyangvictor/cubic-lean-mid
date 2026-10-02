import CubicTenVariables.OnCubicLowRankEquations
import CubicTenVariables.HessianRankStrataTen
import CubicTenVariables.UniformPrimePolynomialZeros
import CubicTenVariables.SmithProfileNumerics

/-! The complete initial finite-field rank profile for an anisotropic
integral cubic in ten variables. One constant precedes all primes and
all eleven rank labels. This is not a prime-power transition count. -/

noncomputable section
namespace CubicTenVariables.OnCubicRankCountsTen
open MvPolynomial HessianTheorem11 OnCubicLowRankEquations

/-- Natural exponent corresponding to the source's rational-valued delta. -/
def deltaNat (r : ℕ) : ℕ :=
  if r ≤ 1 then 0 else if r < 8 then min (2*r-2) (min (r+2) 8) else 9

theorem deltaNat_eq_delta (r : ℕ) (hr : r ≤ 10) :
    (deltaNat r : ℚ) = SmithProfileNumerics.delta r := by
  interval_cases r <;> norm_num [deltaNat, SmithProfileNumerics.delta]

/-- Inclusion into the ambient Hessian rank locus supplies the sharper
bounds needed at ranks five and six. -/
theorem quotient_dimension_le_rank_add_two (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F))
    (r : ℕ) (hr : r ≤ 9) :
    ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸ rationalIdeal F r) ≤
      ((min (r+2) 9 : ℕ) : Dimension) := by
  rw [← RationalEquationDimension.rational_quotient_dimension_eq_geometric_zeroLocus
    _ (rationalIdeal_ne_top F hF r), geometric_zeroLocus_eq]
  let Q : AnisotropicCubic 10 := ⟨map (Int.castRingHom ℚ) F, hF.map _, hA⟩
  have hs : BibleLowRank.onCubicRankLocus (geometricPolynomial Q.polynomial) r ⊆
      rankAtMostLocus Q.polynomial r := fun _ hx => hx.2
  exact (affineDimension_mono hs).trans (Geometry.hessianRankLocus_dimension_le_min Q r hr)

/-- Rank below eight defines a proper closed subset of the actual cubic. -/
theorem quotient_dimension_le_eight (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F))
    (r : ℕ) (hr : r < 8) :
    ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸ rationalIdeal F r) ≤ (8 : Dimension) := by
  rw [← RationalEquationDimension.rational_quotient_dimension_eq_geometric_zeroLocus
    _ (rationalIdeal_ne_top F hF r), geometric_zeroLocus_eq]
  let Q : AnisotropicCubic 10 := ⟨map (Int.castRingHom ℚ) F, hF.map _, hA⟩
  have hs : BibleLowRank.onCubicRankLocus (geometricPolynomial Q.polynomial) r =
      rankAtMostLocus Q.polynomial r ∩ cubicLocus Q.polynomial := by
    ext x
    exact and_comm
  rw [hs]
  exact Geometry.onCubic_hessianRankLocus_dimension_le_eight Q r hr

/-- Transfer a proved rational quotient bound for this literal equation
family. This helper does not add a dimension premise to the final result. -/
theorem exists_uniform_exact_rank_bound_of_dimension
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3) (r d : ℕ)
    (hd : ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸ rationalIdeal F r) ≤ (d : Dimension)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) [Fact p.Prime],
      Nat.card {x : Fin 10 → ZMod p // eval₂ (Int.castRingHom (ZMod p)) x F = 0 ∧
        (hessian (map (Int.castRingHom (ZMod p)) F) x).rank = r} ≤ C*p^d := by
  obtain ⟨C, hC, hc⟩ := FixedEquationPrimeCount.exists_uniform_bound
    (equations F r) (rationalIdeal_ne_top F hF r) hd
  refine ⟨C, hC, ?_⟩
  intro p hp
  apply (exact_rank_count_le F r p).trans
  rw [← zeroCount_eq]
  exact hc p hp.out

theorem exists_uniform_exact_rank_five_count_bound
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) [Fact p.Prime],
      Nat.card {x : Fin 10 → ZMod p // eval₂ (Int.castRingHom (ZMod p)) x F = 0 ∧
        (hessian (map (Int.castRingHom (ZMod p)) F) x).rank = 5} ≤ C*p^7 := by
  apply exists_uniform_exact_rank_bound_of_dimension F hF 5 7
  simpa using quotient_dimension_le_rank_add_two F hF hA 5 (by norm_num)

theorem exists_uniform_exact_rank_six_count_bound
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) [Fact p.Prime],
      Nat.card {x : Fin 10 → ZMod p // eval₂ (Int.castRingHom (ZMod p)) x F = 0 ∧
        (hessian (map (Int.castRingHom (ZMod p)) F) x).rank = 6} ≤ C*p^8 := by
  apply exists_uniform_exact_rank_bound_of_dimension F hF 6 8
  simpa using quotient_dimension_le_rank_add_two F hF hA 6 (by norm_num)

theorem exists_uniform_exact_rank_seven_count_bound
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) [Fact p.Prime],
      Nat.card {x : Fin 10 → ZMod p // eval₂ (Int.castRingHom (ZMod p)) x F = 0 ∧
        (hessian (map (Int.castRingHom (ZMod p)) F) x).rank = 7} ≤ C*p^8 := by
  exact exists_uniform_exact_rank_bound_of_dimension F hF 7 8
    (quotient_dimension_le_eight F hF hA 7 (by norm_num))

/-- Rank zero is also contained in the closed rank-at-most-one locus. -/
theorem exact_rank_count_le_rank_one (F : MvPolynomial (Fin 10) ℤ)
    (r p : ℕ) [Fact p.Prime] (hr : r ≤ 1) :
    Nat.card {x : Fin 10 → ZMod p // eval₂ (Int.castRingHom (ZMod p)) x F = 0 ∧
      (hessian (map (Int.castRingHom (ZMod p)) F) x).rank = r} ≤
    Nat.card {x : Fin 10 → ZMod p // eval₂ (Int.castRingHom (ZMod p)) x F = 0 ∧
      (hessian (map (Int.castRingHom (ZMod p)) F) x).rank ≤ 1} := by
  apply Nat.card_le_card_of_injective
    (fun x => ⟨x.val, x.property.1, x.property.2.le.trans hr⟩)
  intro x y h
  simpa only [Subtype.ext_iff] using h

/-- A per-rank constant, used only to construct the single uniform constant. -/
theorem exists_uniform_exact_rank_delta_bound
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) (r : ℕ) (hr : r ≤ 10) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) [Fact p.Prime],
      Nat.card {x : Fin 10 → ZMod p // eval₂ (Int.castRingHom (ZMod p)) x F = 0 ∧
        (hessian (map (Int.castRingHom (ZMod p)) F) x).rank = r} ≤ C*p^(deltaNat r) := by
  classical
  by_cases hr1 : r ≤ 1
  · obtain ⟨C, hC, hc⟩ := exists_uniform_rank_count_bound F hF hA 1 (by norm_num)
    refine ⟨C, hC, ?_⟩
    intro p hp
    simpa [deltaNat, hr1] using (exact_rank_count_le_rank_one F r p hr1).trans (hc p)
  · by_cases hr8 : r < 8
    · have hr2 : 2 ≤ r := by omega
      interval_cases r
      · simpa [deltaNat] using exists_uniform_exact_rank_two_count_bound F hF hA
      · simpa [deltaNat] using exists_uniform_exact_rank_three_count_bound F hF hA
      · simpa [deltaNat] using exists_uniform_exact_rank_four_count_bound F hF hA
      · simpa [deltaNat] using exists_uniform_exact_rank_five_count_bound F hF hA
      · simpa [deltaNat] using exists_uniform_exact_rank_six_count_bound F hF hA
      · simpa [deltaNat] using exists_uniform_exact_rank_seven_count_bound F hF hA
    · have hne : F ≠ 0 := by
        intro hz
        have he := hA (fun _ => 1) (by simp [hz])
        have hi := congrFun he (0 : Fin 10)
        norm_num at hi
      obtain ⟨C, hC, hc⟩ := UniformPrimePolynomialZeros.exists_uniform_ten_exact_rank_zero_bound F hne
      refine ⟨C, hC, ?_⟩
      intro p hp
      simpa only [deltaNat, if_neg hr1, if_neg hr8,
        Nat.card_eq_fintype_card, Fintype.card_subtype,
        UniformPrimePolynomialZeros.primeZeros,
        TranslatedDepthSeven.mvPolynomialZeroSet, Finset.filter_filter, eval_map] using hc p hp.out r

/-- The literal source initial-rank profile, with one constant before every
prime and every rank label from zero through ten. -/
theorem exists_uniform_exact_rank_profile
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) [Fact p.Prime], ∀ r : ℕ, r ≤ 10 →
      Nat.card {x : Fin 10 → ZMod p // eval₂ (Int.castRingHom (ZMod p)) x F = 0 ∧
        (hessian (map (Int.castRingHom (ZMod p)) F) x).rank = r} ≤ C*p^(deltaNat r) := by
  classical
  choose C hC hc using fun r : Fin 11 =>
    exists_uniform_exact_rank_delta_bound F hF hA r.val (by omega)
  have hle (r : Fin 11) : C r ≤ ∑ i : Fin 11, C i :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (C i)) (Finset.mem_univ r)
  refine ⟨∑ i : Fin 11, C i, (hC 0).trans (hle 0), ?_⟩
  intro p hp r hr
  let i : Fin 11 := ⟨r, by omega⟩
  exact (hc i p).trans (Nat.mul_le_mul_right _ (hle i))

end CubicTenVariables.OnCubicRankCountsTen
