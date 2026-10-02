import CubicTenVariables.PadicLocalization
import CubicTenVariables.IntegralGradientFibers

/-!
# One integral high-rank coset with a uniform gradient-fiber bound

For an integer cubic anisotropic over ℚ, the displayed Pleasants argument
supplies the initial p-adic zero. All subsequent high-rank selection,
primitive normalization, preservation of exact polynomial norms, and local
finite gradient-fiber counts are proved. The two available cosets are
refined to their common smaller coset by taking the maximum exponent.

Every polynomial and minor below is that of the actual integer polynomial.
The selected rows and columns may differ. Only the center is asserted to
be a zero; the surrounding congruence coset need not consist of zeros.
-/

noncomputable section
namespace CubicTenVariables.IntegralHighRankLocalization

open MvPolynomial HessianTheorem11 RationalHessianMinor
open IntegralGradientFibers LocalCongruenceFibers

/-- Integer coefficients mapped through ℚ have their literal direct image. -/
theorem map_rational_image {K : Type*} [Field K] [Algebra ℚ K] {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) :
    map (algebraMap ℚ K) (map (Int.castRingHom ℚ) F) =
      map (Int.castRingHom K) F := by
  have hcomp : (algebraMap ℚ K).comp (Int.castRingHom ℚ) = Int.castRingHom K := by
    ext a
    simp
  rw [map_map, hcomp]

/-- Evaluation after the rational coefficient image is direct integer evaluation. -/
theorem eval₂_rational_image {K : Type*} [Field K] [Algebra ℚ K] {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (x : Fin n → K) :
    eval₂ (algebraMap ℚ K) x (map (Int.castRingHom ℚ) F) =
      eval₂ (Int.castRingHom K) x F := by
  rw [eval₂_map]
  congr 1
  ext a
  simp

/-- The actual first partials commute with the rational coefficient adapter. -/
theorem eval₂_partial_rational_image {K : Type*} [Field K] [Algebra ℚ K] {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (i : Fin n) (x : Fin n → K) :
    eval₂ (algebraMap ℚ K) x (pderiv i (map (Int.castRingHom ℚ) F)) =
      eval₂ (Int.castRingHom K) x (pderiv i F) := by
  rw [pderiv_map, eval₂_rational_image]

/-- The selected rational-image minor is the actual integer minor after evaluation. -/
theorem eval₂_minor_rational_image {K : Type*} [Field K] [Algebra ℚ K] {n r : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (rows cols : Fin r → Fin n) (x : Fin n → K) :
    eval₂ (algebraMap ℚ K) x (hessianMinor (map (Int.castRingHom ℚ) F) rows cols) =
      eval₂ (Int.castRingHom K) x (hessianMinor F rows cols) := by
  rw [eval₂_hessianMinor, eval₂_hessianMinor, map_rational_image]

/-- A larger exponent defines a smaller literal integral congruence coset. -/
theorem integral_coset_subset_of_le (p : ℕ) [Fact p.Prime] {n : ℕ}
    (ξ : Fin n → ℤ_[p]) {M N : ℕ} (hMN : M ≤ N) :
    Set.range (fun t : Fin n → ℤ_[p] => ξ + (p : ℤ_[p]) ^ N • t) ⊆
      Set.range (fun t : Fin n → ℤ_[p] => ξ + (p : ℤ_[p]) ^ M • t) := by
  rintro z ⟨t, rfl⟩
  refine ⟨(p : ℤ_[p]) ^ (N - M) • t, ?_⟩
  dsimp only
  rw [smul_smul, ← pow_add, Nat.add_sub_of_le hMN]

/-- Restricting the patch cannot increase its actual unit-gradient fiber count. -/
theorem card_unitModularFiber_mono (p : ℕ) [Fact p.Prime] {n r : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (rows cols : Fin r → Fin n)
    (s : ℕ) {U V : Set (Fin n → ℤ_[p])} (hUV : U ⊆ V)
    (u : (ZMod (p ^ s))ˣ) (b : Untouched cols → ZMod (p ^ s))
    (c : Fin r → ZMod (p ^ s)) :
    Nat.card (unitModularFiber p F rows cols s U u b c) ≤
      Nat.card (unitModularFiber p F rows cols s V u b c) := by
  let f : unitModularFiber p F rows cols s U u b c →
      unitModularFiber p F rows cols s V u b c := fun v =>
    ⟨v.1, v.2.1, v.2.2.1, by
      obtain ⟨z, hz, hv⟩ := v.2.2.2
      exact ⟨z, hUV hz, hv⟩⟩
  apply Nat.card_le_card_of_injective f
  intro v w hvw
  apply Subtype.ext
  exact congrArg (fun t : unitModularFiber p F rows cols s V u b c => t.1) hvw

set_option maxHeartbeats 1000000 in
/-- Conditional only on the explicit Pleasants argument, all the local
geometric properties and the actual unit-gradient congruence bound hold
on one fixed integral coset. Its exponent and bound precede every modulus,
unit multiplier, and residue target. -/
theorem exists_integral_high_rank_localization
    (pleasants : Literature.Pleasants1971Theorem2Qp)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F))
    (p : ℕ) [Fact p.Prime] :
    ∃ (ξ : Fin 10 → ℤ_[p]) (i j : Fin 10) (r : ℕ)
      (rows cols : Fin r → Fin 10) (M A : ℕ),
      ξ j = 1 ∧
      eval₂ (Int.castRingHom ℚ_[p]) (fun k => (ξ k : ℚ_[p])) F = 0 ∧
      eval₂ (Int.castRingHom ℚ_[p]) (fun k => (ξ k : ℚ_[p])) (pderiv i F) ≠ 0 ∧
      8 ≤ r ∧
      r = (hessian (map (Int.castRingHom ℚ_[p]) F) (fun k => (ξ k : ℚ_[p]))).rank ∧
      1 ≤ M ∧
      eval₂ (Int.castRingHom ℚ_[p]) (fun k => (ξ k : ℚ_[p]))
        (hessianMinor F rows cols) ≠ 0 ∧
      (∀ z : Fin 10 → ℤ_[p],
        let η := ξ + (p : ℤ_[p]) ^ M • z
        IsUnit (η j) ∧
        ‖eval₂ (Int.castRingHom ℚ_[p]) (fun k => (η k : ℚ_[p])) (pderiv i F)‖ =
          ‖eval₂ (Int.castRingHom ℚ_[p]) (fun k => (ξ k : ℚ_[p])) (pderiv i F)‖ ∧
        ‖eval₂ (Int.castRingHom ℚ_[p]) (fun k => (η k : ℚ_[p]))
          (hessianMinor F rows cols)‖ =
          ‖eval₂ (Int.castRingHom ℚ_[p]) (fun k => (ξ k : ℚ_[p]))
            (hessianMinor F rows cols)‖ ∧
        eval₂ (Int.castRingHom ℚ_[p]) (fun k => (η k : ℚ_[p])) (pderiv i F) ≠ 0 ∧
        eval₂ (Int.castRingHom ℚ_[p]) (fun k => (η k : ℚ_[p]))
          (hessianMinor F rows cols) ≠ 0 ∧
        8 ≤ (hessian (map (Int.castRingHom ℚ_[p]) F) (fun k => (η k : ℚ_[p]))).rank) ∧
      ∀ (s : ℕ) (u : (ZMod (p ^ s))ˣ)
        (b : Untouched cols → ZMod (p ^ s)) (c : Fin r → ZMod (p ^ s)),
        Nat.card (unitModularFiber p F rows cols s
          (Set.range (fun t : Fin 10 → ℤ_[p] => ξ + (p : ℤ_[p]) ^ M • t)) u b c) ≤
            p ^ (A * r) := by
  let Fq : AnisotropicCubic 10 := ⟨map (Int.castRingHom ℚ) F, hF.map _, hA⟩
  obtain ⟨ξ, i, j, r, rows, cols, M₀, hj, hzero, hi, hr, hrank, hM₀, hminor, hnorms⟩ :=
    PadicLocalization.exists_primitive_high_rank_localization pleasants Fq p
  simp only [Fq, eval₂_rational_image, eval₂_partial_rational_image,
    eval₂_minor_rational_image, map_rational_image] at hzero hi hrank hminor hnorms
  have hdet : ((hessian (map (Int.castRingHom ℚ_[p]) F)
      (fun k => (ξ k : ℚ_[p]))).submatrix rows cols).det ≠ 0 := by
    rwa [← eval₂_hessianMinor]
  obtain ⟨M₁, A, hM₁, hcount⟩ :=
    exists_coset_uniform_unit_gradient_fiber_bound p F rows cols ξ hdet
  let M := max M₀ M₁
  have hM₀M : M₀ ≤ M := le_max_left _ _
  have hM₁M : M₁ ≤ M := le_max_right _ _
  refine ⟨ξ, i, j, r, rows, cols, M, A, hj, hzero, hi, hr, hrank,
    hM₀.trans hM₀M, hminor, ?_, ?_⟩
  · intro z
    have he : ξ + (p : ℤ_[p]) ^ M₀ • ((p : ℤ_[p]) ^ (M - M₀) • z) =
        ξ + (p : ℤ_[p]) ^ M • z := by
      rw [smul_smul, ← pow_add, Nat.add_sub_of_le hM₀M]
    simpa only [he] using hnorms ((p : ℤ_[p]) ^ (M - M₀) • z)
  · intro s u b c
    exact (card_unitModularFiber_mono p F rows cols s
      (integral_coset_subset_of_le p ξ hM₁M) u b c).trans (hcount s u b c)

end CubicTenVariables.IntegralHighRankLocalization
