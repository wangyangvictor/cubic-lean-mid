import CubicTenVariables.PrimePointwiseBoundsFromSurfacesReduced
import CubicTenVariables.PrimeSquarePointwiseBounds
import CubicTenVariables.CompleteSumMultiplicativity

/-! A conductor-free product bound for a fixed nonzero integer frequency.
The actual all-prime estimates and exact unchanged-frequency CRT yield
`C^(ω(a)+ω(b)) a^8 b^17 gcd(a, |v_i|)` for any nonzero coordinate.
The extra ordinary-prime factor is deliberately enlarged from p^(1/2)
to p; the later divisible power sum pays for this factor. No generic-frequency,
numerical-depth, or radical restriction is assumed. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ConductorNonzeroCoarseReduced
open MvPolynomial HessianTheorem11
open BihomogeneousIncidenceFamily ProjectiveMicrolocalData
open scoped BigOperators

private theorem exceptional_product_le_gcd (a c : ℕ) (ha : a ≠ 0) :
    (∏ p ∈ a.primeFactors, if p ∣ c then (p : ℝ) else 1) ≤ (a.gcd c : ℝ) := by
  have hg : a.gcd c ≠ 0 := (Nat.gcd_pos_of_pos_left c (Nat.pos_of_ne_zero ha)).ne'
  have hsub : a.primeFactors.filter (fun p => p ∣ c) ⊆ (a.gcd c).primeFactors := by
    intro p hp
    obtain ⟨hp,hpc⟩ := Finset.mem_filter.mp hp
    exact (Nat.prime_of_mem_primeFactors hp).mem_primeFactors
      (Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) hpc) hg
  have hd : (∏ p ∈ a.primeFactors.filter (fun p => p ∣ c), p) ∣ a.gcd c :=
    (Finset.prod_dvd_prod_of_subset _ _ (fun p : ℕ => p) hsub).trans
      (Nat.prod_primeFactors_dvd (a.gcd c))
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hg) hd
  rw [← Finset.prod_filter, ← Nat.cast_prod]
  exact_mod_cast hle

/-- The ordinary-prime exception is contained in the primes dividing the
absolute value of any selected integer coordinate. -/
theorem prime_bound {F : MvPolynomial (Fin 10) ℤ} {C : ℝ} (hC : 1 ≤ C)
    (p : ℕ) (hp : p.Prime) (v : Fin 10 → ℤ) (i : Fin 10)
    (hz : (fun j => (v j : ZMod p)) = 0 →
      ‖completeCubicSum F p v‖ ≤ C*(p : ℝ)^((17 : ℝ)/2))
    (hnz : (fun j => (v j : ZMod p)) ≠ 0 →
      ‖completeCubicSum F p v‖ ≤ C*(p : ℝ)^8) :
    ‖completeCubicSum F p v‖ ≤
      C*(p : ℝ)^8*(if p ∣ (v i).natAbs then (p : ℝ) else 1) := by
  have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  by_cases hpc : p ∣ (v i).natAbs
  · rw [if_pos hpc]
    by_cases hv : (fun j => (v j : ZMod p)) = 0
    · have hpow : (p : ℝ)^((17 : ℝ)/2) ≤ (p : ℝ)^9 := by
        simpa only [Real.rpow_ofNat] using
          Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num : (17 : ℝ)/2 ≤ 9)
      calc
        _ ≤ C*(p : ℝ)^((17 : ℝ)/2) := hz hv
        _ ≤ C*(p : ℝ)^9 := mul_le_mul_of_nonneg_left hpow hC0
        _ = _ := by ring
    · calc
        _ ≤ C*(p : ℝ)^8 := hnz hv
        _ ≤ C*(p : ℝ)^8*(p : ℝ) := le_mul_of_one_le_right (by positivity) hp1
  · rw [if_neg hpc,mul_one]
    apply hnz
    intro hv
    apply hpc
    apply Int.natCast_dvd.mp
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (v i) p).mp
    exact congrFun hv i

/-- Exact CRT assembles the actual local estimates. This algebraic helper
also holds when the selected coordinate is zero; the nonzero-coordinate
application below supplies a positive exceptional integer. -/
theorem complete_sum_bound {F : MvPolynomial (Fin 10) ℤ} {C : ℝ}
    (hF : F.IsHomogeneous 3) (hC : 1 ≤ C)
    (hprime : ∀ p : ℕ, p.Prime → ∀ v : Fin 10 → ℤ,
      ((fun j => (v j : ZMod p)) = 0 →
        ‖completeCubicSum F p v‖ ≤ C*(p : ℝ)^((17 : ℝ)/2)) ∧
      ((fun j => (v j : ZMod p)) ≠ 0 →
        ‖completeCubicSum F p v‖ ≤ C*(p : ℝ)^8))
    (hsquare : ∀ p : ℕ, p.Prime → ∀ v : Fin 10 → ℤ,
      ‖completeCubicSum F (p^2) v‖ ≤ C*(p : ℝ)^17)
    (v : Fin 10 → ℤ) (i : Fin 10) (a b : ℕ)
    (ha : Squarefree a) (hb : Squarefree b) (hab : a.Coprime b) :
    ‖completeCubicSum F (a*b^2) v‖ ≤
      C^(a.primeFactors.card+b.primeFactors.card)*
        (a : ℝ)^8*(b : ℝ)^17*(a.gcd (v i).natAbs : ℝ) := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hp := Finset.prod_le_prod (fun p (_ : p ∈ a.primeFactors) =>
      norm_nonneg (completeCubicSum F p v))
    (fun p hp => prime_bound hC p (Nat.prime_of_mem_primeFactors hp) v i
      (hprime p (Nat.prime_of_mem_primeFactors hp) v).1
      (hprime p (Nat.prime_of_mem_primeFactors hp) v).2)
  have hs := Finset.prod_le_prod (fun p (_ : p ∈ b.primeFactors) =>
      norm_nonneg (completeCubicSum F (p^2) v))
    (fun p hp => hsquare p (Nat.prime_of_mem_primeFactors hp) v)
  have hpa : (∏ p ∈ a.primeFactors, (p : ℝ)^8) = (a : ℝ)^8 := by
    rw [Finset.prod_pow, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree ha]
  have hpb : (∏ p ∈ b.primeFactors, (p : ℝ)^17) = (b : ℝ)^17 := by
    rw [Finset.prod_pow, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hb]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, hpa] at hp
  simp only [Finset.prod_mul_distrib, Finset.prod_const, hpb] at hs
  have hp' : (∏ p ∈ a.primeFactors, ‖completeCubicSum F p v‖) ≤
      C^a.primeFactors.card*(a : ℝ)^8*(a.gcd (v i).natAbs : ℝ) := by
    exact hp.trans (mul_le_mul_of_nonneg_left
      (exceptional_product_le_gcd a (v i).natAbs ha.ne_zero) (by positivity))
  rw [CompleteSumMultiplicativity.norm_squarefree_pair_product F hF a b ha hb hab v]
  calc
    _ ≤ (C^a.primeFactors.card*(a : ℝ)^8*(a.gcd (v i).natAbs : ℝ))*
        (C^b.primeFactors.card*(b : ℝ)^17) :=
      mul_le_mul hp' hs (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

/-- One constant is chosen before every integer frequency, its selected
nonzero coordinate and both squarefree modulus parts. All local estimates
are supplied by previously proved actual-sum theorems, with the existing
literature hypotheses, proved prime-field count interface and geometric data explicit. -/
theorem of_data (spread : CubicPrincipalOpenUniform.Uniform)
    (cubicWeil : Literature.SmoothCubicWeil) (isolated : CubicSurfacePointCountReduced.IsolatedConjugateCubicSurfacePointCount)
    (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    {t : ℕ} (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (f : Fin t → Polynomial 10 10) (N B : ℕ) (hN : 1 ≤ N)
    (hgeo : Geometry F f) (hData : TenMicrolocalIncidence.Conclusion F f N B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (v : Fin 10 → ℤ) (i : Fin 10), v i ≠ 0 →
      1 ≤ (v i).natAbs ∧ ∀ a b : ℕ, Squarefree a → Squarefree b → a.Coprime b →
      ‖completeCubicSum F (a*b^2) v‖ ≤
        C^(a.primeFactors.card+b.primeFactors.card)*
          (a : ℝ)^8*(b : ℝ)^17*(a.gcd (v i).natAbs : ℝ) := by
  obtain ⟨Cp,hCp,hp⟩ := PrimePointwiseBoundsFromSurfacesReduced.exists_uniform_bound spread isolated cubicWeil F hF hAn
  obtain ⟨Cs,hCs,hs,_⟩ := PrimeSquarePointwiseBounds.of_data pointcount F hF hAn f N B hN hgeo hData
  let C : ℝ := max Cp Cs
  have hC : 1 ≤ C := hCp.trans (le_max_left _ _)
  have hp' : ∀ p : ℕ, p.Prime → ∀ v : Fin 10 → ℤ,
      ((fun j => (v j : ZMod p)) = 0 →
        ‖completeCubicSum F p v‖ ≤ C*(p : ℝ)^((17 : ℝ)/2)) ∧
      ((fun j => (v j : ZMod p)) ≠ 0 →
        ‖completeCubicSum F p v‖ ≤ C*(p : ℝ)^8) := by
    intro p hprime v
    constructor
    · intro hv
      exact ((hp p hprime v).1 hv).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · intro hv
      exact ((hp p hprime v).2 hv).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hs' : ∀ p : ℕ, p.Prime → ∀ v : Fin 10 → ℤ,
      ‖completeCubicSum F (p^2) v‖ ≤ C*(p : ℝ)^17 := by
    intro p hprime v
    letI : Fact p.Prime := ⟨hprime⟩
    exact (hs p v).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  refine ⟨C,hC,?_⟩
  intro v i hi
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hi),?_⟩
  intro a b ha hb hab
  exact complete_sum_bound hF hC hp' hs' v i a b ha hb hab

end CubicTenVariables.ConductorNonzeroCoarseReduced
