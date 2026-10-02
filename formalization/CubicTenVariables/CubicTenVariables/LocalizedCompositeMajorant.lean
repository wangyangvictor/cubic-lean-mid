import CubicTenVariables.LocalizedResidueMajorant
import CubicTenVariables.ResidueMajorantCRT
import CubicTenVariables.PrimeLocalizationMultiplicativity

/-! Finite-prime assembly of literal localized complete-sum bounds.
All constants are chosen from the fixed local data before the supported
modulus or frequency set. Zero prime exponents retain their local factors. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CubicTenVariables.LocalizedCompositeMajorant
open MvPolynomial
open IntegerResidueClasses (residue)
open scoped BigOperators Classical
variable {F : MvPolynomial (Fin 10) ℤ}

/-- The product of the ceiling-third prime-power residue moduli. -/
def modulus (s : Finset ℕ) (g : ℕ) : ℕ :=
  ∏ p : {p // p ∈ s}, p.val^((g.factorization p.val+2)/3)

theorem modulus_eq_prod (s : Finset ℕ) (g : ℕ) :
    modulus s g = ∏ p ∈ s, p^((g.factorization p+2)/3) := by
  exact Finset.prod_coe_sort s (fun p => p^((g.factorization p+2)/3))

theorem modulus_pos (s : Finset ℕ) (g : ℕ) :
    0 < modulus s g := by
  apply Finset.prod_pos
  intro p _
  by_cases hp : p.val = 0
  · simp [hp,Nat.factorization_eq_zero_of_not_prime g Nat.not_prime_zero]
  · exact pow_pos (Nat.pos_of_ne_zero hp) _

instance modulus_neZero (s : Finset ℕ) (g : ℕ) : NeZero (modulus s g) :=
  ⟨(modulus_pos s g).ne'⟩

@[simp] theorem modulus_one (s : Finset ℕ) : modulus s 1 = 1 := by
  simp [modulus_eq_prod]

@[simp] theorem modulus_empty (g : ℕ) : modulus ∅ g = 1 := by
  simp [modulus_eq_prod]

/-- Factorization remains exact over a finite superset of the support. -/
theorem factorization_product (s : Finset ℕ) (g : ℕ) (hg : 0 < g)
    (hs : g.primeFactors ⊆ s) :
    (∏ p : {p // p ∈ s}, p.val^(g.factorization p.val)) = g := by
  rw [Finset.prod_coe_sort s (fun p => p^(g.factorization p))]
  have he := g.factorization.prod_of_support_subset hs (fun p k => p^k)
    (fun _ _ => pow_zero _)
  exact he.symm.trans (Nat.factorization_prod_pow_eq_self hg.ne')

/-- The selected residue modulus divides the original supported modulus. -/
theorem modulus_dvd (s : Finset ℕ) (g : ℕ) (hg : 0 < g)
    (hs : g.primeFactors ⊆ s) : modulus s g ∣ g := by
  calc
    modulus s g ∣ ∏ p : {p // p ∈ s}, p.val^(g.factorization p.val) := by
      apply Finset.prod_dvd_prod_of_dvd
      intro p _
      exact pow_dvd_pow p.val (by omega)
    _ = g := factorization_product s g hg hs

/-- Cubing the selected residue modulus recovers at least the original
modulus, including all exponent-zero factors and the unit modulus. -/
theorem le_modulus_cube (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (g : ℕ) (hg : 0 < g) (hs : g.primeFactors ⊆ s) : g ≤ (modulus s g)^3 := by
  calc
    g = ∏ p : {p // p ∈ s}, p.val^(g.factorization p.val) :=
      (factorization_product s g hg hs).symm
    _ ≤ ∏ p : {p // p ∈ s}, (p.val^((g.factorization p.val+2)/3))^3 := by
      apply Finset.prod_le_prod'
      intro p _
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (hprimes p.val p.property).one_le (by omega)
    _ = (modulus s g)^3 := Finset.prod_pow _ _ _

/-- No epsilon or support-cardinality loss occurs in the real powers. -/
theorem prod_factorization_rpow (s : Finset ℕ) (g : ℕ) (hg : 0 < g)
    (hs : g.primeFactors ⊆ s) (u : ℝ) :
    (∏ p : {p // p ∈ s}, (p.val : ℝ)^(u*(g.factorization p.val : ℝ))) =
      (g : ℝ)^u := by
  calc
    _ = ∏ p : {p // p ∈ s}, ((p.val : ℝ)^(g.factorization p.val))^u := by
      apply Finset.prod_congr rfl
      intro p _
      rw [mul_comm u,Real.rpow_natCast_mul (Nat.cast_nonneg p.val)]
    _ = (∏ p : {p // p ∈ s}, (p.val : ℝ)^(g.factorization p.val))^u :=
      Real.finset_prod_rpow _ _ (fun p _ => pow_nonneg (Nat.cast_nonneg p.val) _) u
    _ = _ := by
      simp only [← Nat.cast_pow,← Nat.cast_prod,factorization_product s g hg hs]

/-- The literal localized `g` sum has a residue majorant of mass
`O(g^(28/3))`. The implicit constant depends only on the fixed local data. -/
theorem exists_majorant (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (D : ∀ (p : ℕ) (hp : p ∈ s), @PrimeLocalizationData p ⟨hprimes p hp⟩ F)
    (hF : F.IsHomogeneous 3) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (g : ℕ), 0 < g → g.primeFactors ⊆ s →
      ∀ V : Finset (Fin 10 → ℤ),
      ∃ P : (Fin 10 → ZMod (modulus s g)) → ℝ,
        (∀ b, 0 ≤ P b) ∧
        (∀ v ∈ V, ‖localizedCompleteCubicSum F g
          (PrimeLocalizationSeries.modulus s hprimes D)
          (PrimeLocalizationSeries.restriction s hprimes D) v‖ ≤ P (residue (modulus s g) v)) ∧
        (∑ b, P b) ≤ C*(g : ℝ)^((28 : ℝ)/3) := by
  choose C hC hlocal using fun p : {p // p ∈ s} =>
    @LocalizedResidueMajorant.exists_majorant p.val ⟨hprimes p.val p.property⟩ F
      (D p.val p.property) hF
  have hprod : (1 : ℝ) ≤ ∏ p, C p := by
    simpa only [Finset.prod_const_one] using
      (Finset.prod_le_prod (fun _ _ => (zero_le_one : (0 : ℝ) ≤ 1)) (fun p _ => hC p))
  refine ⟨∏ p, C p,hprod,?_⟩
  intro g hg hs V
  let q (p : {p // p ∈ s}) : ℕ := p.val^((g.factorization p.val+2)/3)
  letI : ∀ p : {p // p ∈ s}, NeZero (q p) :=
    fun p => ⟨pow_ne_zero _ (hprimes p.val p.property).ne_zero⟩
  choose P hP hmajor hmass using fun p : {p // p ∈ s} =>
    hlocal p (g.factorization p.val) V
  have hcop : Pairwise fun p r : {p // p ∈ s} => (q p).Coprime (q r) := by
    intro p r hne
    exact Nat.coprime_pow_primes _ _ (hprimes p.val p.property) (hprimes r.val r.property)
      (fun he => hne (Subtype.ext he))
  refine ⟨ResidueMajorantCRT.piProduct q P,
    ResidueMajorantCRT.piProduct_nonneg q P hP,?_,?_⟩
  · intro v hv
    rw [PrimeLocalizationSeries.complete_sum_factorization hF s hprimes D g hg.ne' hs v,norm_prod]
    change _ ≤ ResidueMajorantCRT.piProduct q P (residue (∏ p, q p) v)
    rw [ResidueMajorantCRT.piProduct_at_residue q P v]
    exact Finset.prod_le_prod (fun p _ => norm_nonneg _) (fun p _ => hmajor p v hv)
  · calc
      _ ≤ ∏ p : {p // p ∈ s}, C p*(p.val : ℝ)^((28 : ℝ)/3*(g.factorization p.val : ℝ)) :=
        ResidueMajorantCRT.piProduct_mass_le q hcop P hP _ hmass
      _ = _ := by rw [Finset.prod_mul_distrib,prod_factorization_rpow s g hg hs]

/-- The pointwise seventh-power estimate for the same literal localized
sum, uniformly over all supported positive moduli and integer frequencies. -/
theorem exists_pointwise_bound (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (D : ∀ (p : ℕ) (hp : p ∈ s), @PrimeLocalizationData p ⟨hprimes p hp⟩ F)
    (hF : F.IsHomogeneous 3) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (g : ℕ), 0 < g → g.primeFactors ⊆ s →
      ∀ v : Fin 10 → ℤ,
      ‖localizedCompleteCubicSum F g (PrimeLocalizationSeries.modulus s hprimes D)
        (PrimeLocalizationSeries.restriction s hprimes D) v‖ ≤ C*(g : ℝ)^7 := by
  choose C hC hlocal using fun p : {p // p ∈ s} =>
    @LocalizedResidueMajorant.exists_pointwise_bound p.val ⟨hprimes p.val p.property⟩ F
      (D p.val p.property) hF
  have hprod : (1 : ℝ) ≤ ∏ p, C p := by
    simpa only [Finset.prod_const_one] using
      (Finset.prod_le_prod (fun _ _ => (zero_le_one : (0 : ℝ) ≤ 1)) (fun p _ => hC p))
  refine ⟨∏ p, C p,hprod,?_⟩
  intro g hg hs v
  rw [PrimeLocalizationSeries.complete_sum_factorization hF s hprimes D g hg.ne' hs v,norm_prod]
  calc
    _ ≤ ∏ p : {p // p ∈ s}, C p*(p.val : ℝ)^(7*g.factorization p.val) :=
      Finset.prod_le_prod (fun p _ => norm_nonneg _) (fun p _ => hlocal p (g.factorization p.val) v)
    _ = (∏ p, C p)*(∏ p : {p // p ∈ s}, ((p.val : ℝ)^(g.factorization p.val))^7) := by
      rw [Finset.prod_mul_distrib]
      congr 1
      apply Finset.prod_congr rfl
      intro p _
      rw [Nat.mul_comm 7,pow_mul]
    _ = (∏ p, C p)*(∏ p : {p // p ∈ s}, (p.val : ℝ)^(g.factorization p.val))^7 := by
      rw [Finset.prod_pow]
    _ = _ := by
      simp only [← Nat.cast_pow,← Nat.cast_prod,factorization_product s g hg hs]

end CubicTenVariables.LocalizedCompositeMajorant
