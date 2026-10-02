import CubicTenVariables.LocalizedFourierUnit
import CubicTenVariables.PrimeLocalizationUnitInvariance

/-! Untwisted CRT for the actual localized complete sums. Homogeneity and
the proved scalar symmetry remove the frequency twists before any shifted
box is considered. Modulus-one factors retain the actual restrictions. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.LocalizedRestrictedMultiplicativity
open MvPolynomial LocalizedZeroCRT LocalizedFourierCRT LocalizedFourierUnit
open LocalizedFinitePrimeAssembly
open scoped BigOperators Classical

local instance lcmNeZero (a b : ℕ) [NeZero a] [NeZero b] : NeZero (Nat.lcm a b) :=
  ⟨Nat.lcm_ne_zero (NeZero.ne a) (NeZero.ne b)⟩

/-- No frequency change remains in this actual-sum CRT identity. -/
theorem localized_mul {n d : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous d) (q₀ q₁ W₀ W₁ : ℕ)
    [NeZero q₀] [NeZero q₁] [NeZero W₀] [NeZero W₁]
    (h : (q₀*W₀).Coprime (q₁*W₁))
    (Ω₀ : Set (Fin n → ZMod W₀)) (Ω₁ : Set (Fin n → ZMod W₁))
    (hΩ₀ : ResidueUnitInvariant Ω₀) (hΩ₁ : ResidueUnitInvariant Ω₁)
    (v : Fin n → ℤ) :
    localizedCompleteCubicSum F (q₀*q₁) (W₀*W₁)
      (productRestriction
        ((h.of_dvd_left (dvd_mul_left W₀ q₀)).of_dvd_right (dvd_mul_left W₁ q₁)) Ω₀ Ω₁) v =
      localizedCompleteCubicSum F q₀ W₀ Ω₀ v *
        localizedCompleteCubicSum F q₁ W₁ Ω₁ v := by
  rw [localized_mul_twisted F q₀ q₁ W₀ W₁ h Ω₀ Ω₁ v]
  rw [residueFourierSum_unit_frequency F hF _ _ Ω₀ hΩ₀,
    residueFourierSum_unit_frequency F hF _ _ Ω₁ hΩ₁,
    ← localized_eq_residueFourierSum,← localized_eq_residueFourierSum]

theorem localized_cast_restriction {n W V : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (q : ℕ) (hWV : W = V) (hVW : V ∣ W)
    (Ω : Set (Fin n → ZMod V)) (v : Fin n → ℤ) :
    localizedCompleteCubicSum F q W
      {x | (fun i => ZMod.castHom hVW (ZMod V) (x i)) ∈ Ω} v =
      localizedCompleteCubicSum F q V Ω v := by
  subst W
  simp only [ZMod.castHom_self,RingHom.id_apply]
  rfl

/-- The source's decomposition into a localization block and a coprime
unrestricted block at exactly the same integer frequency. -/
theorem localized_mul_outside {n d : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous d) (q₀ q₁ W : ℕ)
    [NeZero q₀] [NeZero q₁] [NeZero W] (h : (q₀*W).Coprime q₁)
    (Ω : Set (Fin n → ZMod W)) (hΩ : ResidueUnitInvariant Ω) (v : Fin n → ℤ) :
    localizedCompleteCubicSum F (q₀*q₁) W Ω v =
      localizedCompleteCubicSum F q₀ W Ω v * completeCubicSum F q₁ v := by
  have hh := localized_mul F hF q₀ q₁ W 1 (by simpa using h) Ω Set.univ
    hΩ (ResidueUnitInvariant.univ n 1) v
  simp only [productRestriction_eq_cast,Set.mem_univ,and_true,
    localizedCompleteCubicSum_univ_one] at hh
  rw [localized_cast_restriction F (q₀*q₁) (Nat.mul_one W)] at hh
  exact hh

/-- Iterated CRT for every finite collection of distinct primes, retaining
the actual local factor even where k(p)=0. -/
theorem localized_product {n d : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous d) (s : Finset ℕ) (k M : ℕ → ℕ)
    (Ω : ∀ p, Set (Fin n → ZMod (p^(M p))))
    (hprimes : ∀ p ∈ s, p.Prime) (hΩ : ∀ p ∈ s, ResidueUnitInvariant (Ω p))
    (v : Fin n → ℤ) :
    localizedCompleteCubicSum F (modulus s k) (modulus s M) (restriction s M Ω) v =
      ∏ p ∈ s, localizedCompleteCubicSum F (p^(k p)) (p^(M p)) (Ω p) v := by
  revert hprimes hΩ
  induction s using Finset.induction_on with
  | empty =>
      intro _ _
      have he : restriction (∅ : Finset ℕ) M Ω = Set.univ := by
        ext x
        simp [restriction,restrictionAt]
      simp only [he,modulus,Finset.prod_empty,localizedCompleteCubicSum_univ_one,
        completeCubicSum_one]
  | @insert p s hps ih =>
      intro hprimes hΩ
      have hp : p.Prime := hprimes p (Finset.mem_insert_self _ _)
      have hps' : ∀ r ∈ s, r.Prime := fun r hr => hprimes r (Finset.mem_insert_of_mem hr)
      have hΩs : ∀ r ∈ s, ResidueUnitInvariant (Ω r) :=
        fun r hr => hΩ r (Finset.mem_insert_of_mem hr)
      letI : NeZero (modulus s k) := ⟨(modulus_pos s k hps').ne'⟩
      letI : NeZero (modulus s M) := ⟨(modulus_pos s M hps').ne'⟩
      letI : NeZero p := ⟨hp.ne_zero⟩
      have hc (f : ℕ → ℕ) : (modulus s f).Coprime p := by
        apply Nat.coprime_prod_left_iff.mpr
        intro r hr
        exact ((Nat.coprime_primes (hps' r hr) hp).mpr
          (by intro he; subst r; exact hps hr)).pow_left (f r)
      have hblock : ((modulus s k)*(modulus s M)).Coprime (p^(k p)*p^(M p)) :=
        ((hc k).mul_left (hc M)).pow_right (k p + M p) |>.of_dvd_right
          (by rw [pow_add])
      have hs := localized_mul F hF (modulus s k) (p^(k p)) (modulus s M) (p^(M p))
        hblock (restriction s M Ω) (Ω p) (restriction_unitInvariant s M Ω hΩs)
        (hΩ p (Finset.mem_insert_self _ _)) v
      have hnew : localizedCompleteCubicSum F ((modulus s k)*p^(k p))
          ((modulus s M)*p^(M p)) (restrictionAt (insert p s) M Ω ((modulus s M)*p^(M p))) v =
          localizedCompleteCubicSum F (modulus s k) (modulus s M) (restriction s M Ω) v *
            localizedCompleteCubicSum F (p^(k p)) (p^(M p)) (Ω p) v := by
        rw [restrictionAt_insert s M Ω p (modulus s M)
          (primePower_dvd_modulus s M) ((hc M).pow_right (M p))]
        exact hs
      rw [ih hps' hΩs] at hnew
      unfold restriction
      rw [modulus_insert s k p hps,modulus_insert s M p hps,Finset.prod_insert hps]
      exact hnew.trans (mul_comm _ _)

/-- Prime factorization over any finite superset of the actual prime
support; exponents zero contribute one to the modulus, not to a sum. -/
theorem modulus_factorization_eq (q : ℕ) (hq : q ≠ 0) (s : Finset ℕ)
    (hs : q.primeFactors ⊆ s) : modulus s q.factorization = q := by
  have he := q.factorization.prod_of_support_subset hs (fun p k => p^k)
    (fun _ _ => pow_zero _)
  exact he.symm.trans (Nat.factorization_prod_pow_eq_self hq)

/-- The finite localized prime factorization of an arbitrary positive q
supported on the selected primes, at the unchanged integer frequency. -/
theorem localized_factorization {n d : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous d) (q : ℕ) (hq : q ≠ 0) (s : Finset ℕ)
    (hs : q.primeFactors ⊆ s) (M : ℕ → ℕ)
    (Ω : ∀ p, Set (Fin n → ZMod (p^(M p))))
    (hprimes : ∀ p ∈ s, p.Prime) (hΩ : ∀ p ∈ s, ResidueUnitInvariant (Ω p))
    (v : Fin n → ℤ) :
    localizedCompleteCubicSum F q (modulus s M) (restriction s M Ω) v =
      ∏ p ∈ s, localizedCompleteCubicSum F (p^(q.factorization p)) (p^(M p)) (Ω p) v := by
  simpa only [modulus_factorization_eq q hq s hs] using
    localized_product F hF s q.factorization M Ω hprimes hΩ v

end CubicTenVariables.LocalizedRestrictedMultiplicativity
