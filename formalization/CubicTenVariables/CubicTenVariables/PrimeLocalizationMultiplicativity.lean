import CubicTenVariables.LocalizedRestrictedMultiplicativity

/-! Actual chosen local data instantiate the untwisted complete-sum CRT.
No residue symmetry is assumed by the caller: it is proved on the chosen
unit orbits and their finite product restriction. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace CubicTenVariables.PrimeLocalizationSeries
open MvPolynomial LocalizedRestrictedMultiplicativity
open scoped BigOperators Classical
variable {F : MvPolynomial (Fin 10) ℤ}

theorem complete_sum_mul_outside (hF : F.IsHomogeneous 3)
    (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (D : ∀ (p : ℕ) (hp : p ∈ s), @PrimeLocalizationData p ⟨hprimes p hp⟩ F)
    (q₀ q₁ : ℕ) [NeZero q₀] [NeZero q₁]
    (hc : (q₀*modulus s hprimes D).Coprime q₁) (v : Fin 10 → ℤ) :
    localizedCompleteCubicSum F (q₀*q₁) (modulus s hprimes D) (restriction s hprimes D) v =
      localizedCompleteCubicSum F q₀ (modulus s hprimes D) (restriction s hprimes D) v *
        completeCubicSum F q₁ v := by
  letI : NeZero (modulus s hprimes D) := ⟨(modulus_pos s hprimes D).ne'⟩
  exact localized_mul_outside F hF q₀ q₁ (modulus s hprimes D) hc
    (restriction s hprimes D) (restriction_unitInvariant s hprimes D) v

/-- Product of the literal local factors attached to each supplied D,
including its full restricted factor whenever v_p(q)=0. -/
theorem complete_sum_factorization (hF : F.IsHomogeneous 3)
    (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (D : ∀ (p : ℕ) (hp : p ∈ s), @PrimeLocalizationData p ⟨hprimes p hp⟩ F)
    (q : ℕ) (hq : q ≠ 0) (hs : q.primeFactors ⊆ s) (v : Fin 10 → ℤ) :
    localizedCompleteCubicSum F q (modulus s hprimes D) (restriction s hprimes D) v =
      ∏ p : {p // p ∈ s}, localizedCompleteCubicSum F (p.val^(q.factorization p.val))
        (p.val^(@PrimeLocalizationData.modulusExponent p.val ⟨hprimes p.val p.property⟩ F
          (D p.val p.property)))
        (@PrimeLocalizationData.residueSet p.val ⟨hprimes p.val p.property⟩ F
          (D p.val p.property)) v := by
  have hlocal : ∀ p ∈ s, ResidueUnitInvariant (localResidues s hprimes D p) := by
    intro p hp
    letI : Fact p.Prime := ⟨hprimes p hp⟩
    exact (congrArg (fun spec : Σ M : ℕ, Set (Fin 10 → ZMod (p^M)) =>
      ResidueUnitInvariant spec.2) (localSpecification_of_mem s hprimes D p hp)).mpr
      (D p hp).residueSet_unitInvariant
  have he := localized_factorization F hF q hq s hs (exponent s hprimes D)
    (localResidues s hprimes D) hprimes hlocal v
  change localizedCompleteCubicSum F q (modulus s hprimes D) (restriction s hprimes D) v =
    ∏ p ∈ s, localizedCompleteCubicSum F (p^(q.factorization p))
      (p^(exponent s hprimes D p)) (localResidues s hprimes D p) v at he
  rw [he,←Finset.prod_attach]
  change (∏ p ∈ s.attach, localizedCompleteCubicSum F (p.val^(q.factorization p.val))
      (p.val^(exponent s hprimes D p.val)) (localResidues s hprimes D p.val) v) =
    ∏ p ∈ s.attach, localizedCompleteCubicSum F (p.val^(q.factorization p.val))
      (p.val^(@PrimeLocalizationData.modulusExponent p.val ⟨hprimes p.val p.property⟩ F
        (D p.val p.property)))
      (@PrimeLocalizationData.residueSet p.val ⟨hprimes p.val p.property⟩ F
        (D p.val p.property)) v
  apply Finset.prod_congr rfl
  intro p _
  have hpoint := congrArg (fun spec : Σ M : ℕ, Set (Fin 10 → ZMod (p.val^M)) =>
    localizedCompleteCubicSum F (p.val^(q.factorization p.val)) (p.val^spec.1) spec.2 v)
      (localSpecification_of_mem s hprimes D p.val p.property)
  exact hpoint

end CubicTenVariables.PrimeLocalizationSeries
