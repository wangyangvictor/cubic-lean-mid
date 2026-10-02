import CubicTenVariables.LocalizedPrimeInsertion
import Mathlib.Data.Nat.GCD.BigOperators

/-! Finite insertion of the actual restricted local prime factors. The final
modulus is the literal product of the prime powers, and membership in the
final residue restriction is exactly membership in every local restriction
after canonical reduction. No replacement coefficient system is assumed. -/

noncomputable section
namespace CubicTenVariables.LocalizedFinitePrimeAssembly
open MvPolynomial LocalizedZeroCRT CRTCharacters
open scoped BigOperators Classical

def modulus (s : Finset ℕ) (M : ℕ → ℕ) : ℕ := ∏ p ∈ s, p^(M p)

/-- Canonical reductions from a specified ambient modulus. The required
divisibilities are proved when this is used at the product modulus. -/
def restrictionAt {n : ℕ} (s : Finset ℕ) (M : ℕ → ℕ)
    (Ω : ∀ p, Set (Fin n → ZMod (p^(M p)))) (A : ℕ) : Set (Fin n → ZMod A) :=
  {x | ∀ p ∈ s, (fun i => (ZMod.cast (x i) : ZMod (p^(M p)))) ∈ Ω p}

def restriction {n : ℕ} (s : Finset ℕ) (M : ℕ → ℕ)
    (Ω : ∀ p, Set (Fin n → ZMod (p^(M p)))) : Set (Fin n → ZMod (modulus s M)) :=
  restrictionAt s M Ω (modulus s M)

theorem modulus_insert (s : Finset ℕ) (M : ℕ → ℕ) (p : ℕ) (hp : p ∉ s) :
    modulus (insert p s) M = modulus s M * p^(M p) := by
  simp only [modulus, Finset.prod_insert hp, mul_comm]

theorem primePower_dvd_modulus (s : Finset ℕ) (M : ℕ → ℕ) (p : ℕ) (hp : p ∈ s) :
    p^(M p) ∣ modulus s M := Finset.dvd_prod_of_mem _ hp

theorem modulus_pos (s : Finset ℕ) (M : ℕ → ℕ) (hp : ∀ p ∈ s, p.Prime) :
    0 < modulus s M :=
  Finset.prod_pos fun p hp' => pow_pos (hp p hp').pos _

/-- Membership uses the canonical ring homomorphism to each local factor. -/
theorem mem_restriction_iff {n : ℕ} (s : Finset ℕ) (M : ℕ → ℕ)
    (Ω : ∀ p, Set (Fin n → ZMod (p^(M p)))) (x : Fin n → ZMod (modulus s M)) :
    x ∈ restriction s M Ω ↔
      ∀ (p : ℕ) (hp : p ∈ s),
        (fun i => ZMod.castHom (primePower_dvd_modulus s M p hp) (ZMod (p^(M p))) (x i)) ∈ Ω p :=
  Iff.rfl

/-- For actual integer vectors this is exactly the simultaneous collection
of local congruence restrictions from the counting problem. -/
theorem integerResidue_mem_iff {n : ℕ} (s : Finset ℕ) (M : ℕ → ℕ)
    (Ω : ∀ p, Set (Fin n → ZMod (p^(M p)))) (x : Fin n → ℤ) :
    integerResidue (modulus s M) x ∈ restriction s M Ω ↔
      ∀ p ∈ s, integerResidue (p^(M p)) x ∈ Ω p := by
  rw [mem_restriction_iff]
  simp only [integerResidue, map_intCast]
  rfl

theorem restrictionAt_insert {n : ℕ} (s : Finset ℕ) (M : ℕ → ℕ)
    (Ω : ∀ p, Set (Fin n → ZMod (p^(M p)))) (p W : ℕ)
    (hdiv : ∀ r ∈ s, r^(M r) ∣ W) (hc : W.Coprime (p^(M p))) :
    restrictionAt (insert p s) M Ω (W*p^(M p)) =
      productRestriction hc (restrictionAt s M Ω W) (Ω p) := by
  ext x
  have hleft (r : ℕ) (hr : r ∈ s) :
      (fun i => (ZMod.cast (leftProjection hc (x i)) : ZMod (r^(M r)))) =
        fun i => (ZMod.cast (x i) : ZMod (r^(M r))) := by
    funext i
    exact congrArg (fun f : ZMod (W*p^(M p)) →+* ZMod (r^(M r)) => f (x i))
      (Subsingleton.elim
        ((ZMod.castHom (hdiv r hr) (ZMod (r^(M r)))).comp (leftProjection hc))
        (ZMod.castHom ((hdiv r hr).trans (dvd_mul_right W (p^(M p)))) (ZMod (r^(M r)))))
  have hright : (fun i => rightProjection hc (x i)) =
      fun i => (ZMod.cast (x i) : ZMod (p^(M p))) := by
    funext i
    exact congrArg (fun f : ZMod (W*p^(M p)) →+* ZMod (p^(M p)) => f (x i))
      (Subsingleton.elim (rightProjection hc)
        (ZMod.castHom (dvd_mul_left (p^(M p)) W) (ZMod (p^(M p)))))
  simp only [restrictionAt, productRestriction, Set.mem_setOf_eq, Finset.forall_mem_insert,
    hright]
  constructor
  · rintro ⟨hp, hs⟩
    exact ⟨fun r hr => by simpa only [hleft r hr] using hs r hr, hp⟩
  · rintro ⟨hs, hp⟩
    exact ⟨hp, fun r hr => by simpa only [hleft r hr] using hs r hr⟩

/-- Actual localized convergence and positivity after finitely many distinct
prime restrictions. Ordinary global convergence/positivity and each actual
restricted local factor remain explicit hypotheses of this assembly. -/
theorem assemble {n : ℕ} (F : MvPolynomial (Fin n) ℤ) (hn : 1 ≤ n)
    (s : Finset ℕ) (M : ℕ → ℕ) (Ω : ∀ p, Set (Fin n → ZMod (p^(M p))))
    (hprimes : ∀ p ∈ s, p.Prime) (hordinary : SingularSeriesAbsolutelyConvergent F)
    (S : ℝ) (hS : 0 < S) (hordinaryValue : singularSeries F = (S:ℂ))
    (hlocal : ∀ p ∈ s, ∃ L : ℝ, 0 < L ∧
      Summable (fun k => ‖localizedSingularSeriesTerm F (p^(M p)) (Ω p) (p^k)‖) ∧
      HasSum (fun k => localizedSingularSeriesTerm F (p^(M p)) (Ω p) (p^k)) (L:ℂ)) :
    Summable (fun q => ‖localizedSingularSeriesTerm F (modulus s M) (restriction s M Ω) q‖) ∧
      ∃ T : ℝ, 0 < T ∧ localizedSingularSeries F (modulus s M) (restriction s M Ω) = (T:ℂ) := by
  revert hprimes hlocal
  induction s using Finset.induction_on with
  | empty =>
      intro _ _
      have he : restriction (∅ : Finset ℕ) M Ω = Set.univ := by
        ext x
        simp [restriction, restrictionAt]
      simpa only [he, modulus, Finset.prod_empty, localizedSingularSeriesTerm_univ_one,
        localizedSingularSeries_univ_one] using And.intro hordinary ⟨S,hS,hordinaryValue⟩
  | @insert p s hp ih =>
      intro hprimes hlocal
      have hpp : p.Prime := hprimes p (Finset.mem_insert_self _ _)
      have hps : ∀ r ∈ s, r.Prime := fun r hr => hprimes r (Finset.mem_insert_of_mem hr)
      obtain ⟨hold, T, hT, hTvalue⟩ := ih hps
        (fun r hr => hlocal r (Finset.mem_insert_of_mem hr))
      obtain ⟨L,hL,habsL,hLvalue⟩ := hlocal p (Finset.mem_insert_self _ _)
      have hc : (modulus s M).Coprime p := by
        apply Nat.coprime_prod_left_iff.mpr
        intro r hr
        exact ((Nat.coprime_primes (hps r hr) hpp).mpr
          (by intro he; subst r; exact hp hr)).pow_left (M r)
      have hnew := LocalizedPrimeInsertion.insert_prime F hn p (M p) (modulus s M) hpp
        (modulus_pos s M hps) hc (restriction s M Ω) (Ω p)
        hordinary hold T hT hTvalue habsL L hL hLvalue.tsum_eq
      change Summable (fun q => ‖localizedSingularSeriesTerm F _
        (productRestriction (hc.pow_right (M p)) (restrictionAt s M Ω (modulus s M)) (Ω p)) q‖) ∧
        ∃ T : ℝ, 0 < T ∧ localizedSingularSeries F _
          (productRestriction (hc.pow_right (M p)) (restrictionAt s M Ω (modulus s M)) (Ω p)) = (T:ℂ) at hnew
      rw [← restrictionAt_insert s M Ω p (modulus s M)
        (primePower_dvd_modulus s M) (hc.pow_right (M p))] at hnew
      let E (A : ℕ) : Prop :=
        Summable (fun q => ‖localizedSingularSeriesTerm F A (restrictionAt (insert p s) M Ω A) q‖) ∧
          ∃ T : ℝ, 0 < T ∧ localizedSingularSeries F A (restrictionAt (insert p s) M Ω A) = (T:ℂ)
      exact (congrArg E (modulus_insert s M p hp)).mpr hnew

end CubicTenVariables.LocalizedFinitePrimeAssembly
