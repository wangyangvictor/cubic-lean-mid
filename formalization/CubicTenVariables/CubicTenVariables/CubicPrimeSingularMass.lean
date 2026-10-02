import CubicTenVariables.FiniteRankMass
import CubicTenVariables.PrimeFrogTwoMass
import CubicTenVariables.OnCubicLowRankEquations
import CubicTenVariables.HessianRankOneReduction
import CubicTenVariables.CubicFiniteFieldMass

/-! The actual nonzero singular-root Hessian mass in ten variables.
Only closed low-rank counts and the full gradient-zero count are used.
The existing all-prime rank-one count absorbs exceptional primes already. -/

noncomputable section
namespace CubicTenVariables.CubicPrimeSingularMass
open MvPolynomial HessianTheorem11 HessianKernelCRT PrimeFrogTwoMass
open scoped BigOperators

/-- Finite assembly from the displayed literal count bounds. These are
helper hypotheses, supplied by proved theorems at the final endpoint. -/
theorem mass_le_of_counts (F : MvPolynomial (Fin 10) ℤ)
    (p : ℕ) [Fact p.Prime] (C₁ C₂ C₃ G : ℕ)
    (h₁ : (HessianRankOneReduction.onCubicRankOnePoints F p).card ≤ C₁)
    (h₂ : Nat.card {x : Fin 10 → ZMod p //
      eval₂ (Int.castRingHom (ZMod p)) x F = 0 ∧
        (hessian (map (Int.castRingHom (ZMod p)) F) x).rank ≤ 2} ≤ C₂*p^2)
    (h₃ : Nat.card {x : Fin 10 → ZMod p //
      eval₂ (Int.castRingHom (ZMod p)) x F = 0 ∧
        (hessian (map (Int.castRingHom (ZMod p)) F) x).rank ≤ 3} ≤ C₃*p^4)
    (hG : Nat.card {x : Fin 10 → ZMod p //
      gradient (map (Int.castRingHom (ZMod p)) F) x = 0} ≤ G*p^5) :
    (∑ x ∈ singularRootPoints F p, hessianKernelCard F p x) ≤
      (C₁+C₂+C₃+G)*p^11 := by
  classical
  let S := singularRootPoints F p
  let rk := fun x : Fin 10 → ZMod p =>
    (hessian (map (Int.castRingHom (ZMod p)) F) x).rank
  have hmem (x) (hx : x ∈ S) :
      eval₂ (Int.castRingHom (ZMod p)) x F = 0 ∧ x ≠ 0 ∧
        ∀ i, eval₂ (Int.castRingHom (ZMod p)) x (pderiv i F) = 0 :=
    (Finset.mem_filter.mp hx).2
  have hcard₁ : (S.filter (fun x => rk x ≤ 1)).card ≤ C₁ := by
    apply le_trans (Finset.card_le_card ?_) h₁
    intro x hx
    obtain ⟨hxS, hr⟩ := Finset.mem_filter.mp hx
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by simpa only [eval_map] using (hmem x hxS).1, hr⟩
  have hcard₂ : (S.filter (fun x => rk x = 2)).card ≤ C₂*p^2 := by
    have hc : (Finset.univ.filter (fun x : Fin 10 → ZMod p =>
        eval₂ (Int.castRingHom (ZMod p)) x F = 0 ∧ rk x ≤ 2)).card ≤ C₂*p^2 := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using h₂
    apply le_trans (Finset.card_le_card ?_) hc
    intro x hx
    obtain ⟨hxS, hr⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hmem x hxS).1, hr.le⟩
  have hcard₃ : (S.filter (fun x => rk x = 3)).card ≤ C₃*p^4 := by
    have hc : (Finset.univ.filter (fun x : Fin 10 → ZMod p =>
        eval₂ (Int.castRingHom (ZMod p)) x F = 0 ∧ rk x ≤ 3)).card ≤ C₃*p^4 := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using h₃
    apply le_trans (Finset.card_le_card ?_) hc
    intro x hx
    obtain ⟨hxS, hr⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hmem x hxS).1, hr.le⟩
  have hcardG : S.card ≤ G*p^5 := by
    have hc : (Finset.univ.filter (fun x : Fin 10 → ZMod p =>
        ∀ i, eval₂ (Int.castRingHom (ZMod p)) x (pderiv i F) = 0)).card ≤ G*p^5 := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype,
        HessianTheorem11.gradient, _root_.funext_iff, Pi.zero_apply,
        pderiv_map, eval_map] using hG
    apply le_trans (Finset.card_le_card ?_) hc
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hmem x hx).2.2⟩
  have hbound := FiniteRankMass.sum_le_four_rank_classes S rk
    (hessianKernelCard F p) (p^10) (p^8) (p^7) (p^6)
    (fun x _ _ => by simpa using
      PrimeFieldKernelRank.hessianKernelCard_le_pow_of_rank_le F p x (Nat.zero_le _))
    (fun x _ hx => by simpa using
      PrimeFieldKernelRank.hessianKernelCard_le_pow_of_rank_le F p x hx.ge)
    (fun x _ hx => by simpa using
      PrimeFieldKernelRank.hessianKernelCard_le_pow_of_rank_le F p x hx.ge)
    (fun x _ hx => by simpa using
      PrimeFieldKernelRank.hessianKernelCard_le_pow_of_rank_le F p x hx)
  have h1011 : p^10 ≤ p^11 := Nat.pow_le_pow_right (Nat.Prime.one_le Fact.out) (by decide)
  calc
    _ ≤ (S.filter (fun x => rk x ≤ 1)).card*p^10 +
        (S.filter (fun x => rk x = 2)).card*p^8 +
        (S.filter (fun x => rk x = 3)).card*p^7 + S.card*p^6 := hbound
    _ ≤ C₁*p^10 + (C₂*p^2)*p^8 + (C₃*p^4)*p^7 + (G*p^5)*p^6 :=
      Nat.add_le_add (Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_right _ hcard₁) (Nat.mul_le_mul_right _ hcard₂))
        (Nat.mul_le_mul_right _ hcard₃)) (Nat.mul_le_mul_right _ hcardG)
    _ = C₁*p^10 + C₂*p^10 + C₃*p^11 + G*p^11 := by ring
    _ ≤ C₁*p^11 + C₂*p^11 + C₃*p^11 + G*p^11 := by
      exact Nat.add_le_add_right (Nat.add_le_add_right
        (Nat.add_le_add (Nat.mul_le_mul_left _ h1011) (Nat.mul_le_mul_left _ h1011)) _) _
    _ = _ := by ring

/-- One constant before every prime controls the literal nonzero
singular-root kernel mass. No dimension, point-count, rank exclusion,
good-prime or literature premise is left in this endpoint. -/
theorem exists_uniform_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) [Fact p.Prime],
      (∑ x ∈ singularRootPoints F p, hessianKernelCard F p x) ≤ C*p^11 := by
  obtain ⟨C₁, hC₁, hc₁⟩ := HessianRankOneReduction.exists_uniform_onCubic_rankOne_bound F hF hA
  obtain ⟨C₂, _hC₂, hc₂⟩ := OnCubicLowRankEquations.exists_uniform_rank_two_count_bound F hF hA
  obtain ⟨C₃, _hC₃, hc₃⟩ := OnCubicLowRankEquations.exists_uniform_rank_three_count_bound F hF hA
  obtain ⟨G, _hG, hg⟩ := CubicFiniteFieldMass.exists_uniform_gradient_zero_bound F hF hA
  refine ⟨C₁+C₂+C₃+G, by omega, ?_⟩
  intro p hp
  exact mass_le_of_counts F p C₁ C₂ C₃ G (hc₁ p hp.out) (hc₂ p) (hc₃ p) (hg p hp.out)

end CubicTenVariables.CubicPrimeSingularMass
