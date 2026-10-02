import CubicTenVariables.IntegralGradientPatch
import CubicTenVariables.LocalCongruenceFibers
import CubicTenVariables.PolynomialResidueEvaluation

/-!
# Uniform actual gradient-congruence counts on a p-adic coset

A supplied integral point with a nonzero Hessian minor determines one
prime-power coset and one uniform bound p^(A*r). The count concerns full
residue tuples, with fixed untouched coordinates and selected gradient
values evaluated literally over ZMod(p^s). Membership in the coset is
expressed by an actual integral lift. All constants precede the modulus
and target residues. No literature, local-solubility, or cubic-homogeneity
input is required for this local counting implication.
-/

noncomputable section

namespace CubicTenVariables.IntegralGradientFibers

open MvPolynomial HessianTheorem11 LocalCongruenceFibers IntegralGradientPatch

attribute [local instance] Classical.propDecidable

variable (p : ℕ) [Fact p.Prime] {n r : ℕ}

/-- The selected gradient evaluated over the actual finite residue ring. -/
def modularSelectedGradient (F : MvPolynomial (Fin n) ℤ)
    (rows : Fin r → Fin n) (s : ℕ) (v : Fin n → ZMod (p ^ s)) :
    Fin r → ZMod (p ^ s) :=
  fun a => eval₂ (Int.castRingHom (ZMod (p ^ s))) v (pderiv (rows a) F)

/-- A finite residue tuple with specified actual polynomial gradient values,
fixed untouched coordinates, and a lift in the displayed integral patch. -/
def modularFiber (F : MvPolynomial (Fin n) ℤ) (rows cols : Fin r → Fin n)
    (s : ℕ) (U : Set (Fin n → ℤ_[p]))
    (b : Untouched cols → ZMod (p ^ s)) (c : Fin r → ZMod (p ^ s)) :
    Set (Fin n → ZMod (p ^ s)) :=
  {v | (∀ j : Untouched cols, v j.1 = b j) ∧
    (∀ a, modularSelectedGradient p F rows s v a = c a) ∧
    ∃ z ∈ U, ∀ k, PadicInt.toZModPow s (z k) = v k}

theorem modularFiber_eq_representedFiber (F : MvPolynomial (Fin n) ℤ)
    (rows cols : Fin r → Fin n) (s : ℕ) (U : Set (Fin n → ℤ_[p]))
    (b : Untouched cols → ZMod (p ^ s)) (c : Fin r → ZMod (p ^ s)) :
    modularFiber p F rows cols s U b c =
      representedFiber p s U (integralSelectedGradient p F rows) cols b c := by
  ext v
  constructor
  · rintro ⟨hb, hc, z, hz, hv⟩
    refine ⟨hb, z, hz, hv, ?_⟩
    intro a
    change PadicInt.toZModPow s (eval₂ (Int.castRingHom ℤ_[p]) z
      (pderiv (rows a) F)) = c a
    rw [PolynomialResidueEvaluation.toZModPow_eval₂_int_of_lift _ s z v hv]
    exact hc a
  · rintro ⟨hb, z, hz, hv, hc⟩
    refine ⟨hb, ?_, z, hz, hv⟩
    intro a
    have ha := hc a
    change PadicInt.toZModPow s (eval₂ (Int.castRingHom ℤ_[p]) z
      (pderiv (rows a) F)) = c a at ha
    rw [PolynomialResidueEvaluation.toZModPow_eval₂_int_of_lift _ s z v hv] at ha
    exact ha

/-- A nonzero literal minor supplies a coset with a uniform actual
gradient-congruence fiber bound. The selected rows and columns may differ. -/
theorem exists_coset_uniform_gradient_fiber_bound
    (F : MvPolynomial (Fin n) ℤ) (rows cols : Fin r → Fin n)
    (ξ : Fin n → ℤ_[p])
    (hdet : ((hessian (map (Int.castRingHom ℚ_[p]) F)
      (fun k => (ξ k : ℚ_[p]))).submatrix rows cols).det ≠ 0) :
    ∃ M A : ℕ, 1 ≤ M ∧ ∀ (s : ℕ)
      (b : Untouched cols → ZMod (p ^ s)) (c : Fin r → ZMod (p ^ s)),
      Nat.card (modularFiber p F rows cols s
        (Set.range (fun t : Fin n → ℤ_[p] => ξ + (p : ℤ_[p]) ^ M • t)) b c) ≤
          p ^ (A * r) := by
  obtain ⟨U, C, M, hξ, hU, hM, hcoset, hbound⟩ :=
    exists_integral_gradient_coset_patch p F rows cols ξ hdet
  let B : Set (Fin n → ℤ_[p]) :=
    Set.range (fun t : Fin n → ℤ_[p] => ξ + (p : ℤ_[p]) ^ M • t)
  have hBU : B ⊆ U := by
    rintro z ⟨t, rfl⟩
    exact hcoset t
  obtain ⟨A, hA⟩ := exists_uniform_representedFiber_bound_of_norm_control p B
    (integralSelectedGradient p F rows) cols C
    (fun z hz w hw => hbound z (hBU hz) w (hBU hw))
  refine ⟨M, A, hM, ?_⟩
  intro s b c
  rw [modularFiber_eq_representedFiber]
  exact hA s b c

/-- The actual gradient congruence with an arbitrary invertible multiplier. -/
def unitModularFiber (F : MvPolynomial (Fin n) ℤ) (rows cols : Fin r → Fin n)
    (s : ℕ) (U : Set (Fin n → ℤ_[p])) (u : (ZMod (p ^ s))ˣ)
    (b : Untouched cols → ZMod (p ^ s)) (c : Fin r → ZMod (p ^ s)) :
    Set (Fin n → ZMod (p ^ s)) :=
  {v | (∀ j : Untouched cols, v j.1 = b j) ∧
    (∀ a, (u : ZMod (p ^ s)) * modularSelectedGradient p F rows s v a = c a) ∧
    ∃ z ∈ U, ∀ k, PadicInt.toZModPow s (z k) = v k}

theorem unitModularFiber_eq_modularFiber (F : MvPolynomial (Fin n) ℤ)
    (rows cols : Fin r → Fin n) (s : ℕ) (U : Set (Fin n → ℤ_[p]))
    (u : (ZMod (p ^ s))ˣ) (b : Untouched cols → ZMod (p ^ s))
    (c : Fin r → ZMod (p ^ s)) :
    unitModularFiber p F rows cols s U u b c =
      modularFiber p F rows cols s U b (fun a => (↑u⁻¹ : ZMod (p ^ s)) * c a) := by
  ext v
  simp only [unitModularFiber, modularFiber, Set.mem_setOf_eq,
    Units.eq_inv_mul_iff_mul_eq]

/-- Both constants are independent of the invertible multiplier as well as
the modulus, untouched residues and gradient target. -/
theorem exists_coset_uniform_unit_gradient_fiber_bound
    (F : MvPolynomial (Fin n) ℤ) (rows cols : Fin r → Fin n)
    (ξ : Fin n → ℤ_[p])
    (hdet : ((hessian (map (Int.castRingHom ℚ_[p]) F)
      (fun k => (ξ k : ℚ_[p]))).submatrix rows cols).det ≠ 0) :
    ∃ M A : ℕ, 1 ≤ M ∧ ∀ (s : ℕ) (u : (ZMod (p ^ s))ˣ)
      (b : Untouched cols → ZMod (p ^ s)) (c : Fin r → ZMod (p ^ s)),
      Nat.card (unitModularFiber p F rows cols s
        (Set.range (fun t : Fin n → ℤ_[p] => ξ + (p : ℤ_[p]) ^ M • t)) u b c) ≤
          p ^ (A * r) := by
  obtain ⟨M, A, hM, hcount⟩ := exists_coset_uniform_gradient_fiber_bound p F rows cols ξ hdet
  refine ⟨M, A, hM, ?_⟩
  intro s u b c
  rw [unitModularFiber_eq_modularFiber]
  exact hcount s b (fun a => (↑u⁻¹ : ZMod (p ^ s)) * c a)

end CubicTenVariables.IntegralGradientFibers
