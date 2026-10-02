import CubicTenVariables.PadicUnitOrbit
import CubicTenVariables.GradientTotalCount
import CubicTenVariables.CubicGradientScaling

/-! Uniform actual gradient-congruence counts on the full unit orbit of a
literal integral coset. The finite cover is constructed before all residue
targets; overlap between its members does not require disjointness. -/

noncomputable section
namespace CubicTenVariables.UnitGradientFibers

open MvPolynomial HessianTheorem11 IntegralGradientFibers LocalCongruenceFibers
open PadicUnitOrbit GradientFiberUnions GradientTotalCount

attribute [local instance] Classical.propDecidable

variable (p : ℕ) [Fact p.Prime] {n r : ℕ}

theorem card_unitOrbit_fiber_le_of_scaled_bounds
    (F : MvPolynomial (Fin n) ℤ) (rows cols : Fin r → Fin n)
    (ξ : Fin n → ℤ_[p]) (M s : ℕ) (u : (ZMod (p ^ s))ˣ)
    (b : Untouched cols → ZMod (p ^ s)) (c : Fin r → ZMod (p ^ s))
    (K : ℕ)
    (hK : ∀ a : ℤ_[p]ˣ,
      Nat.card (unitModularFiber p F rows cols s
        ((fun z => (a : ℤ_[p]) • z) '' coset p ξ M) u b c) ≤ K) :
    Nat.card (unitModularFiber p F rows cols s (unitOrbit p ξ M) u b c) ≤ p ^ M * K := by
  obtain ⟨T, hT, hcover⟩ := exists_finite_unit_orbit_cover p ξ M
  rw [hcover]
  exact (card_unitModularFiber_biUnion_le_uniform p F rows cols s u b c T
    (fun a => (fun z => (a : ℤ_[p]) • z) '' coset p ξ M) K
    (fun a _ => hK a)).trans (Nat.mul_le_mul_right K hT)

/-- The already uniform bound on one coset transfers to its whole unit orbit.
The fixed finite-cover factor is at most p^M. -/
theorem card_unitOrbit_fiber_le_of_coset_bound
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (rows cols : Fin r → Fin n) (ξ : Fin n → ℤ_[p]) (M K : ℕ)
    (hK : ∀ (s : ℕ) (u : (ZMod (p ^ s))ˣ)
      (b : Untouched cols → ZMod (p ^ s)) (c : Fin r → ZMod (p ^ s)),
      Nat.card (unitModularFiber p F rows cols s (coset p ξ M) u b c) ≤ K)
    (s : ℕ) (u : (ZMod (p ^ s))ˣ)
    (b : Untouched cols → ZMod (p ^ s)) (c : Fin r → ZMod (p ^ s)) :
    Nat.card (unitModularFiber p F rows cols s (unitOrbit p ξ M) u b c) ≤ p ^ M * K := by
  apply card_unitOrbit_fiber_le_of_scaled_bounds p F rows cols ξ M s u b c K
  intro a
  exact CubicGradientScaling.unit_image_fiber_bound p F hF rows cols
    (coset p ξ M) K hK a s u b c

/-- A nonzero possibly nonprincipal Hessian minor of an integral cubic
supplies one unit-invariant orbit with a uniform selected-coordinate fiber bound. -/
theorem exists_unitOrbit_uniform_gradient_fiber_bound
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (rows cols : Fin r → Fin n) (ξ : Fin n → ℤ_[p])
    (hdet : ((hessian (map (Int.castRingHom ℚ_[p]) F)
      (fun k => (ξ k : ℚ_[p]))).submatrix rows cols).det ≠ 0) :
    ∃ M A : ℕ, 1 ≤ M ∧ ∀ (s : ℕ) (u : (ZMod (p ^ s))ˣ)
      (b : Untouched cols → ZMod (p ^ s)) (c : Fin r → ZMod (p ^ s)),
      Nat.card (unitModularFiber p F rows cols s (unitOrbit p ξ M) u b c) ≤
        p ^ (M + A * r) := by
  obtain ⟨M, A, hM, hcount⟩ :=
    exists_coset_uniform_unit_gradient_fiber_bound p F rows cols ξ hdet
  refine ⟨M, A, hM, ?_⟩
  intro s u b c
  simpa only [pow_add] using card_unitOrbit_fiber_le_of_coset_bound p F hF
    rows cols ξ M (p ^ (A * r)) hcount s u b c

/-- The actual full gradient congruence has at most the fixed local constant
times p^(s*(n-r)) residue tuples in the unit orbit. All constants precede
the modulus, unit multiplier and full gradient target. -/
theorem exists_unitOrbit_full_gradient_bound
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (rows cols : Fin r → Fin n) (ξ : Fin n → ℤ_[p])
    (hdet : ((hessian (map (Int.castRingHom ℚ_[p]) F)
      (fun k => (ξ k : ℚ_[p]))).submatrix rows cols).det ≠ 0) :
    ∃ M A : ℕ, 1 ≤ M ∧ ∀ (s : ℕ) (u : (ZMod (p ^ s))ˣ)
      (c : Fin n → ZMod (p ^ s)),
      Nat.card (gradientFiber p F id s (unitOrbit p ξ M) u c) ≤
        p ^ (M + A * r + s * (n - r)) := by
  have hcols := SelectedGradientCoordinates.cols_injective_of_submatrix_det_ne_zero
    _ rows cols hdet
  obtain ⟨M, A, hM, hcount⟩ :=
    exists_unitOrbit_uniform_gradient_fiber_bound p F hF rows cols ξ hdet
  refine ⟨M, A, hM, ?_⟩
  intro s u c
  simpa only [pow_add] using card_full_gradientFiber_le p F rows cols hcols s
    (unitOrbit p ξ M) u c (p ^ (M + A * r))
    (fun b => hcount s u b (fun a => c (rows a)))

end CubicTenVariables.UnitGradientFibers
