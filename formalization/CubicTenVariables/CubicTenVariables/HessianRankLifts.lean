import CubicTenVariables.SmoothResidueIteration
import CubicTenVariables.OnCubicRankCountsTen

/-!
# Actual prime-power root sets with a prescribed initial Hessian rank

The finite partition uses literal reduction modulo p. No lifting estimate,
smoothness, cubic homogeneity, or literature result is needed here.
-/

noncomputable section
namespace CubicTenVariables.HessianRankLifts
open MvPolynomial HessianTheorem11 SmoothResidueIteration
open scoped BigOperators

variable {n : ℕ}

/-- Roots modulo p^a classified by the rank of their actual Hessian modulo p. -/
def rankRoots (F : MvPolynomial (Fin n) ℤ) (p : ℕ) [Fact p.Prime]
    (a : ℕ) (ha : 1 ≤ a) (r : ℕ) : Finset (Fin n → ZMod (p^a)) :=
  Finset.univ.filter fun z => eval₂ (Int.castRingHom (ZMod (p^a))) z F = 0 ∧
    (hessian (map (Int.castRingHom (ZMod p)) F)
      (fun i => toPrime p a ha (z i))).rank = r

@[simp] theorem mem_rankRoots (F : MvPolynomial (Fin n) ℤ) (p : ℕ) [Fact p.Prime]
    (a : ℕ) (ha : 1 ≤ a) (r : ℕ) (z : Fin n → ZMod (p^a)) :
    z ∈ rankRoots F p a ha r ↔
      eval₂ (Int.castRingHom (ZMod (p^a))) z F = 0 ∧
      (hessian (map (Int.castRingHom (ZMod p)) F)
        (fun i => toPrime p a ha (z i))).rank = r := by
  classical
  simp [rankRoots]

/-- Every actual lifted zero reduces to a zero of the original polynomial. -/
theorem reduction_is_root (F : MvPolynomial (Fin n) ℤ) (p : ℕ) [Fact p.Prime]
    (a : ℕ) (ha : 1 ≤ a) (z : Fin n → ZMod (p^a))
    (hz : eval₂ (Int.castRingHom (ZMod (p^a))) z F = 0) :
    eval₂ (Int.castRingHom (ZMod p)) (fun i => toPrime p a ha (z i)) F = 0 := by
  rw [← map_eval₂_int, hz, map_zero]

/-- The fiber of the rank-conditioned root set is the existing literal zero
fiber whenever its prime-field center has the prescribed rank. -/
theorem rankRoots_fiber (F : MvPolynomial (Fin n) ℤ) (p : ℕ) [Fact p.Prime]
    (a : ℕ) (ha : 1 ≤ a) (r : ℕ) (y : Fin n → ZMod p)
    (hy : (hessian (map (Int.castRingHom (ZMod p)) F) y).rank = r) :
    (rankRoots F p a ha r).filter (fun z =>
      (fun i => toPrime p a ha (z i)) = y) = zeroLifts p a ha F y := by
  classical
  ext z
  simp only [Finset.mem_filter, mem_rankRoots, mem_zeroLifts]
  constructor
  · rintro ⟨⟨hz,_⟩,heq⟩
    exact ⟨congrFun heq, hz⟩
  · rintro ⟨heq,hz⟩
    have heq' := funext heq
    exact ⟨⟨hz, by rw [heq']; exact hy⟩,heq'⟩

/-- Exact partition of every actual prime-power root of initial rank r. -/
theorem card_rankRoots_eq_sum (F : MvPolynomial (Fin n) ℤ) (p : ℕ) [Fact p.Prime]
    (a : ℕ) (ha : 1 ≤ a) (r : ℕ) :
    (rankRoots F p a ha r).card =
      ∑ y ∈ Finset.univ.filter (fun y : Fin n → ZMod p =>
        eval₂ (Int.castRingHom (ZMod p)) y F = 0 ∧
        (hessian (map (Int.castRingHom (ZMod p)) F) y).rank = r),
        (zeroLifts p a ha F y).card := by
  classical
  have hmem : ∀ z ∈ rankRoots F p a ha r,
      (fun i => toPrime p a ha (z i)) ∈ Finset.univ.filter
        (fun y : Fin n → ZMod p => eval₂ (Int.castRingHom (ZMod p)) y F = 0 ∧
          (hessian (map (Int.castRingHom (ZMod p)) F) y).rank = r) := by
    intro z hz
    have hz' := (mem_rankRoots F p a ha r z).mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,reduction_is_root F p a ha z hz'.1,hz'.2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmem]
  apply Finset.sum_congr rfl
  intro y hy
  rw [rankRoots_fiber F p a ha r y (Finset.mem_filter.mp hy).2.2]

/-- At level one there is no gamma loss: each base root has exactly one lift. -/
theorem card_rankRoots_one (F : MvPolynomial (Fin n) ℤ) (p : ℕ) [Fact p.Prime]
    (r : ℕ) :
    (rankRoots F p 1 le_rfl r).card =
      (Finset.univ.filter (fun y : Fin n → ZMod p =>
        eval₂ (Int.castRingHom (ZMod p)) y F = 0 ∧
        (hessian (map (Int.castRingHom (ZMod p)) F) y).rank = r)).card := by
  classical
  rw [card_rankRoots_eq_sum]
  have hsum := Finset.sum_congr rfl (fun y (hy : y ∈ Finset.univ.filter
      (fun y : Fin n → ZMod p => eval₂ (Int.castRingHom (ZMod p)) y F = 0 ∧
        (hessian (map (Int.castRingHom (ZMod p)) F) y).rank = r)) =>
    congrArg Finset.card (zeroLifts_one p F y (Finset.mem_filter.mp hy).2.1))
  rw [hsum]
  simp

end CubicTenVariables.HessianRankLifts
