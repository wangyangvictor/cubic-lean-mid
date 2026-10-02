import CubicTenVariables.MatrixSmithProfileInvariant
import CubicTenVariables.HessianRankLifts

/-!
# Actual cubic roots with their complete cumulative Hessian profile

The profile is that of the literal Hessian matrix modulo the prime power.
The definitions retain the cubic equation. Integral lifts are used only
through the proved independence of representatives.
-/

noncomputable section
namespace CubicTenVariables.HessianProfileRoots
open MvPolynomial HessianTheorem11 MatrixSmithProfileInvariant
open SmoothResidueIteration PrimePowerFibers
open scoped BigOperators

variable {n : ℕ}

def matrix (F : MvPolynomial (Fin n) ℤ) (q : ℕ) (z : Fin n → ZMod q) :
    Matrix (Fin n) (Fin n) (ZMod q) :=
  hessian (map (Int.castRingHom (ZMod q)) F) z

theorem matrix_apply (F : MvPolynomial (Fin n) ℤ) (q : ℕ)
    (z : Fin n → ZMod q) (i j : Fin n) :
    matrix F q z i j = eval₂ (Int.castRingHom (ZMod q)) z (pderiv j (pderiv i F)) := by
  simp [matrix, hessian, hessianPolynomial, pderiv_map, eval_map]

theorem matrix_map (F : MvPolynomial (Fin n) ℤ) {q r : ℕ}
    (f : ZMod q →+* ZMod r) (z : Fin n → ZMod q) :
    (matrix F q z).map f = matrix F r (fun i => f (z i)) := by
  ext i j
  simp only [Matrix.map_apply, matrix_apply, map_eval₂_int]

theorem matrix_int_cast (F : MvPolynomial (Fin n) ℤ) (q : ℕ)
    (z : Fin n → ℤ) :
    (hessian F z).map (Int.castRingHom (ZMod q)) =
      matrix F q (fun i => (z i : ZMod q)) := by
  ext i j
  rw [Matrix.map_apply, matrix_apply]
  exact SmoothResidueLifting.cast_eval_int _ q z

def profileEntry (F : MvPolynomial (Fin n) ℤ) (p a : ℕ)
    (z : Fin n → ZMod (p^a)) (i : ℕ) : ℕ :=
  residueEntry p a (matrix F (p^a) z) i

theorem profileEntry_int_cast (F : MvPolynomial (Fin n) ℤ) (p : ℕ)
    (hp : p.Prime) {a i : ℕ} (hi : i < a) (z : Fin n → ℤ) :
    profileEntry F p a (fun j => (z j : ZMod (p^a))) i =
      entry (hessian F z) p i := by
  unfold profileEntry
  rw [← matrix_int_cast]
  exact residueEntry_map_int _ p hp hi

theorem profileEntry_reduction (F : MvPolynomial (Fin n) ℤ) (p : ℕ)
    (hp : p.Prime) {a b i : ℕ} (hb : b ≤ a) (hi : i < b)
    (z : Fin n → ZMod (p^a)) :
    profileEntry F p b (fun j => reduction p hb (z j)) i =
      profileEntry F p a z i := by
  unfold profileEntry
  rw [← matrix_map]
  exact residueEntry_reduction p hp hb hi _

theorem profileEntry_zero (F : MvPolynomial (Fin n) ℤ) (p : ℕ)
    (hp : p.Prime) (a : ℕ) (ha : 1 ≤ a) (z : Fin n → ZMod (p^a)) :
    profileEntry F p a z 0 =
      (matrix F p (fun i => toPrime p a ha (z i))).rank := by
  letI : NeZero (p^a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let y : Fin n → ℤ := fun i => (z i).val
  have hy : (fun i => (y i : ZMod (p^a))) = z := by
    funext i
    simp [y]
  rw [← hy, profileEntry_int_cast F p hp (by omega), entry_zero_eq_rank _ p hp, matrix_int_cast]
  congr 1
  funext i
  simp only [map_intCast]

/-- Every actual root with every prescribed profile entry below the level.
The label is a natural sequence so truncation needs no auxiliary choices. -/
def roots (F : MvPolynomial (Fin n) ℤ) (p : ℕ) [Fact p.Prime]
    (a : ℕ) (c : ℕ → ℕ) : Finset (Fin n → ZMod (p^a)) :=
  Finset.univ.filter fun z => eval₂ (Int.castRingHom (ZMod (p^a))) z F = 0 ∧
    ∀ i < a, profileEntry F p a z i = c i

@[simp] theorem mem_roots (F : MvPolynomial (Fin n) ℤ) (p : ℕ) [Fact p.Prime]
    (a : ℕ) (c : ℕ → ℕ) (z : Fin n → ZMod (p^a)) :
    z ∈ roots F p a c ↔ eval₂ (Int.castRingHom (ZMod (p^a))) z F = 0 ∧
      ∀ i < a, profileEntry F p a z i = c i := by
  classical
  simp [roots]

theorem reduction_mem_roots (F : MvPolynomial (Fin n) ℤ) (p : ℕ) [Fact p.Prime]
    {a b : ℕ} (hb : b ≤ a) (c : ℕ → ℕ) (z : Fin n → ZMod (p^a))
    (hz : z ∈ roots F p a c) :
    (fun i => reduction p hb (z i)) ∈ roots F p b c := by
  rw [mem_roots] at hz ⊢
  refine ⟨?_, fun i hi => ?_⟩
  · rw [← map_eval₂_int, hz.1, map_zero]
  · rw [profileEntry_reduction F p Fact.out hb hi]
    exact hz.2 i (hi.trans_le hb)

theorem roots_subset_rankRoots (F : MvPolynomial (Fin n) ℤ) (p : ℕ) [Fact p.Prime]
    (a : ℕ) (ha : 1 ≤ a) (c : ℕ → ℕ) :
    roots F p a c ⊆ HessianRankLifts.rankRoots F p a ha (c 0) := by
  intro z hz
  have hz := (mem_roots F p a c z).mp hz
  rw [HessianRankLifts.mem_rankRoots]
  refine ⟨hz.1, ?_⟩
  exact (profileEntry_zero F p Fact.out a ha z).symm.trans (hz.2 0 (by omega))

theorem roots_one (F : MvPolynomial (Fin n) ℤ) (p : ℕ) [Fact p.Prime]
    (c : ℕ → ℕ) :
    roots F p 1 c = HessianRankLifts.rankRoots F p 1 le_rfl (c 0) := by
  apply Finset.Subset.antisymm (roots_subset_rankRoots F p 1 le_rfl c)
  intro z hz
  rw [HessianRankLifts.mem_rankRoots] at hz
  rw [mem_roots]
  refine ⟨hz.1, ?_⟩
  intro i hi
  have hi0 : i = 0 := by omega
  subst i
  exact (profileEntry_zero F p Fact.out 1 le_rfl z).trans hz.2

/-- The initial bound is for the actual profile root set, uniformly in all
prime fields and all sequences whose first entry is a possible rank. -/
theorem exists_initial_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) [Fact p.Prime], ∀ c : ℕ → ℕ, c 0 ≤ 10 →
      (roots F p 1 c).card ≤ C*p^(OnCubicRankCountsTen.deltaNat (c 0)) := by
  obtain ⟨C, hC, hc⟩ := OnCubicRankCountsTen.exists_uniform_exact_rank_profile F hF hA
  refine ⟨C, hC, ?_⟩
  intro p hp c hc0
  rw [roots_one, HessianRankLifts.card_rankRoots_one]
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hc p (c 0) hc0

/-- Exact finite partition by the preceding residue class. -/
theorem card_roots_succ_eq_sum (F : MvPolynomial (Fin n) ℤ) (p : ℕ) [Fact p.Prime]
    (a : ℕ) (c : ℕ → ℕ) :
    (roots F p (a+1) c).card =
      ∑ y ∈ roots F p a c, ((roots F p (a+1) c).filter fun z =>
        (fun i => reduction p (Nat.le_succ a) (z i)) = y).card := by
  classical
  exact Finset.card_eq_sum_card_fiberwise (fun z hz =>
    reduction_mem_roots F p (Nat.le_succ a) c z hz)

end CubicTenVariables.HessianProfileRoots
