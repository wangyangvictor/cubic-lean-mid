import CubicTenVariables.PolynomialResidueCRT

/-!
Finite CRT summation and the actual directional-derivative character phase.
Both inverse-modulus twists are retained. The polynomial and direction are
integral, but no degree or homogeneity hypothesis is needed.
-/

noncomputable section
namespace CubicTenVariables.WeightedCRTAdapters

open MvPolynomial CRTCharacters
open scoped BigOperators

/-- Reindex a product weight by the genuine vector CRT equivalence. -/
theorem sum_crt_product {α : Type*} [CommSemiring α] {d m n : ℕ}
    [NeZero m] [NeZero n] (h : m.Coprime n)
    (L : (Fin d → ZMod m) → α) (R : (Fin d → ZMod n) → α) :
    (∑ x : Fin d → ZMod (m*n),
      L (fun i => leftProjection h (x i)) * R (fun i => rightProjection h (x i))) =
      (∑ x, L x) * ∑ y, R y := by
  classical
  calc
    _ = ∑ p : (Fin d → ZMod m) × (Fin d → ZMod n), L p.1 * R p.2 := by
      apply Fintype.sum_equiv (vectorEquiv h d)
      intro x
      rfl
    _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_mul_sum]

/-- Evaluation of an integral polynomial commutes with any residue-ring map. -/
theorem map_eval₂_int {d : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (F : MvPolynomial (Fin d) ℤ) (x : Fin d → R) :
    f (eval₂ (Int.castRingHom R) x F) =
      eval₂ (Int.castRingHom S) (fun i => f (x i)) F := by
  have hc : f.comp (Int.castRingHom R) = Int.castRingHom S := by ext k; simp
  simpa only [hc, Function.comp_def] using eval₂_comp_left f (Int.castRingHom R) x F

/-- The literal phase h dot gradient F(x), formed using formal partials. -/
def directionalPhase {d : ℕ} {R : Type*} [CommRing R]
    (F : MvPolynomial (Fin d) ℤ) (h : Fin d → ℤ) (x : Fin d → R) : R :=
  ∑ i, (h i : R) * eval₂ (Int.castRingHom R) x (pderiv i F)

theorem map_directionalPhase {d : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (F : MvPolynomial (Fin d) ℤ)
    (h : Fin d → ℤ) (x : Fin d → R) :
    f (directionalPhase F h x) = directionalPhase F h (fun i => f (x i)) := by
  simp only [directionalPhase, map_sum, map_mul, map_intCast, map_eval₂_int]

/-- Exact character factorization, with the inverse of the opposite modulus
multiplying the scalar in each local factor. -/
theorem stdAddChar_directionalPhase_crt {d m n : ℕ} [NeZero m] [NeZero n]
    (hc : m.Coprime n) (F : MvPolynomial (Fin d) ℤ)
    (h : Fin d → ℤ) (a : ZMod (m*n)) (x : Fin d → ZMod (m*n)) :
    ZMod.stdAddChar (a * directionalPhase F h x) =
      ZMod.stdAddChar (((leftTwist hc : ZMod m) * leftProjection hc a) *
        directionalPhase F h (fun i => leftProjection hc (x i))) *
      ZMod.stdAddChar (((rightTwist hc : ZMod n) * rightProjection hc a) *
        directionalPhase F h (fun i => rightProjection hc (x i))) := by
  rw [stdAddChar_crt hc]
  simp only [map_mul, map_directionalPhase, mul_assoc]

end CubicTenVariables.WeightedCRTAdapters
