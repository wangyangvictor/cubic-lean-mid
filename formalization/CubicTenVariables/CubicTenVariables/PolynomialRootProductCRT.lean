import CubicTenVariables.WeightedCRTAdapters
import CubicTenVariables.SecondLiftSum
import Mathlib.Data.ZMod.QuotientRing

/-! Exact finite-product CRT for weighted polynomial roots. -/

noncomputable section
namespace CubicTenVariables.PolynomialRootProductCRT
open MvPolynomial
open scoped BigOperators

variable {ι R : Type*} [Fintype ι] [CommSemiring R]

/-- The literal reduction from the product modulus to a factor. -/
def projection (q : ι → ℕ) (i : ι) : ZMod (∏ j, q j) →+* ZMod (q i) :=
  ZMod.castHom (by classical exact Finset.dvd_prod_of_mem q (Finset.mem_univ i)) (ZMod (q i))

theorem prodEquivPi_apply (q : ι → ℕ)
    (hc : Pairwise fun i j => (q i).Coprime (q j))
    (x : ZMod (∏ j, q j)) (i : ι) :
    ZMod.prodEquivPi q hc x i = projection q i x := by
  have h : (Pi.evalRingHom (fun j => ZMod (q j)) i).comp
      (ZMod.prodEquivPi q hc).toRingHom = projection q i := Subsingleton.elim _ _
  exact congrArg (fun f : ZMod (∏ j, q j) →+* ZMod (q i) => f x) h

def vectorEquiv (q : ι → ℕ)
    (hc : Pairwise fun i j => (q i).Coprime (q j)) (n : ℕ) :
    (Fin n → ZMod (∏ j, q j)) ≃ (∀ j, Fin n → ZMod (q j)) :=
  (Equiv.piCongrRight fun _ => (ZMod.prodEquivPi q hc).toEquiv).trans
    (Equiv.piComm fun (_ : Fin n) j => ZMod (q j))

@[simp] theorem vectorEquiv_apply (q : ι → ℕ)
    (hc : Pairwise fun i j => (q i).Coprime (q j)) (n : ℕ)
    (x : Fin n → ZMod (∏ j, q j)) (j : ι) (i : Fin n) :
    vectorEquiv q hc n x j i = projection q j (x i) :=
  prodEquivPi_apply q hc (x i) j

theorem zero_iff (q : ι → ℕ)
    (hc : Pairwise fun i j => (q i).Coprime (q j)) {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (x : Fin n → ZMod (∏ j, q j)) :
    eval₂ (Int.castRingHom (ZMod (∏ j, q j))) x F = 0 ↔
      ∀ j, eval₂ (Int.castRingHom (ZMod (q j))) (fun i => projection q j (x i)) F = 0 := by
  constructor
  · intro hx j
    rw [← WeightedCRTAdapters.map_eval₂_int, hx, map_zero]
  · intro hx
    apply (ZMod.prodEquivPi q hc).injective
    ext j
    rw [prodEquivPi_apply, map_zero, Pi.zero_apply]
    exact (WeightedCRTAdapters.map_eval₂_int _ F x).trans (hx j)

section Finite
variable (q : ι → ℕ) [∀ j, NeZero (q j)]
    (hc : Pairwise fun i j => (q i).Coprime (q j))

instance productNeZero : NeZero (∏ j, q j) := by
  classical
  exact ⟨Finset.prod_ne_zero_iff.mpr (fun j _ => NeZero.ne (q j))⟩

include hc

theorem sum_product (n : ℕ) (w : ∀ j, (Fin n → ZMod (q j)) → R) :
    (∑ x : Fin n → ZMod (∏ j, q j), ∏ j, w j (fun i => projection q j (x i))) =
      ∏ j, ∑ y : Fin n → ZMod (q j), w j y := by
  classical
  calc
    _ = ∑ x : ∀ j, Fin n → ZMod (q j), ∏ j, w j (x j) := by
      apply Fintype.sum_equiv (vectorEquiv q hc n)
      intro x
      apply Finset.prod_congr rfl
      intro j _
      congr 1
      funext i
      exact (vectorEquiv_apply q hc n x j i).symm
    _ = _ := (Fintype.prod_sum w).symm

/-- Exact factorization with the actual polynomial zero condition retained. -/
theorem sum_roots_product {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (w : ∀ j, (Fin n → ZMod (q j)) → R) :
    (∑ x : Fin n → ZMod (∏ j, q j),
      if eval₂ (Int.castRingHom (ZMod (∏ j, q j))) x F = 0 then
        ∏ j, w j (fun i => projection q j (x i)) else 0) =
      ∏ j, ∑ y : Fin n → ZMod (q j),
        if eval₂ (Int.castRingHom (ZMod (q j))) y F = 0 then w j y else 0 := by
  classical
  rw [← sum_product q hc n (fun j y =>
    if eval₂ (Int.castRingHom (ZMod (q j))) y F = 0 then w j y else 0)]
  apply Finset.sum_congr rfl
  intro x _
  simp only [zero_iff q hc F x]
  by_cases h : ∀ j, eval₂ (Int.castRingHom (ZMod (q j)))
      (fun i => projection q j (x i)) F = 0
  · simp only [h, implies_true, if_true]
  · rw [if_neg h]
    obtain ⟨j,hj⟩ := not_forall.mp h
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact if_neg hj

/-- The same identity for the canonical integer representatives used by
the flexible lifting theorem. Empty products have modulus one. -/
theorem sum_roots_fin_product {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (w : ∀ j, (Fin n → ZMod (q j)) → R) :
    (∑ x : Fin n → Fin (∏ j, q j),
      if ((∏ j, q j : ℕ) : ℤ) ∣ eval (SecondLiftSum.integerVector x) F then
        ∏ j, w j (fun i => ((x i).val : ZMod (q j))) else 0) =
      ∏ j, ∑ y : Fin n → ZMod (q j),
        if eval₂ (Int.castRingHom (ZMod (q j))) y F = 0 then w j y else 0 := by
  classical
  rw [← sum_roots_product q hc F w]
  apply Fintype.sum_equiv (PrimeSumAdapter.vectorResidueEquiv (∏ j, q j) n)
  intro x
  have he : eval₂ (Int.castRingHom (ZMod (∏ j, q j)))
      (PrimeSumAdapter.vectorResidueEquiv (∏ j, q j) n x) F =
      ((eval (SecondLiftSum.integerVector x) F : ℤ) : ZMod (∏ j, q j)) := by
    symm
    simpa only [SecondLiftSum.integerVector, PrimeSumAdapter.vectorResidueEquiv_apply,
      Int.cast_natCast, Function.comp_def, Int.coe_castRingHom, eval₂_eq_eval_map] using
        (MvPolynomial.map_eval (Int.castRingHom (ZMod (∏ j, q j)))
          (SecondLiftSum.integerVector x) F)
  simp only [he, ZMod.intCast_zmod_eq_zero_iff_dvd]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  congr 1
  funext i
  simp only [PrimeSumAdapter.vectorResidueEquiv_apply, map_natCast]

end Finite
end CubicTenVariables.PolynomialRootProductCRT
