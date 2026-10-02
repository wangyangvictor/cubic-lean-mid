import HessianTheorem11.GeometricInjectivity
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.ZMod.Basic

/-!
An explicit integral determinant controls reduction of the actual linear
Hessian pencil. Rational anisotropy makes this determinant nonzero. Outside
its prime divisors the reduced pencil is injective; the exceptional primes
are bounded by its absolute value. No geometric spreading result is used.
-/

noncomputable section
namespace CubicTenVariables.HessianRankZeroReduction

open MvPolynomial HessianTheorem11 Matrix
open scoped BigOperators Matrix

/-- The literal coefficient matrix of the flattened Hessian pencil. -/
def hessianCoefficientMatrix {R : Type*} [CommRing R] {n : ℕ}
    (F : MvPolynomial (Fin n) R) : Matrix (Fin n × Fin n) (Fin n) R :=
  fun ij k => coeff 0 (pderiv k (pderiv ij.2 (pderiv ij.1 F)))

theorem hessianCoefficientMatrix_map {R S : Type*} [CommRing R] [CommRing S]
    {n : ℕ} (F : MvPolynomial (Fin n) R) (f : R →+* S) :
    hessianCoefficientMatrix (map f F) = (hessianCoefficientMatrix F).map f := by
  ext ij k
  simp [hessianCoefficientMatrix, pderiv_map, coeff_map]

theorem coefficientMatrix_mulVec {R : Type*} [CommRing R] {n : ℕ}
    (F : MvPolynomial (Fin n) R) (hF : F.IsHomogeneous 3) (x : Fin n → R) :
    (hessianCoefficientMatrix F).mulVec x = fun ij => hessian F x ij.1 ij.2 := by
  ext ij
  simp only [mulVec, dotProduct, hessianCoefficientMatrix, hessian_entry_expansion hF]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/-- The Gram determinant is an integer certificate, not a field-extension premise. -/
def hessianDiscriminant {n : ℕ} (F : MvPolynomial (Fin n) ℤ) : ℤ :=
  ((hessianCoefficientMatrix F).transpose * hessianCoefficientMatrix F).det

theorem gram_map {R S α β : Type*} [CommRing R] [CommRing S] [Fintype α]
    (B : Matrix α β R) (f : R →+* S) :
    (B.transpose * B).map f = (B.map f).transpose * B.map f := by
  rw [Matrix.map_mul]
  rfl

/-- Rational injectivity of an integral rectangular matrix gives a nonzero
integral Gram determinant, also for a zero-dimensional domain. -/
theorem gram_det_ne_zero_of_rational_injective {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq β]
    (B : Matrix α β ℤ)
    (hB : Function.Injective (B.map (Int.castRingHom ℚ)).mulVec) :
    (B.transpose * B).det ≠ 0 := by
  let Q := B.map (Int.castRingHom ℚ)
  have hk : LinearMap.ker (Q.transpose * Q).mulVecLin = ⊥ := by
    rw [Matrix.ker_mulVecLin_transpose_mul_self]
    exact LinearMap.ker_eq_bot.mpr hB
  have hu : IsUnit (Q.transpose * Q) :=
    Matrix.mulVec_injective_iff_isUnit.mp (LinearMap.ker_eq_bot.mp hk)
  have hd : (Q.transpose * Q).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  intro hz
  apply hd
  change ((B.map (Int.castRingHom ℚ)).transpose * B.map (Int.castRingHom ℚ)).det = 0
  rw [← gram_map]
  have he := (Int.castRingHom ℚ).map_det (B.transpose * B)
  rw [hz, map_zero] at he
  exact he.symm

theorem hessianDiscriminant_ne_zero {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    hessianDiscriminant F ≠ 0 := by
  apply gram_det_ne_zero_of_rational_injective
  rw [← hessianCoefficientMatrix_map]
  intro x y hxy
  apply rational_hessian_injective ⟨map (Int.castRingHom ℚ) F, hF.map _, hA⟩
  have he := hxy
  rw [coefficientMatrix_mulVec _ (hF.map _) x,
    coefficientMatrix_mulVec _ (hF.map _) y] at he
  exact funext (fun i => funext (fun j => congrFun he (i, j)))

/-- Inverting the displayed determinant makes the reduced rectangular map
injective. This argument uses an actual determinant modulo p. -/
theorem reduction_injective_of_not_dvd_gram_det {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq β]
    (B : Matrix α β ℤ) (p : ℕ) [Fact p.Prime]
    (hp : ¬ (p : ℤ) ∣ (B.transpose * B).det) :
    Function.Injective (B.map (Int.castRingHom (ZMod p))).mulVec := by
  let Q := B.map (Int.castRingHom (ZMod p))
  have hd : (Q.transpose * Q).det ≠ 0 := by
    change ((B.map (Int.castRingHom (ZMod p))).transpose *
      B.map (Int.castRingHom (ZMod p))).det ≠ 0
    rw [← gram_map]
    have he := (Int.castRingHom (ZMod p)).map_det (B.transpose * B)
    intro hz
    apply hp
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    exact he.trans hz
  have hu : IsUnit (Q.transpose * Q) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd)
  have hi := Matrix.mulVec_injective_iff_isUnit.mpr hu
  intro x y hxy
  apply hi
  simp only [← Matrix.mulVec_mulVec]
  exact congrArg Q.transpose.mulVec hxy

theorem hessianReduction_injective_of_not_dvd {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (p : ℕ) [Fact p.Prime] (hp : ¬ (p : ℤ) ∣ hessianDiscriminant F) :
    Function.Injective (hessian (map (Int.castRingHom (ZMod p)) F)) := by
  have hi := reduction_injective_of_not_dvd_gram_det (hessianCoefficientMatrix F) p hp
  rw [← hessianCoefficientMatrix_map] at hi
  intro x y hxy
  apply hi
  rw [coefficientMatrix_mulVec _ (hF.map _) x,
    coefficientMatrix_mulVec _ (hF.map _) y, hxy]

theorem rank_zero_iff_of_not_dvd {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (p : ℕ) [Fact p.Prime] (hp : ¬ (p : ℤ) ∣ hessianDiscriminant F)
    (x : Fin n → ZMod p) :
    (hessian (map (Int.castRingHom (ZMod p)) F) x).rank = 0 ↔ x = 0 := by
  constructor
  · intro hx
    apply hessianReduction_injective_of_not_dvd F hF p hp
    rw [hessian_zero (hF.map _)]
    exact matrix_eq_zero_of_rank_eq_zero _ hx
  · rintro rfl
    rw [hessian_zero (hF.map _), Matrix.rank_zero]

/-- Literal full-affine-space rank-zero points, with no cubic equation imposed. -/
def rankZeroPoints {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (p : ℕ) [Fact p.Prime] : Finset (Fin n → ZMod p) := by
  classical
  exact Finset.univ.filter (fun x => (hessian (map (Int.castRingHom (ZMod p)) F) x).rank = 0)

theorem rankZeroPoints_eq_singleton_of_not_dvd {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (p : ℕ) [Fact p.Prime] (hp : ¬ (p : ℤ) ∣ hessianDiscriminant F) :
    rankZeroPoints F p = {0} := by
  classical
  ext x
  simp only [rankZeroPoints, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton, rank_zero_iff_of_not_dvd F hF p hp]

/-- A nonzero integer is constructed before the prime, with both literal
injectivity and the exact full-affine-space rank-zero set at every good prime. -/
theorem exists_good_prime_certificate {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ Δ : ℤ, Δ ≠ 0 ∧ ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      ¬ (p : ℤ) ∣ Δ →
        Function.Injective (hessian (map (Int.castRingHom (ZMod p)) F)) ∧
        rankZeroPoints F p = {0} := by
  refine ⟨hessianDiscriminant F, hessianDiscriminant_ne_zero F hF hA, ?_⟩
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  intro hgood
  exact ⟨hessianReduction_injective_of_not_dvd F hF p hgood,
    rankZeroPoints_eq_singleton_of_not_dvd F hF p hgood⟩

theorem card_rankZeroPoints_le {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F))
    (p : ℕ) [Fact p.Prime] :
    (rankZeroPoints F p).card ≤ max 1 ((hessianDiscriminant F).natAbs ^ n) := by
  classical
  by_cases hp : (p : ℤ) ∣ hessianDiscriminant F
  · have hple : p ≤ (hessianDiscriminant F).natAbs := by
      simpa only [Int.natAbs_natCast] using
        Int.natAbs_le_of_dvd_ne_zero hp (hessianDiscriminant_ne_zero F hF hA)
    calc
      _ ≤ Fintype.card (Fin n → ZMod p) := Finset.card_le_univ _
      _ = p ^ n := by simp [ZMod.card]
      _ ≤ (hessianDiscriminant F).natAbs ^ n := Nat.pow_le_pow_left hple n
      _ ≤ _ := le_max_right _ _
  · rw [rankZeroPoints_eq_singleton_of_not_dvd F hF p hp, Finset.card_singleton]
    exact le_max_left _ _

/-- One positive explicit constant is fixed before every prime. -/
theorem exists_uniform_rankZero_bound {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℕ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      (rankZeroPoints F p).card ≤ C := by
  refine ⟨max 1 ((hessianDiscriminant F).natAbs ^ n),
    lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _), ?_⟩
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  exact card_rankZeroPoints_le F hF hA p

/-- Imposing the literal cubic equation only reduces this uniform count. -/
theorem card_onCubic_rankZero_le {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F))
    (p : ℕ) [Fact p.Prime] :
    ((rankZeroPoints F p).filter
      (fun x => eval x (map (Int.castRingHom (ZMod p)) F) = 0)).card ≤
        max 1 ((hessianDiscriminant F).natAbs ^ n) := by
  exact (Finset.card_filter_le _ _).trans (card_rankZeroPoints_le F hF hA p)

end CubicTenVariables.HessianRankZeroReduction
