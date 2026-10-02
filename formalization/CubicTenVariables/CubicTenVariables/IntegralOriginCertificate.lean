import HessianTheorem11.Geometry
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Data.ZMod.Basic

/-! A characteristic-zero origin locus gives an integral certificate and a
uniform bound for its finite-field reductions. Denominators are cleared in
an actual ideal; no geometric spreading theorem is assumed. -/
noncomputable section
namespace CubicTenVariables.IntegralOriginCertificate
open MvPolynomial HessianTheorem11
open scoped BigOperators
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- The literal extension of an integral polynomial ideal to rational coefficients. -/
def rationalIdeal {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℤ)) :
    Ideal (MvPolynomial (Fin n) ℚ) :=
  I.map (algebraMap (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℚ))

/-- Each coordinate has a power in the ideal after multiplication by a
nonzero integer. The hypothesis concerns actual geometric zeros over Qbar. -/
theorem coordinate_certificate {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℤ))
    (hI : zeroLocus GeometricField (rationalIdeal I) ⊆ {0}) (i : Fin n) :
    ∃ (d : ℤ) (e : ℕ), d ≠ 0 ∧ C d * (X i) ^ e ∈ I := by
  have hx : (X i : MvPolynomial (Fin n) ℚ) ∈ (rationalIdeal I).radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := GeometricField)]
    intro x hx
    have he : x = 0 := Set.mem_singleton_iff.mp (hI hx)
    simp [he]
  obtain ⟨e, he⟩ := Ideal.mem_radical_iff.mp hx
  have hm : algebraMap (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℚ)
      ((X i) ^ e) ∈ rationalIdeal I := by
    simpa [MvPolynomial.algebraMap_def] using he
  obtain ⟨m, hm, hi⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff
      ((nonZeroDivisors ℤ).map (C (σ := Fin n)))
      (MvPolynomial (Fin n) ℚ) I ((X i) ^ e)).mp hm
  obtain ⟨d, hd, rfl⟩ := hm
  exact ⟨d, e, mem_nonZeroDivisors_iff_ne_zero.mp hd, hi⟩

/-- One nonzero integer works for all coordinates simultaneously. -/
theorem common_certificate {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℤ))
    (hI : zeroLocus GeometricField (rationalIdeal I) ⊆ {0}) :
    ∃ (D : ℤ) (e : Fin n → ℕ), D ≠ 0 ∧ ∀ i, C D * (X i) ^ e i ∈ I := by
  classical
  choose d e hd he using coordinate_certificate I hI
  refine ⟨∏ i, d i, e, Finset.prod_ne_zero_iff.mpr (fun i _ => hd i), ?_⟩
  intro i
  have hm := I.mul_mem_left (C (∏ j ∈ Finset.univ.erase i, d j)) (he i)
  rw [← mul_assoc, ← map_mul] at hm
  have hp : (∏ j ∈ Finset.univ.erase i, d j) * d i = ∏ j, d j := by
    rw [mul_comm, Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  rwa [hp] at hm

/-- A good prime detects every coordinate from the integral identities. -/
theorem zero_of_certificate {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℤ))
    (D : ℤ) (e : Fin n → ℕ) (he : ∀ i, C D * (X i) ^ e i ∈ I)
    (p : ℕ) [Fact p.Prime] (hp : ¬ (p : ℤ) ∣ D) (x : Fin n → ZMod p)
    (hx : ∀ f ∈ I, eval₂ (Int.castRingHom (ZMod p)) x f = 0) : x = 0 := by
  have hd : (D : ZMod p) ≠ 0 := by
    intro hz
    exact hp ((ZMod.intCast_zmod_eq_zero_iff_dvd D p).mp hz)
  ext i
  have h := hx _ (he i)
  simp only [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X] at h
  exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp h).resolve_left hd)

/-- Every prime outside one fixed finite exceptional set has at most the origin. -/
theorem exists_good_prime_certificate {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℤ))
    (hI : zeroLocus GeometricField (rationalIdeal I) ⊆ {0}) :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      ¬ (p : ℤ) ∣ D → ∀ x : Fin n → ZMod p,
        (∀ f ∈ I, eval₂ (Int.castRingHom (ZMod p)) x f = 0) → x = 0 := by
  obtain ⟨D, e, hd, he⟩ := common_certificate I hI
  refine ⟨D, hd, ?_⟩
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  exact zero_of_certificate I D e he p

end CubicTenVariables.IntegralOriginCertificate
