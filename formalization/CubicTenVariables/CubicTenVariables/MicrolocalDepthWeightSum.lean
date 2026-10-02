import CubicTenVariables.MicrolocalDepthSupportCountProved
import CubicTenVariables.FixedFamilyPrimeFieldPointCount

/-! Local positive-moment majorants with alpha=1/2. These are genuine
functions on residue vectors: their five indicators use the actual geometric
depth loci with the origin adjoined. No periodicity of the numerical depths
of integer-frequency prime-square sums is asserted or required. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.MicrolocalDepthWeightSum
open MvPolynomial HessianTheorem11
open ProjectiveMicrolocalData BihomogeneousIncidenceFamily
open MicrolocalDepthSupportCount
open scoped BigOperators Classical

def support {t : ℕ} (f : Fin t → Polynomial 10 10) (p : ℕ) [Fact p.Prime]
    (j : Fin 5) (v : Fin 10 → ZMod p) : Prop :=
  v = 0 ∨ ((j.val+2 : ℕ) : Dimension) ≤
    IntegralGeometricFiberDepth.geometricFiberDimension f (ZMod p) v

def primeExponent (j : Fin 5) : ℝ := (3/2) * (((j.val+2 : ℕ) : ℝ)/2-1)

def squareExponent (j : Fin 5) : ℝ := (3/2) * (((j.val+2 : ℕ) : ℝ)-2)

theorem prime_exponent_le (j : Fin 5) : (profile j : ℝ) + primeExponent j ≤ 8 := by
  fin_cases j <;> norm_num [profile,primeExponent]

theorem square_exponent_le (j : Fin 5) : (profile j : ℝ) + squareExponent j ≤ 9 := by
  fin_cases j <;> norm_num [profile,squareExponent]

def primeWeight {t : ℕ} (f : Fin t → Polynomial 10 10) (p : ℕ) [Fact p.Prime]
    (v : Fin 10 → ZMod p) : ℝ :=
  ∑ j : Fin 5, if support f p j v then (p : ℝ)^(primeExponent j) else 0

def squareWeight {t : ℕ} (f : Fin t → Polynomial 10 10) (p : ℕ) [Fact p.Prime]
    (v : Fin 10 → ZMod p) : ℝ :=
  ∑ j : Fin 5, if support f p j v then (p : ℝ)^(squareExponent j) else 0

private theorem support_card_le {t : ℕ} (f : Fin t → Polynomial 10 10)
    (p : ℕ) [hp : Fact p.Prime] (j : Fin 5) (C : ℕ)
    (hc : Nat.card {v : Fin 10 → ZMod p // ((j.val+2 : ℕ) : Dimension) ≤
      IntegralGeometricFiberDepth.geometricFiberDimension f (ZMod p) v} ≤
        C * p^(profile j)) :
    Nat.card {v : Fin 10 → ZMod p // support f p j v} ≤ (C+1)*p^(profile j) := by
  classical
  let S : Finset (Fin 10 → ZMod p) := Finset.univ.filter fun v =>
    ((j.val+2 : ℕ) : Dimension) ≤
      IntegralGeometricFiberDepth.geometricFiberDimension f (ZMod p) v
  have hS : S.card ≤ C*p^(profile j) := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype] using hc
  have he : Finset.univ.filter (support f p j) = insert 0 S := by
    ext v
    simp [support,S]
  have hcard : Nat.card {v : Fin 10 → ZMod p // support f p j v} =
      (insert 0 S).card := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype,he]
  rw [hcard]
  have hpow : 1 ≤ p^(profile j) := one_le_pow₀ hp.out.one_lt.le
  have hi := Finset.card_insert_le (0 : Fin 10 → ZMod p) S
  nlinarith

private theorem weighted_sum_le {t : ℕ} (f : Fin t → Polynomial 10 10)
    (p : ℕ) [hp : Fact p.Prime] (A : ℝ) (hA : 0 ≤ A)
    (hc : ∀ j : Fin 5, (Nat.card {v : Fin 10 → ZMod p // support f p j v} : ℝ) ≤
      A*(p : ℝ)^(profile j)) (a : Fin 5 → ℝ) (b : ℕ)
    (he : ∀ j : Fin 5, (profile j : ℝ)+a j ≤ b) :
    (∑ v : Fin 10 → ZMod p, ∑ j : Fin 5,
      if support f p j v then (p : ℝ)^(a j) else 0) ≤ (5*A)*(p : ℝ)^b := by
  classical
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast hp.out.one_lt.le
  have hs (j : Fin 5) :
      (∑ v : Fin 10 → ZMod p, if support f p j v then (p : ℝ)^(a j) else 0) =
      (Nat.card {v : Fin 10 → ZMod p // support f p j v} : ℝ)*(p : ℝ)^(a j) := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul,Nat.card_eq_fintype_card,Fintype.card_subtype]
  calc
    _ = ∑ j : Fin 5, (Nat.card {v : Fin 10 → ZMod p // support f p j v} : ℝ)*
        (p : ℝ)^(a j) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun j _ => hs j)
    _ ≤ ∑ _j : Fin 5, A*(p : ℝ)^b := by
      apply Finset.sum_le_sum
      intro j _
      have hpow : (p : ℝ)^(profile j)*(p : ℝ)^(a j) ≤ (p : ℝ)^b := by
        rw [← Real.rpow_natCast,← Real.rpow_add hp0,← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hp1 (he j)
      calc
        _ ≤ (A*(p : ℝ)^(profile j))*(p : ℝ)^(a j) :=
          mul_le_mul_of_nonneg_right (hc j) (Real.rpow_nonneg hp0.le _)
        _ = A*((p : ℝ)^(profile j)*(p : ℝ)^(a j)) := by ring
        _ ≤ A*(p : ℝ)^b := mul_le_mul_of_nonneg_left hpow hA
    _ = (5*A)*(p : ℝ)^b := by simp [Finset.sum_const,nsmul_eq_mul]; ring

/-- Both literal five-indicator residue sums are controlled with the same
constant and excluded integer, fixed before every good prime. -/
theorem exists_uniform_bound (lit : FixedFamilyPrimeFieldPointCount.Uniform)
    {t : ℕ} {F : MvPolynomial (Fin 10) ℤ} {f : Fin t → Polynomial 10 10}
    {N B : ℕ} (h : Geometry F f) (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (hData : TenMicrolocalIncidence.Conclusion F f N B) (hN : 1 ≤ N) :
    ∃ (D : ℕ) (C : ℝ), 1 ≤ D ∧ N ∣ D ∧ 1 ≤ C ∧
      ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ D →
        (∑ v : Fin 10 → ZMod p, primeWeight f p v) ≤ C*(p : ℝ)^8 ∧
        (∑ v : Fin 10 → ZMod p, squareWeight f p v) ≤ C*(p : ℝ)^9 := by
  obtain ⟨D,C,hD,hND,hC,hcount⟩ :=
    MicrolocalDepthSupportCountProved.exists_uniform_bound h hhom hAn hData hN
  refine ⟨D,5*((C : ℝ)+1),hD,hND,?_,?_⟩
  · have hCr : 1 ≤ (C : ℝ) := by exact_mod_cast hC
    linarith
  · intro p hp hpD
    have hc (j : Fin 5) :
        (Nat.card {v : Fin 10 → ZMod p // support f p j v} : ℝ) ≤
          ((C : ℝ)+1)*(p : ℝ)^(profile j) := by
      have hb := hcount j p hp.out hpD (ZMod p)
      rw [ZMod.card] at hb
      exact_mod_cast support_card_le f p j C hb
    exact ⟨weighted_sum_le f p ((C : ℝ)+1) (by positivity) hc primeExponent 8 prime_exponent_le,
      weighted_sum_le f p ((C : ℝ)+1) (by positivity) hc squareExponent 9 square_exponent_le⟩

end CubicTenVariables.MicrolocalDepthWeightSum
