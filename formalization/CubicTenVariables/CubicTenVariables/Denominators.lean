import CubicTenVariables.Targets
import HessianTheorem11.LocalCubicNormalForm

/-! Literal coefficient and coordinate denominator clearing. Every polynomial
and every zero in the conclusions is the actual polynomial or vector; no
arithmetic existence theorem is assumed. -/

noncomputable section
namespace CubicTenVariables
open MvPolynomial

/-- One positive integer clears a finite family of rational numbers. -/
theorem exists_integral_multiple_family {ι : Type*} [Fintype ι] (x : ι → ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∃ z : ι → ℤ, ∀ i, (z i : ℚ) = (D : ℚ) * x i := by
  classical
  let D : ℕ := ∏ i, (x i).den
  have hD : 0 < D := Finset.prod_pos (fun i _ => (x i).den_pos)
  have hex (i : ι) : ∃ z : ℤ, (z : ℚ) = (D : ℚ) * x i := by
    have hdiv : (x i).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    obtain ⟨k, hk⟩ := hdiv
    refine ⟨(x i).num * (k : ℤ), ?_⟩
    rw [hk]
    have hcross : ((x i).num : ℚ) = ((x i).den : ℚ) * x i := by
      calc
        ((x i).num : ℚ) = ((x i).den : ℚ) *
            (((x i).num : ℚ) / (x i).den) := by field_simp
        _ = ((x i).den : ℚ) * x i := by rw [Rat.num_div_den]
    push_cast
    rw [hcross]
    ring
  choose z hz using hex
  exact ⟨D, hD, z, hz⟩

/-- A nonzero integer multiple of a rational homogeneous polynomial is the
coefficient extension of an integer polynomial of exactly the same homogeneous
degree. This includes the zero polynomial and degree zero. -/
theorem exists_integral_homogeneous_multiple {σ : Type*} {d : ℕ}
    (F : MvPolynomial σ ℚ) (hF : F.IsHomogeneous d) :
    ∃ c : ℤ, c ≠ 0 ∧ ∃ G : MvPolynomial σ ℤ,
      G.IsHomogeneous d ∧ map (Int.castRingHom ℚ) G = C (c : ℚ) * F := by
  classical
  obtain ⟨D, hD, a, ha⟩ := exists_integral_multiple_family
    (fun m : F.support => F.coeff m.val)
  let G : MvPolynomial σ ℤ := ∑ m : F.support, monomial m.val (a m)
  have hmap : map (Int.castRingHom ℚ) G = C (D : ℚ) * F := by
    ext m
    rw [coeff_map, coeff_C_mul]
    dsimp only [G]
    rw [coeff_sum]
    by_cases hm : m ∈ F.support
    · rw [Finset.sum_eq_single ⟨m, hm⟩]
      · simpa only [coeff_monomial, if_pos rfl] using ha ⟨m, hm⟩
      · intro u _ hne
        rw [coeff_monomial, if_neg]
        exact fun he => hne (Subtype.ext he)
      · simp
    · have hz : ∀ u : F.support, coeff m (monomial u.val (a u)) = 0 := by
        intro u
        rw [coeff_monomial, if_neg]
        exact fun he => hm (he ▸ u.property)
      simp [hz, notMem_support_iff.mp hm]
  refine ⟨D, by exact_mod_cast hD.ne', G, ?_, ?_⟩
  · apply IsHomogeneous.of_map (f := Int.castRingHom ℚ) Int.cast_injective
    rw [hmap]
    exact hF.C_mul _
  · simpa using hmap

/-- Integral solutions remain nonzero rational solutions under coefficient
extension. No homogeneity is needed in this direction. -/
theorem hasRationalZero_of_hasIntegerZero {n : ℕ}
    {G : MvPolynomial (Fin n) ℤ} (hG : HasIntegerZero G) :
    HasRationalZero (map (Int.castRingHom ℚ) G) := by
  obtain ⟨z, hz, hzero⟩ := hG
  refine ⟨fun i => (z i : ℚ), ?_, ?_⟩
  · intro he
    apply hz
    funext i
    apply Int.cast_injective (α := ℚ)
    simpa using congrFun he i
  · have he := MvPolynomial.map_eval (Int.castRingHom ℚ) z G
    simpa only [hzero, map_zero, Function.comp_apply] using he.symm

/-- Clear the coordinates of a rational zero by one common nonzero scalar;
homogeneity ensures that the resulting actual integer vector is still a zero. -/
theorem hasIntegerZero_of_hasRationalZero {n d : ℕ}
    {G : MvPolynomial (Fin n) ℤ} (hG : G.IsHomogeneous d)
    (hzero : HasRationalZero (map (Int.castRingHom ℚ) G)) : HasIntegerZero G := by
  obtain ⟨x, hx, hFx⟩ := hzero
  obtain ⟨D, hD, z, hz⟩ := exists_integral_multiple_family x
  have hDQ : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  refine ⟨z, ?_, ?_⟩
  · intro hzz
    apply hx
    funext i
    have hi := hz i
    rw [hzz, Pi.zero_apply, Int.cast_zero] at hi
    exact (mul_eq_zero.mp hi.symm).resolve_left hDQ
  · apply Int.cast_injective (α := ℚ)
    have hscale := HessianTheorem11.LocalCubicNormalForm.homogeneous_eval₂_common_scalar
      (map (Int.castRingHom ℚ) G) (hG.map _) (RingHom.id ℚ) x (D : ℚ)
    have hzfun : (fun i => (z i : ℚ)) = fun i => (D : ℚ) * x i := funext hz
    have heval : eval (fun i => (z i : ℚ)) (map (Int.castRingHom ℚ) G) = 0 := by
      rw [hzfun]
      simpa only [eval₂_id, hFx, mul_zero] using hscale
    have he := MvPolynomial.map_eval (Int.castRingHom ℚ) z G
    simpa only [Int.cast_zero] using he.trans heval

/-- For homogeneous integer polynomials, rational and integer nonzero zeros
are equivalent. All degrees and all numbers of variables are included. -/
theorem hasRationalZero_map_iff {n d : ℕ}
    {G : MvPolynomial (Fin n) ℤ} (hG : G.IsHomogeneous d) :
    HasRationalZero (map (Int.castRingHom ℚ) G) ↔ HasIntegerZero G :=
  ⟨hasIntegerZero_of_hasRationalZero hG, hasRationalZero_of_hasIntegerZero⟩

/-- Multiplication of a polynomial by a nonzero scalar preserves precisely
its nonzero rational zeros. -/
theorem hasRationalZero_C_mul_iff {n : ℕ} (F : MvPolynomial (Fin n) ℚ)
    (c : ℚ) (hc : c ≠ 0) : HasRationalZero (C c * F) ↔ HasRationalZero F := by
  constructor
  · rintro ⟨x, hx, he⟩
    refine ⟨x, hx, ?_⟩
    rw [eval_mul, eval_C] at he
    exact (mul_eq_zero.mp he).resolve_left hc
  · rintro ⟨x, hx, he⟩
    exact ⟨x, hx, by simp [he]⟩

end CubicTenVariables
