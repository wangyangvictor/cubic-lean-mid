import TranslatedDepthSeven.PrimitiveIntegralHypersurfaceClosure
import TranslatedDepthSeven.PrimitiveDirectionNormalization

/-!
# Primitive polynomial normalization without increasing coefficients

Normalize the finite vector of nonzero coefficients by its integer gcd.
This is independent of component extraction, elimination, and geometry.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped BigOperators

theorem exists_primitive_integral_polynomial_of_ne_zero
    {N : ℕ} (G : MvPolynomial (Fin N) ℤ) (hG : G ≠ 0) :
    ∃ P : MvPolynomial (Fin N) ℤ, ∃ r : ℚ,
      P ≠ 0 ∧ IsPrimitiveIntegralMvPolynomial P ∧ r ≠ 0 ∧
      P.map (Int.castRingHom ℚ) =
        MvPolynomial.C r * G.map (Int.castRingHom ℚ) ∧
      ∀ m, (P.coeff m).natAbs ≤ (G.coeff m).natAbs := by
  classical
  let s := G.support.card
  let E : Fin s ≃ G.support := G.support.equivFin.symm
  let exponent : Fin s → (Fin N →₀ ℕ) := fun i ↦ (E i).1
  let z : IntVector s := fun i ↦ G.coeff (exponent i)
  have hz : z ≠ 0 := by
    intro he
    obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.mpr hG
    let i := E.symm ⟨m, hm⟩
    have hi := congrFun he i
    have hc : G.coeff m = 0 := by simpa [z, exponent, i] using hi
    exact (MvPolynomial.mem_support_iff.mp hm) hc
  obtain ⟨h, r, hprimitive, hr, hscale, hbound⟩ :=
    exists_bounded_primitiveDirection_of_ne_zero z hz
  let P : MvPolynomial (Fin N) ℤ :=
    ∑ i, MvPolynomial.monomial (exponent i) (h i)
  have hsum : (∑ i, MvPolynomial.monomial (exponent i) (z i)) = G := by
    calc
      _ = ∑ m : G.support, MvPolynomial.monomial m.1 (G.coeff m.1) := by
        exact Equiv.sum_comp E
          (fun m : G.support ↦ MvPolynomial.monomial m.1 (G.coeff m.1))
      _ = ∑ m ∈ G.support, MvPolynomial.monomial m (G.coeff m) :=
        Finset.sum_coe_sort G.support
          (fun m ↦ MvPolynomial.monomial m (G.coeff m))
      _ = G := G.as_sum.symm
  have hsumQ :
      (∑ i, MvPolynomial.monomial (exponent i) (z i : ℚ)) =
        G.map (Int.castRingHom ℚ) := by
    simpa using congrArg (MvPolynomial.map (Int.castRingHom ℚ)) hsum
  have hmap : P.map (Int.castRingHom ℚ) =
      MvPolynomial.C r * G.map (Int.castRingHom ℚ) := by
    calc
      _ = ∑ i, MvPolynomial.monomial (exponent i) (h i : ℚ) := by simp [P]
      _ = ∑ i, MvPolynomial.C r *
          MvPolynomial.monomial (exponent i) (z i : ℚ) := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [MvPolynomial.C_mul_monomial, hscale i]
      _ = _ := by rw [← Finset.mul_sum, hsumQ]
  have hcoeff (m) : ((P.coeff m : ℤ) : ℚ) =
      r * ((G.coeff m : ℤ) : ℚ) := by
    simpa only [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul] using
      congrArg (MvPolynomial.coeff m) hmap
  have hcoeffi (i : Fin s) : P.coeff (exponent i) = h i := by
    have hi : ((P.coeff (exponent i) : ℤ) : ℚ) = (h i : ℚ) :=
      (hcoeff (exponent i)).trans (hscale i).symm
    exact_mod_cast hi
  have hP : P ≠ 0 := by
    intro he
    obtain ⟨i, hi⟩ := hprimitive.exists_ne_zero
    apply hi
    rw [← hcoeffi i, he]
    simp
  refine ⟨P, r, hP, ?_, hr, hmap, ?_⟩
  · intro n hn
    obtain ⟨c, hc⟩ := hprimitive
    apply isUnit_iff_dvd_one.mpr
    rw [← hc]
    apply Finset.dvd_sum
    intro i _hi
    exact dvd_mul_of_dvd_right (by rw [← hcoeffi i]; exact hn _) _
  · intro m
    by_cases hm : m ∈ G.support
    · let i := E.symm ⟨m, hm⟩
      have he : exponent i = m := by simp [exponent, i]
      have hi := hbound i
      simpa only [z, ← hcoeffi i, he] using hi
    · have hGm : G.coeff m = 0 := MvPolynomial.notMem_support_iff.mp hm
      have hPm : P.coeff m = 0 := by
        have hi := hcoeff m
        rw [hGm, Int.cast_zero, mul_zero] at hi
        exact_mod_cast hi
      simp [hPm]

end

end TranslatedDepthSeven
