import CubicTenVariables.FirstLiftSum
import CubicTenVariables.LocalizedSums

/-! First-lift cancellation with an actual fixed congruence restriction.
The restriction is preserved by the high digits, and a nonzero derivative
modulo the low orthogonality modulus forces the localized sum to vanish. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.LocalizedFirstLiftVanishing
open MvPolynomial FirstLiftPhase FirstLiftSum MixedRadixLifting
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

theorem integerResidue_add_smul (W M : ℕ) (hWM : W ∣ M)
    (y z : Fin n → ℤ) : integerResidue W (y+(M:ℤ) • z) = integerResidue W y := by
  have hM : (M : ZMod W) = 0 := (ZMod.natCast_eq_zero_iff M W).mpr hWM
  ext i
  simp [integerResidue,hM]

/-- The restriction may be any residue set; its modulus only has to divide
the low-digit modulus. Both scalar and vector high digits are summed. -/
theorem complete_sum_eq_zero_of_no_support (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (A M W : ℕ) [NeZero A] [NeZero M]
    (hAM : A ∣ M) (hWM : W ∣ M) (Ω : Set (Fin n → ZMod W))
    (hno : ∀ (a : Fin M), Nat.Coprime a.val M → ∀ y : Fin n → Fin M,
      integerResidue W (fun i => ((y i).val:ℤ)) ∈ Ω →
      ¬ supportCondition F A (a.val:ℤ) (fun i => ((y i).val:ℤ)) 0) :
    localizedCompleteCubicSum F (A*M) W Ω 0 = 0 := by
  have hWq : W ∣ A*M := hWM.trans (dvd_mul_left M A)
  have hlcm : Nat.lcm (A*M) W = A*M := Nat.lcm_eq_left_iff_dvd.mpr hWq
  unfold localizedCompleteCubicSum
  rw [hlcm]
  simp only [Pi.zero_apply,zero_mul,Finset.sum_const_zero,residueExponential_zero,mul_one]
  rw [sum_mixedRadix]
  apply Finset.sum_eq_zero
  intro a _
  simp_rw [coprime_mixedRadix_iff A M hAM]
  by_cases ha : Nat.Coprime a.val M
  · simp_rw [if_pos ha,sum_mixedRadixVector n A M]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro y _
    have hr (h : Fin n → Fin A) :
        integerResidue W (fun i => ((mixedRadixVectorEquiv n A M (y,h) i).val:ℤ)) =
          integerResidue W (fun i => ((y i).val:ℤ)) := by
      rw [mixedRadixVectorEquiv_intCast]
      exact integerResidue_add_smul W M hWM _ _
    simp_rw [hr]
    by_cases hy : integerResidue W (fun i => ((y i).val:ℤ)) ∈ Ω
    · simp_rw [if_pos hy]
      have hphase (e : Fin A) (h : Fin n → Fin A) :
          (mixedRadixEquiv A M (a,e)).val *
              eval (fun i => ((mixedRadixVectorEquiv n A M (y,h) i).val:ℤ)) F =
            integerPhase F ((a.val:ℤ)+(M:ℤ)*e.val)
              ((fun i => ((y i).val:ℤ))+(M:ℤ) • (fun i => ((h i).val:ℤ))) 0 := by
        rw [mixedRadixEquiv_intCast,mixedRadixVectorEquiv_intCast]
        simp [integerPhase]
      simp_rw [hphase]
      rw [sum_lifted_phase F hF A M hAM]
      exact if_neg (hno a ha y hy)
    · simp [hy]
  · simp [ha]

/-- One derivative failing the A-divisibility test on every allowed
representative is enough; no smoothness modulo the residue prime is assumed. -/
theorem complete_sum_eq_zero (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (A M W : ℕ) [NeZero A] [NeZero M]
    (hAM : A ∣ M) (hWM : W ∣ M) (Ω : Set (Fin n → ZMod W))
    (hderiv : ∀ y : Fin n → Fin M,
      integerResidue W (fun i => ((y i).val:ℤ)) ∈ Ω →
      ∃ i, ¬ (A:ℤ) ∣ eval (fun j => ((y j).val:ℤ)) (pderiv i F)) :
    localizedCompleteCubicSum F (A*M) W Ω 0 = 0 := by
  apply complete_sum_eq_zero_of_no_support F hF A M W hAM hWM Ω
  intro a ha y hy hs
  obtain ⟨i,hi⟩ := hderiv y hy
  have hd : (A:ℤ) ∣ (a.val:ℤ)*eval (fun j => ((y j).val:ℤ)) (pderiv i F) := by
    simpa only [Pi.zero_apply,add_zero] using hs.2 i
  apply hi
  apply Int.dvd_of_dvd_mul_right_of_gcd_one hd
  simpa using (ha.of_dvd_right hAM).symm

end CubicTenVariables.LocalizedFirstLiftVanishing
