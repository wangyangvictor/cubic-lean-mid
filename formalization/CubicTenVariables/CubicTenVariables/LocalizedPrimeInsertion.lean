import CubicTenVariables.PrimeCoprimeSeries
import CubicTenVariables.LocalizedZeroCRT
import CubicTenVariables.OrdinaryLocalSeriesFactor

/-! Insert one restricted prime factor into the actual localized singular
series. The old series and the new local factor are the actual coefficients,
not abstract replacements. No assumption of normalized multiplicativity of
the localized coefficients is made. -/

noncomputable section
namespace CubicTenVariables.LocalizedPrimeInsertion
open MvPolynomial PrimeCoprimeSeries LocalizedZeroCRT
open scoped BigOperators

theorem old_split {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (p W : ℕ) (hp : p.Prime) (hW : 0 < W) (hc : Nat.Coprime W p)
    (Ω : Set (Fin n → ZMod W)) (k : ℕ) (m : CoprimePart p) :
    localizedSingularSeriesTerm F W Ω (p^k*m) =
      singularSeriesTerm F (p^k) * localizedSingularSeriesTerm F W Ω m := by
  letI : NeZero W := ⟨hW.ne'⟩
  letI : NeZero m.val := ⟨m.2.1⟩
  letI : NeZero (p^k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have h := localized_seriesTerm_mul_outside F m.val (p^k) W
    ((m.2.2.symm.mul_left hc).pow_right k) Ω
  simpa only [Nat.mul_comm, mul_comm] using h

theorem new_split {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (p M W : ℕ) (hp : p.Prime) (hW : 0 < W) (hc : Nat.Coprime W p)
    (Ω : Set (Fin n → ZMod W)) (Ωp : Set (Fin n → ZMod (p^M)))
    (k : ℕ) (m : CoprimePart p) :
    localizedSingularSeriesTerm F (W*p^M)
      (productRestriction (hc.pow_right M) Ω Ωp) (p^k*m) =
      localizedSingularSeriesTerm F (p^M) Ωp (p^k) *
        localizedSingularSeriesTerm F W Ω m := by
  letI : NeZero W := ⟨hW.ne'⟩
  letI : NeZero m.val := ⟨m.2.1⟩
  letI : NeZero (p^k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : NeZero (p^M) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcop : Nat.Coprime (m.val*W) (p^k*p^M) := by
    rw [← pow_add]
    exact (m.2.2.symm.mul_left hc).pow_right (k+M)
  have h := localized_seriesTerm_mul F m.val (p^k) W (p^M) hcop Ω Ωp
  simpa only [Nat.mul_comm, mul_comm] using h

/-- Absolute convergence and a strictly positive real sum survive insertion
of the actual positive restricted prime factor. -/
theorem insert_prime {n : ℕ} (F : MvPolynomial (Fin n) ℤ) (hn : 1 ≤ n)
    (p M W : ℕ) (hp : p.Prime) (hW : 0 < W) (hc : Nat.Coprime W p)
    (Ω : Set (Fin n → ZMod W)) (Ωp : Set (Fin n → ZMod (p^M)))
    (hordinary : SingularSeriesAbsolutelyConvergent F)
    (hold : Summable (fun q => ‖localizedSingularSeriesTerm F W Ω q‖))
    (S : ℝ) (hS : 0 < S) (holdValue : localizedSingularSeries F W Ω = (S : ℂ))
    (hlocal : Summable (fun k => ‖localizedSingularSeriesTerm F (p^M) Ωp (p^k)‖))
    (L : ℝ) (hL : 0 < L)
    (hlocalValue : (∑' k, localizedSingularSeriesTerm F (p^M) Ωp (p^k)) = (L : ℂ)) :
    Summable (fun q => ‖localizedSingularSeriesTerm F (W*p^M)
      (productRestriction (hc.pow_right M) Ω Ωp) q‖) ∧
    ∃ T : ℝ, 0 < T ∧ localizedSingularSeries F (W*p^M)
      (productRestriction (hc.pow_right M) Ω Ωp) = (T : ℂ) := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨σ,hσ,hσvalue⟩ :=
    OrdinaryLocalSeriesFactor.exists_nonnegative_localFactor F hn hordinary p
  have hv : Summable (fun m : CoprimePart p => ‖localizedSingularSeriesTerm F W Ω m‖) :=
    hold.subtype _
  let C : ℂ := ∑' m : CoprimePart p, localizedSingularSeriesTerm F W Ω m
  have he : (S : ℂ) = (σ : ℂ)*C := by
    have ht := tsum_of_split p hp (localizedSingularSeriesTerm F W Ω)
      (fun k => singularSeriesTerm F (p^k))
      (fun m : CoprimePart p => localizedSingularSeriesTerm F W Ω m)
      (by simp [localizedSingularSeriesTerm]) (old_split F p W hp hW hc Ω)
      (OrdinaryLocalSeriesFactor.summable_norm_prime_power F hordinary p hp) hv
    rw [hσvalue] at ht
    exact holdValue.symm.trans ht
  have hprod : 0 < σ*C.re := by
    have hre := congrArg Complex.re he
    simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul,
      sub_zero] at hre
    linarith
  have hCpos : 0 < C.re := by nlinarith
  have hσpos : 0 < σ := by nlinarith
  have hσC : (σ : ℂ) ≠ 0 := by exact_mod_cast hσpos.ne'
  have hC : C = ((S/σ : ℝ) : ℂ) := by
    rw [Complex.ofReal_div]
    apply (eq_div_iff hσC).mpr
    simpa only [mul_comm] using he.symm
  have habs := summable_norm_of_split p hp
    (localizedSingularSeriesTerm F (W*p^M) (productRestriction (hc.pow_right M) Ω Ωp))
    (fun k => localizedSingularSeriesTerm F (p^M) Ωp (p^k))
    (fun m : CoprimePart p => localizedSingularSeriesTerm F W Ω m)
    (new_split F p M W hp hW hc Ω Ωp) hlocal hv
  refine ⟨habs,L*(S/σ),mul_pos hL (div_pos hS hσpos),?_⟩
  have ht := tsum_of_split p hp
    (localizedSingularSeriesTerm F (W*p^M) (productRestriction (hc.pow_right M) Ω Ωp))
    (fun k => localizedSingularSeriesTerm F (p^M) Ωp (p^k))
    (fun m : CoprimePart p => localizedSingularSeriesTerm F W Ω m)
    (by simp [localizedSingularSeriesTerm]) (new_split F p M W hp hW hc Ω Ωp) hlocal hv
  change localizedSingularSeries F (W*p^M) _ = _ at ht
  rw [hlocalValue] at ht
  change localizedSingularSeries F (W*p^M) _ = (L : ℂ)*C at ht
  rw [hC, ← Complex.ofReal_mul] at ht
  exact ht

end CubicTenVariables.LocalizedPrimeInsertion
