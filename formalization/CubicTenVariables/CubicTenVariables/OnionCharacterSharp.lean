import CubicTenVariables.OnionFiniteBound
import CubicTenVariables.GcdWeightedHessianSharp
import CubicTenVariables.OnionModuli

/-! Uniform bounds for the actual partially constrained onion character sum. -/

noncomputable section
namespace CubicTenVariables.OnionCharacterSharp
open MvPolynomial HessianTheorem11 HessianKernelCRT WeightedHessianRootCRT
open scoped BigOperators

/-- The exact exponent combination after taking a square root. -/
theorem factored_exponents (m n d : ℕ) [NeZero m] [NeZero d] (ε U V K : ℝ) :
    (U*(m : ℝ)^(10+ε))*(V*(d : ℝ)^(6+ε))*(n : ℝ)^5*K =
      (U*V)*((m*n : ℕ) : ℝ)^5*((m*d : ℕ) : ℝ)^(5+ε)*
        (d : ℝ)*K := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast NeZero.pos m
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast NeZero.pos d
  have hm : (m : ℝ)^(10+ε) = (m : ℝ)^5*(m : ℝ)^(5+ε) := by
    rw [show (10:ℝ)+ε = 5+(5+ε) by ring, Real.rpow_add hm0]
    norm_num
  have hd : (d : ℝ)^(6+ε) = (d : ℝ)^(5+ε)*(d : ℝ) := by
    rw [show (6:ℝ)+ε=(5+ε)+1 by ring, Real.rpow_add hd0, Real.rpow_one]
  rw [hm,hd,Nat.cast_mul,Nat.cast_mul,mul_pow,Real.mul_rpow hm0.le hd0.le]
  ring

/-- One constant controls all factored moduli, units and integer frequencies.
Both finite geometric masses are proved, and no literature premise occurs. -/
theorem exists_uniform_factored_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (m n d : ℕ) [NeZero m] [NeZero n] [NeZero d],
      Squarefree m → Squarefree d → (hc : m.Coprime n) → (hd : d ∣ n) →
      ∀ (a : (ZMod (m*n))ˣ) (h : Fin 10 → ℤ),
      ‖partialRootCharacterMass F (m*n) (m*d) m
        (Nat.mul_dvd_mul (dvd_refl m) hd) (dvd_mul_right m n) (a : ZMod (m*n)) h‖ ≤
        C*((m*n : ℕ) : ℝ)^5*((m*d : ℕ) : ℝ)^(5+ε)*
          (d : ℝ)*Real.sqrt (kernelCard (hessian F h) (n/d) : ℝ) := by
  obtain ⟨U,hU,hroot⟩ := GcdWeightedHessianSharp.exists_uniform_root_mass_bound F hF hA ε hε
  obtain ⟨V,hV,hkernel⟩ := SquarefreeHessianMass.exists_uniform_kernel_mass_bound F hF hA (2*ε) (by positivity)
  refine ⟨U*V, by nlinarith [mul_le_mul_of_nonneg_left hV (zero_le_one.trans hU)], ?_⟩
  intro m n d _ _ _ hm hd hc hdn a h
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast NeZero.pos m
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast NeZero.pos d
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hV0 : 0 ≤ V := zero_le_one.trans hV
  let B := U*(m : ℝ)^(10+ε)
  let D := V*(d : ℝ)^(6+ε)
  let K : ℝ := kernelCard (hessian F h) (n/d)
  have hB : 0 ≤ B := mul_nonneg hU0 (Real.rpow_nonneg hm0.le _)
  have hD : 0 ≤ D := mul_nonneg hV0 (Real.rpow_nonneg hd0.le _)
  have hK : 0 ≤ K := Nat.cast_nonneg _
  have hr : rootMass F m ≤ B := hroot m hm
  have hk : (∑ x : Fin 10 → ZMod d, (hessianKernelCard F d x : ℝ)) ≤ D^2 := by
    have hmass : (∑ x : Fin 10 → ZMod d, (hessianKernelCard F d x : ℝ)) ≤
        V*(d : ℝ)^(12+2*ε) := by
      simpa only [Nat.cast_sum] using hkernel d hd
    have hV2 : V ≤ V^2 := by nlinarith [mul_le_mul_of_nonneg_left hV hV0]
    calc
      _ ≤ V*(d : ℝ)^(12+2*ε) := hmass
      _ ≤ V^2*(d : ℝ)^(12+2*ε) :=
        mul_le_mul_of_nonneg_right hV2 (Real.rpow_nonneg hd0.le _)
      _ = D^2 := by
        dsimp [D]
        rw [mul_pow,← Real.rpow_mul_natCast hd0.le]
        congr 2
        ring
  have hsq := OnionFiniteBound.norm_partialRootCharacterMass_sq_le F hF hc hdn a h
  have hmass : (rootMass F m)^2*(∑ x : Fin 10 → ZMod d, (hessianKernelCard F d x : ℝ)) ≤ B^2*D^2 :=
    mul_le_mul (pow_le_pow_left₀ (rootMass_nonneg F) hr 2) hk (by positivity) (sq_nonneg B)
  have hsq' :
      ‖partialRootCharacterMass F (m*n) (m*d) m
        (Nat.mul_dvd_mul (dvd_refl m) hdn) (dvd_mul_right m n) (a : ZMod (m*n)) h‖^2 ≤
        (B*D*(n : ℝ)^5*Real.sqrt K)^2 := by
    calc
      _ ≤ B^2*D^2*(n : ℝ)^10*K :=
        hsq.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hmass (by positivity)) hK)
      _ = _ := by rw [mul_pow,mul_pow,mul_pow,Real.sq_sqrt hK]; ring
  have hb : 0 ≤ B*D*(n : ℝ)^5*Real.sqrt K := by positivity
  have hnorm := (sq_le_sq₀ (norm_nonneg _) hb).mp hsq'
  exact hnorm.trans_eq (factored_exponents m n d ε U V (Real.sqrt K))

/-- The source's c,d-shaped character bound. The polynomial-zero
condition is imposed exactly modulo the prescribed factor d1; the
Hessian weight has modulus d, and the remaining kernel has modulus c/d. -/
theorem exists_uniform_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (c d : ℕ) [NeZero c] [NeZero d],
      ∀ (hd : Squarefree d) (hdc : d ∣ c) (a : (ZMod c)ˣ) (h : Fin 10 → ℤ),
      ‖partialRootCharacterMass F c d (SquarefreeResidueFactors.d1 c d) hdc
        (OnionModuli.d1_dvd_c c d (NeZero.pos c) hd hdc) (a : ZMod c) h‖ ≤
        C*(c : ℝ)^5*(d : ℝ)^(5+ε)*
          (SquarefreeResidueFactors.d2 c d : ℝ)*
            Real.sqrt (kernelCard (hessian F h) (c/d) : ℝ) := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_factored_bound F hF hA ε hε
  refine ⟨C,hC,?_⟩
  intro c d _ _ hd hdc a h
  have hmpos := OnionModuli.d1_pos c d (NeZero.pos c) hd hdc
  have hnpos := OnionModuli.c2_pos c d (NeZero.pos c) hd hdc
  have hepos := SquarefreeResidueFactors.d2_pos c d (NeZero.pos c) hd hdc
  have hmsq := OnionModuli.d1_squarefree c d (NeZero.pos c) hd hdc
  have hesq := SquarefreeResidueFactors.d2_squarefree c d (NeZero.pos c) hd hdc
  have hcm := OnionModuli.c_eq_d1_mul_c2 c d (NeZero.pos c) hd hdc
  have hde := OnionModuli.d_eq_d1_mul_d2 c d (NeZero.pos c) hd hdc
  have hen := OnionModuli.d2_dvd_c2 c d (NeZero.pos c) hd hdc
  have hcop := OnionModuli.coprime_d1_c2 c d (NeZero.pos c) hd hdc
  have hquot := OnionModuli.c2_div_d2 c d (NeZero.pos c) hd hdc
  have hmc := OnionModuli.d1_dvd_c c d (NeZero.pos c) hd hdc
  change ‖partialRootCharacterMass F c d (SquarefreeResidueFactors.d1 c d)
    hdc hmc (a : ZMod c) h‖ ≤ _
  generalize hm : SquarefreeResidueFactors.d1 c d = m at *
  generalize hn : OnionModuli.c2 c d = n at *
  generalize he : SquarefreeResidueFactors.d2 c d = e at *
  letI : NeZero m := ⟨hmpos.ne'⟩
  letI : NeZero n := ⟨hnpos.ne'⟩
  letI : NeZero e := ⟨hepos.ne'⟩
  subst c
  subst d
  simpa only [hquot] using hbound m n e hmsq hesq hcop hen a h

end CubicTenVariables.OnionCharacterSharp
