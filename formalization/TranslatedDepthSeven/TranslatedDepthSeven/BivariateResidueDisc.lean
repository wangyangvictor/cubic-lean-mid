import Mathlib

/-!
# A bivariate residue disc modulo a prime power

This file constructs the literal infinitesimal disc used to compare points
of a smooth surface which have the same reduction modulo `p`.  Its coordinate
ring is the quotient of `ℤ[U, V]` by the `a`-th power of the maximal residue
ideal at the common point modulo `p`.  Evaluation at any integral lift of that
point factors through the disc with values in `ZMod (p ^ a)`.

All maps below are actual ring homomorphisms.  In particular, no chosen
integer lift of a function on a localized chart is required.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- Reduction from `ZMod (p ^ a)` to `ZMod p`, for positive `a`. -/
def zmodPrimePowerReduction (p a : ℕ) (ha : 0 < a) :
    ZMod (p ^ a) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (Nat.ne_zero_of_lt ha)) (ZMod p)

theorem zmodPrimePowerReduction_surjective (p a : ℕ) (ha : 0 < a) :
    Function.Surjective (zmodPrimePowerReduction p a ha) :=
  ZMod.castHom_surjective _

theorem ker_zmodPrimePowerReduction_le_span (p a : ℕ) (ha : 0 < a) :
    RingHom.ker (zmodPrimePowerReduction p a ha) ≤
      Ideal.span {(p : ZMod (p ^ a))} := by
  intro z hz
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective z
  rw [RingHom.mem_ker] at hz
  have hz' : ((n : ZMod p)) = 0 := by
    simpa [zmodPrimePowerReduction] using hz
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz'
  rw [Ideal.mem_span_singleton]
  obtain ⟨m, rfl⟩ := hz'
  refine ⟨(m : ZMod (p ^ a)), ?_⟩
  push_cast
  ring

theorem ker_zmodPrimePowerReduction_pow_eq_bot
    (p a : ℕ) (ha : 0 < a) :
    RingHom.ker (zmodPrimePowerReduction p a ha) ^ a = ⊥ := by
  apply le_antisymm
  · calc
      RingHom.ker (zmodPrimePowerReduction p a ha) ^ a ≤
          Ideal.span {(p : ZMod (p ^ a))} ^ a :=
        pow_le_pow_left' (ker_zmodPrimePowerReduction_le_span p a ha) a
      _ = Ideal.span {((p : ZMod (p ^ a)) ^ a)} :=
        Ideal.span_singleton_pow _ _
      _ = ⊥ := by
        rw [← Nat.cast_pow, ZMod.natCast_self]
        simp
  · exact bot_le

theorem ker_zmodPrimePowerReduction_isNilpotent
    (p a : ℕ) (ha : 0 < a) :
    IsNilpotent (RingHom.ker (zmodPrimePowerReduction p a ha)) :=
  ⟨a, ker_zmodPrimePowerReduction_pow_eq_bot p a ha⟩

/-- The polynomial ring `ℤ[U, V]`. -/
abbrev BivariateIntPolynomial := MvPolynomial (Fin 2) ℤ

/-- Evaluation of an integral bivariate polynomial modulo `n`. -/
def evalBivariateIntPolynomialZMod (n : ℕ) (x : Fin 2 → ℤ) :
    BivariateIntPolynomial →+* ZMod n :=
  MvPolynomial.eval₂Hom (Int.castRingHom (ZMod n))
    (fun i ↦ (x i : ZMod n))

theorem evalBivariateIntPolynomialZMod_surjective
    (n : ℕ) (x : Fin 2 → ℤ) :
    Function.Surjective (evalBivariateIntPolynomialZMod n x) := by
  intro z
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective z
  exact ⟨MvPolynomial.C m, by simp [evalBivariateIntPolynomialZMod]⟩

theorem zmodPrimePowerReduction_comp_evalBivariateIntPolynomialZMod
    (p a : ℕ) (ha : 0 < a) (x y : Fin 2 → ℤ)
    (hxy : ∀ i, (p : ℤ) ∣ x i - y i) :
    (zmodPrimePowerReduction p a ha).comp
        (evalBivariateIntPolynomialZMod (p ^ a) x) =
      evalBivariateIntPolynomialZMod p y := by
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [evalBivariateIntPolynomialZMod, zmodPrimePowerReduction]
  · intro i
    simp only [RingHom.comp_apply, evalBivariateIntPolynomialZMod,
      MvPolynomial.eval₂Hom_X', zmodPrimePowerReduction,
      ZMod.castHom_apply]
    rw [ZMod.cast_intCast
      (dvd_pow_self p (Nat.ne_zero_of_lt ha)) (x i)]
    rw [← sub_eq_zero, ← Int.cast_sub,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hxy i

/-- The maximal residue ideal of `ℤ[U,V]` at the point `y modulo p`. -/
def bivariateResidueIdeal (p : ℕ) (y : Fin 2 → ℤ) :
    Ideal BivariateIntPolynomial :=
  RingHom.ker (evalBivariateIntPolynomialZMod p y)

/-- Reduction of the order-`a` bivariate residue disc to its closed point. -/
def bivariateResidueDiscReduction (p a : ℕ) (ha : 0 < a)
    (y : Fin 2 → ℤ) :
    (BivariateIntPolynomial ⧸ bivariateResidueIdeal p y ^ a) →+* ZMod p :=
  Ideal.Quotient.lift (bivariateResidueIdeal p y ^ a)
    (evalBivariateIntPolynomialZMod p y)
    (fun _ hf ↦ by
      apply RingHom.mem_ker.mp
      exact Ideal.pow_le_self (Nat.ne_zero_of_lt ha) hf)

theorem bivariateResidueDiscReduction_surjective
    (p a : ℕ) (ha : 0 < a) (y : Fin 2 → ℤ) :
    Function.Surjective (bivariateResidueDiscReduction p a ha y) := by
  intro z
  obtain ⟨f, hf⟩ := evalBivariateIntPolynomialZMod_surjective p y z
  exact ⟨Ideal.Quotient.mk (bivariateResidueIdeal p y ^ a) f, by
    simpa [bivariateResidueDiscReduction] using hf⟩

set_option synthInstance.maxHeartbeats 100000 in
theorem ker_bivariateResidueDiscReduction_pow_eq_bot
    (p a : ℕ) (ha : 0 < a) (y : Fin 2 → ℤ) :
    RingHom.ker (bivariateResidueDiscReduction p a ha y) ^ a = ⊥ := by
  have hker : RingHom.ker (bivariateResidueDiscReduction p a ha y) =
      (bivariateResidueIdeal p y).map
        (Ideal.Quotient.mk (bivariateResidueIdeal p y ^ a)) := by
    exact Ideal.ker_quotient_lift _ _
  rw [hker, ← Ideal.map_pow, Ideal.map_quotient_self]

set_option synthInstance.maxHeartbeats 100000 in
theorem ker_bivariateResidueDiscReduction_isNilpotent
    (p a : ℕ) (ha : 0 < a) (y : Fin 2 → ℤ) :
    IsNilpotent (RingHom.ker (bivariateResidueDiscReduction p a ha y)) :=
  ⟨a, ker_bivariateResidueDiscReduction_pow_eq_bot p a ha y⟩

private theorem evalBivariateIntPolynomialZMod_pow_mem_ker
    (p a : ℕ) (ha : 0 < a) (x y : Fin 2 → ℤ)
    (hxy : ∀ i, (p : ℤ) ∣ x i - y i)
    (f : BivariateIntPolynomial)
    (hf : f ∈ bivariateResidueIdeal p y ^ a) :
    evalBivariateIntPolynomialZMod (p ^ a) x f = 0 := by
  let ev := evalBivariateIntPolynomialZMod (p ^ a) x
  let red := zmodPrimePowerReduction p a ha
  have hmap : Ideal.map ev (bivariateResidueIdeal p y) ≤ RingHom.ker red := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change (red.comp ev) g = 0
    rw [zmodPrimePowerReduction_comp_evalBivariateIntPolynomialZMod
      p a ha x y hxy]
    exact RingHom.mem_ker.mp hg
  have hfmap : ev f ∈ Ideal.map ev (bivariateResidueIdeal p y ^ a) :=
    Ideal.mem_map_of_mem ev hf
  rw [Ideal.map_pow] at hfmap
  have hpow := pow_le_pow_left' hmap a
  have : ev f ∈ RingHom.ker red ^ a := hpow hfmap
  rw [ker_zmodPrimePowerReduction_pow_eq_bot p a ha] at this
  exact this

/-- Evaluation at an integral point `x` congruent to `y modulo p` factors
through the order-`a` residue disc. -/
def bivariateResidueDiscEvaluation
    (p a : ℕ) (ha : 0 < a) (x y : Fin 2 → ℤ)
    (hxy : ∀ i, (p : ℤ) ∣ x i - y i) :
    (BivariateIntPolynomial ⧸ bivariateResidueIdeal p y ^ a) →+*
      ZMod (p ^ a) :=
  Ideal.Quotient.lift (bivariateResidueIdeal p y ^ a)
    (evalBivariateIntPolynomialZMod (p ^ a) x)
    (evalBivariateIntPolynomialZMod_pow_mem_ker p a ha x y hxy)

theorem zmodPrimePowerReduction_comp_bivariateResidueDiscEvaluation
    (p a : ℕ) (ha : 0 < a) (x y : Fin 2 → ℤ)
    (hxy : ∀ i, (p : ℤ) ∣ x i - y i) :
    (zmodPrimePowerReduction p a ha).comp
        (bivariateResidueDiscEvaluation p a ha x y hxy) =
      bivariateResidueDiscReduction p a ha y := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [bivariateResidueDiscEvaluation,
      bivariateResidueDiscReduction, evalBivariateIntPolynomialZMod,
      zmodPrimePowerReduction]
  · intro i
    simp only [RingHom.comp_apply, bivariateResidueDiscEvaluation,
      bivariateResidueDiscReduction, Ideal.Quotient.lift_mk,
      evalBivariateIntPolynomialZMod, MvPolynomial.eval₂Hom_X',
      zmodPrimePowerReduction, ZMod.castHom_apply]
    rw [ZMod.cast_intCast
      (dvd_pow_self p (Nat.ne_zero_of_lt ha)) (x i)]
    rw [← sub_eq_zero, ← Int.cast_sub,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hxy i

end

end TranslatedDepthSeven
