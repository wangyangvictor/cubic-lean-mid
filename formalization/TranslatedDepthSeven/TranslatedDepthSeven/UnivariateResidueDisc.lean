import TranslatedDepthSeven.BivariateResidueDisc

/-!
# A univariate residue disc modulo a prime power

This is the one-parameter analogue of `BivariateResidueDisc`.  It is the
literal infinitesimal disc used at a smooth point of a curve.  Evaluation at
any integral lift of the closed point factors through the quotient by the
corresponding residue ideal power.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- The polynomial ring `ℤ[T]`, represented as a one-variable
multivariate polynomial ring so that the same ambient-polynomial APIs apply. -/
abbrev UnivariateIntPolynomial := MvPolynomial (Fin 1) ℤ

/-- Evaluation of an integral univariate polynomial modulo `n`. -/
def evalUnivariateIntPolynomialZMod (n : ℕ) (x : Fin 1 → ℤ) :
    UnivariateIntPolynomial →+* ZMod n :=
  MvPolynomial.eval₂Hom (Int.castRingHom (ZMod n))
    (fun i ↦ (x i : ZMod n))

theorem evalUnivariateIntPolynomialZMod_surjective
    (n : ℕ) (x : Fin 1 → ℤ) :
    Function.Surjective (evalUnivariateIntPolynomialZMod n x) := by
  intro z
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective z
  exact ⟨MvPolynomial.C m, by simp [evalUnivariateIntPolynomialZMod]⟩

theorem zmodPrimePowerReduction_comp_evalUnivariateIntPolynomialZMod
    (p a : ℕ) (ha : 0 < a) (x y : Fin 1 → ℤ)
    (hxy : ∀ i, (p : ℤ) ∣ x i - y i) :
    (zmodPrimePowerReduction p a ha).comp
        (evalUnivariateIntPolynomialZMod (p ^ a) x) =
      evalUnivariateIntPolynomialZMod p y := by
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [evalUnivariateIntPolynomialZMod, zmodPrimePowerReduction]
  · intro i
    simp only [RingHom.comp_apply, evalUnivariateIntPolynomialZMod,
      MvPolynomial.eval₂Hom_X', zmodPrimePowerReduction,
      ZMod.castHom_apply]
    rw [ZMod.cast_intCast
      (dvd_pow_self p (Nat.ne_zero_of_lt ha)) (x i)]
    rw [← sub_eq_zero, ← Int.cast_sub,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hxy i

/-- The maximal residue ideal of `ℤ[T]` at `y modulo p`. -/
def univariateResidueIdeal (p : ℕ) (y : Fin 1 → ℤ) :
    Ideal UnivariateIntPolynomial :=
  RingHom.ker (evalUnivariateIntPolynomialZMod p y)

/-- Reduction of the order-`a` univariate residue disc to its closed point. -/
def univariateResidueDiscReduction (p a : ℕ) (ha : 0 < a)
    (y : Fin 1 → ℤ) :
    (UnivariateIntPolynomial ⧸ univariateResidueIdeal p y ^ a) →+* ZMod p :=
  Ideal.Quotient.lift (univariateResidueIdeal p y ^ a)
    (evalUnivariateIntPolynomialZMod p y)
    (fun _ hf ↦ by
      apply RingHom.mem_ker.mp
      exact Ideal.pow_le_self (Nat.ne_zero_of_lt ha) hf)

theorem univariateResidueDiscReduction_surjective
    (p a : ℕ) (ha : 0 < a) (y : Fin 1 → ℤ) :
    Function.Surjective (univariateResidueDiscReduction p a ha y) := by
  intro z
  obtain ⟨f, hf⟩ := evalUnivariateIntPolynomialZMod_surjective p y z
  exact ⟨Ideal.Quotient.mk (univariateResidueIdeal p y ^ a) f, by
    simpa [univariateResidueDiscReduction] using hf⟩

set_option synthInstance.maxHeartbeats 100000 in
theorem ker_univariateResidueDiscReduction_pow_eq_bot
    (p a : ℕ) (ha : 0 < a) (y : Fin 1 → ℤ) :
    RingHom.ker (univariateResidueDiscReduction p a ha y) ^ a = ⊥ := by
  have hker : RingHom.ker (univariateResidueDiscReduction p a ha y) =
      (univariateResidueIdeal p y).map
        (Ideal.Quotient.mk (univariateResidueIdeal p y ^ a)) := by
    exact Ideal.ker_quotient_lift _ _
  rw [hker, ← Ideal.map_pow, Ideal.map_quotient_self]

set_option synthInstance.maxHeartbeats 100000 in
theorem ker_univariateResidueDiscReduction_isNilpotent
    (p a : ℕ) (ha : 0 < a) (y : Fin 1 → ℤ) :
    IsNilpotent (RingHom.ker (univariateResidueDiscReduction p a ha y)) :=
  ⟨a, ker_univariateResidueDiscReduction_pow_eq_bot p a ha y⟩

private theorem evalUnivariateIntPolynomialZMod_pow_mem_ker
    (p a : ℕ) (ha : 0 < a) (x y : Fin 1 → ℤ)
    (hxy : ∀ i, (p : ℤ) ∣ x i - y i)
    (f : UnivariateIntPolynomial)
    (hf : f ∈ univariateResidueIdeal p y ^ a) :
    evalUnivariateIntPolynomialZMod (p ^ a) x f = 0 := by
  let ev := evalUnivariateIntPolynomialZMod (p ^ a) x
  let red := zmodPrimePowerReduction p a ha
  have hmap : Ideal.map ev (univariateResidueIdeal p y) ≤ RingHom.ker red := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change (red.comp ev) g = 0
    rw [zmodPrimePowerReduction_comp_evalUnivariateIntPolynomialZMod
      p a ha x y hxy]
    exact RingHom.mem_ker.mp hg
  have hfmap : ev f ∈ Ideal.map ev (univariateResidueIdeal p y ^ a) :=
    Ideal.mem_map_of_mem ev hf
  rw [Ideal.map_pow] at hfmap
  have hpow := pow_le_pow_left' hmap a
  have : ev f ∈ RingHom.ker red ^ a := hpow hfmap
  rw [ker_zmodPrimePowerReduction_pow_eq_bot p a ha] at this
  exact this

/-- Evaluation at an integral lift `x` factors through the order-`a`
univariate residue disc. -/
def univariateResidueDiscEvaluation
    (p a : ℕ) (ha : 0 < a) (x y : Fin 1 → ℤ)
    (hxy : ∀ i, (p : ℤ) ∣ x i - y i) :
    (UnivariateIntPolynomial ⧸ univariateResidueIdeal p y ^ a) →+*
      ZMod (p ^ a) :=
  Ideal.Quotient.lift (univariateResidueIdeal p y ^ a)
    (evalUnivariateIntPolynomialZMod (p ^ a) x)
    (evalUnivariateIntPolynomialZMod_pow_mem_ker p a ha x y hxy)

theorem zmodPrimePowerReduction_comp_univariateResidueDiscEvaluation
    (p a : ℕ) (ha : 0 < a) (x y : Fin 1 → ℤ)
    (hxy : ∀ i, (p : ℤ) ∣ x i - y i) :
    (zmodPrimePowerReduction p a ha).comp
        (univariateResidueDiscEvaluation p a ha x y hxy) =
      univariateResidueDiscReduction p a ha y := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [univariateResidueDiscEvaluation,
      univariateResidueDiscReduction, evalUnivariateIntPolynomialZMod,
      zmodPrimePowerReduction]
  · intro i
    simp only [RingHom.comp_apply, univariateResidueDiscEvaluation,
      univariateResidueDiscReduction, Ideal.Quotient.lift_mk,
      evalUnivariateIntPolynomialZMod, MvPolynomial.eval₂Hom_X',
      zmodPrimePowerReduction, ZMod.castHom_apply]
    rw [ZMod.cast_intCast
      (dvd_pow_self p (Nat.ne_zero_of_lt ha)) (x i)]
    rw [← sub_eq_zero, ← Int.cast_sub,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hxy i

end

end TranslatedDepthSeven
