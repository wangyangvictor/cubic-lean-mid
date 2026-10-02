import CubicTenVariables.NumericalConductorRadical
import CubicTenVariables.ConductorFixedFrequency
import CubicTenVariables.ConductorCoarsePointwise

/-! Sum the actual low-depth moduli after fixing the two high-depth parts.
The low-pair map is injective on each such fiber. Exact same-frequency CRT,
the proved fixed-frequency inverse-conductor estimate, and the coarse
high-modulus estimate give the bound without an averaging premise. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ConductorLowModulusFiber
open MvPolynomial NumericalPrimeDepth NumericalConductorRadical
open ConductorFixedFrequency
open scoped BigOperators

variable {F : MvPolynomial (Fin 10) ℤ} {C : ℝ}

private theorem low_high_coprime (h : CoarseBounds F C) (a b : ℕ)
    (ha : Squarefree a) (hb : Squarefree b) (hab : a.Coprime b) (v : Fin 10 → ℤ) :
    (primeLow h a v * (squareLow h b v)^2).Coprime
      (primeHigh h a v * (squareHigh h b v)^2) := by
  obtain ⟨h1,h2,_,h4,h5,_⟩ := parts_pairwise_coprime h a b ha hb hab v
  exact Nat.coprime_mul_iff_left.mpr
    ⟨Nat.coprime_mul_iff_right.mpr ⟨h1,h4.pow_right 2⟩,
      Nat.coprime_mul_iff_right.mpr ⟨h5.symm.pow_left 2,(h2.pow_left 2).pow_right 2⟩⟩

private theorem modulus_split (h : CoarseBounds F C) (a b : ℕ)
    (ha : Squarefree a) (hb : Squarefree b) (v : Fin 10 → ℤ) :
    a*b^2 = (primeLow h a v * (squareLow h b v)^2) *
      (primeHigh h a v * (squareHigh h b v)^2) := by
  calc
    a*b^2 = (primeLow h a v * primeHigh h a v) *
        (squareLow h b v * squareHigh h b v)^2 := by
      rw [← prime_reconstruction h a ha v,← square_reconstruction h b hb v]
    _ = _ := by ring

private theorem norm_split (h : CoarseBounds F C) (hF : F.IsHomogeneous 3)
    (a b : ℕ) (ha : Squarefree a) (hb : Squarefree b) (hab : a.Coprime b)
    (v : Fin 10 → ℤ) :
    ‖completeCubicSum F (a*b^2) v‖ =
      ‖completeCubicSum F (primeLow h a v * (squareLow h b v)^2) v‖ *
      ‖completeCubicSum F (primeHigh h a v * (squareHigh h b v)^2) v‖ := by
  rw [modulus_split h a b ha hb v]
  exact CompleteSumMultiplicativity.norm_mul F hF _ _ (low_high_coprime h a b ha hb hab v) v

/-- The high parts are fixed as actual numerical-depth prime products.
One constant precedes the frequency, real scale, high parts, and arbitrary
finite family of original squarefree coprime pairs. -/
theorem exists_bound {t : ℕ}
    {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
    {T : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)}
    {N d₀ : ℕ} {h : CoarseBounds F C}
    (hF : F.IsHomogeneous 3) (hc : MicrolocalConductorDepth.Conclusion F f T N C d₀ h)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ v : Fin 10 → ℤ, GoodFrequency F f T v →
      ∀ D : ℝ, 1 ≤ D → ∀ t1 t2 : ℕ, ∀ Q : Finset (ℕ × ℕ),
        (∀ x ∈ Q, 1 ≤ x.1 ∧ 1 ≤ x.2 ∧ Squarefree x.1 ∧ Squarefree x.2 ∧
          x.1.Coprime x.2 ∧ (x.1 : ℝ)*(x.2 : ℝ)^2 ≤ 2*D ∧
          primeHigh h x.1 v = t1 ∧ squareHigh h x.2 v = t2) →
        (∑ x ∈ Q, ‖completeCubicSum F (x.1*x.2^2) v‖) ≤
          M*(D*frequencyHeight v)^ε*D^((13 : ℝ)/2)*
            C^(t1.primeFactors.card+t2.primeFactors.card)*NumericalConductor.K h t1 t2 v := by
  classical
  obtain ⟨M₀,hM₀,hbound⟩ := ConductorFixedFrequency.exists_inverse_bound hF hc ε hε
  let M : ℝ := max 1 (M₀*(2 : ℝ)^ε*(2 : ℝ)^((13 : ℝ)/2))
  refine ⟨M,le_max_left _ _,?_⟩
  intro v hv D hD t1 t2 Q hQ
  have hC : 0 ≤ C := zero_le_one.trans h.constant_pos
  have hK : 0 ≤ NumericalConductor.K h t1 t2 v :=
    (NumericalConductor.K_pos h t1 t2 v).le
  have hheight : 0 ≤ frequencyHeight v := by
    dsimp [frequencyHeight]
    positivity
  by_cases hne : Q.Nonempty
  · obtain ⟨x₀,hx₀⟩ := hne
    obtain ⟨_,_,hsa₀,hsb₀,hab₀,hsize₀,hhigh₀,hhigh'₀⟩ := hQ x₀ hx₀
    have ht1 : 0 < t1 := hhigh₀ ▸ primeHigh_pos h x₀.1 v
    have ht2 : 0 < t2 := hhigh'₀ ▸ squareHigh_pos h x₀.2 v
    have hsf := parts_squarefree h x₀.1 x₀.2 hsa₀ hsb₀ v
    have hsf1 : Squarefree t1 := hhigh₀ ▸ hsf.2.1
    have hsf2 : Squarefree t2 := hhigh'₀ ▸ hsf.2.2.2
    have hcop : t1.Coprime t2 := by
      simpa only [hhigh₀,hhigh'₀] using
        (parts_pairwise_coprime h x₀.1 x₀.2 hsa₀ hsb₀ hab₀ v).2.2.2.2.2
    let H : ℝ := ((t1*t2^2 : ℕ) : ℝ)
    have hH1 : 1 ≤ H := by dsimp [H]; exact_mod_cast Nat.succ_le_iff.mpr (Nat.mul_pos ht1 (pow_pos ht2 2))
    have hH : 0 < H := zero_lt_one.trans_le hH1
    let X : ℝ := 2*D/H
    let low : ℕ × ℕ → ℕ × ℕ := fun x => (primeLow h x.1 v,squareLow h x.2 v)
    let Qlow : Finset (ℕ × ℕ) := Q.image low
    have hsplit (x : ℕ × ℕ) (hx : x ∈ Q) :
        (x.1 : ℝ)*(x.2 : ℝ)^2 = ((low x).1 : ℝ)*((low x).2 : ℝ)^2*H := by
      have he := modulus_split h x.1 x.2 (hQ x hx).2.2.1 (hQ x hx).2.2.2.1 v
      rw [(hQ x hx).2.2.2.2.2.2.1,(hQ x hx).2.2.2.2.2.2.2] at he
      dsimp only [low,H]
      exact_mod_cast he
    have hlow1 (x : ℕ × ℕ) : 1 ≤ ((low x).1 : ℝ)*((low x).2 : ℝ)^2 := by
      have ha : (1 : ℝ) ≤ (low x).1 := by exact_mod_cast primeLow_pos h x.1 v
      have hb : (1 : ℝ) ≤ (low x).2 := by exact_mod_cast squareLow_pos h x.2 v
      nlinarith [sq_nonneg ((low x).2 : ℝ)]
    have hHD : H ≤ 2*D := by
      have he := hsplit x₀ hx₀
      have hh := mul_le_mul_of_nonneg_right (hlow1 x₀) hH.le
      nlinarith
    have hX : 1 ≤ X := (le_div_iff₀ hH).mpr (by simpa using hHD)
    have hX0 : 0 ≤ X := zero_le_one.trans hX
    have hXle : X ≤ 2*D := by
      apply (div_le_iff₀ hH).mpr
      nlinarith
    have hXH : X*H = 2*D := div_mul_cancel₀ _ hH.ne'
    have hlowbound (x : ℕ × ℕ) (hx : x ∈ Q) :
        ((low x).1 : ℝ)*((low x).2 : ℝ)^2 ≤ 2*X := by
      have hxsize := (hQ x hx).2.2.2.2.2.1
      rw [hsplit x hx] at hxsize
      have he : ((low x).1 : ℝ)*((low x).2 : ℝ)^2 ≤ X :=
        (le_div_iff₀ hH).mpr hxsize
      linarith
    have hQlow : ∀ y ∈ Qlow,
        1 ≤ y.1 ∧ 1 ≤ y.2 ∧ Squarefree y.1 ∧ Squarefree y.2 ∧
          y.1.Coprime y.2 ∧ (y.1 : ℝ)*(y.2 : ℝ)^2 ≤ 2*X := by
      intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      have hs := parts_squarefree h x.1 x.2 (hQ x hx).2.2.1 (hQ x hx).2.2.2.1 v
      have hp := parts_pairwise_coprime h x.1 x.2 (hQ x hx).2.2.1
        (hQ x hx).2.2.2.1 (hQ x hx).2.2.2.2.1 v
      exact ⟨primeLow_pos h x.1 v,squareLow_pos h x.2 v,hs.1,hs.2.2.1,hp.2.2.1,
        hlowbound x hx⟩
    have hinj : Set.InjOn low (↑Q : Set (ℕ × ℕ)) := by
      intro x hx y hy he
      have ha := congrArg Prod.fst he
      have hb := congrArg Prod.snd he
      apply Prod.ext
      · calc
          x.1 = (low x).1*t1 := by
            simpa only [low,(hQ x hx).2.2.2.2.2.2.1] using
              prime_reconstruction h x.1 (hQ x hx).2.2.1 v
          _ = (low y).1*t1 := by rw [ha]
          _ = y.1 := by
            symm
            simpa only [low,(hQ y hy).2.2.2.2.2.2.1] using
              prime_reconstruction h y.1 (hQ y hy).2.2.1 v
      · calc
          x.2 = (low x).2*t2 := by
            simpa only [low,(hQ x hx).2.2.2.2.2.2.2] using
              square_reconstruction h x.2 (hQ x hx).2.2.2.1 v
          _ = (low y).2*t2 := by rw [hb]
          _ = y.2 := by
            symm
            simpa only [low,(hQ y hy).2.2.2.2.2.2.2] using
              square_reconstruction h y.2 (hQ y hy).2.2.2.1 v
    have hlowK (y : ℕ × ℕ) (hy : y ∈ Qlow) : NumericalConductor.K h y.1 y.2 v = 1 := by
      obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hy
      exact K_low_eq_one h x.1 x.2 v
    have hs : (∑ y ∈ Qlow, ‖completeCubicSum F (y.1*y.2^2) v‖) ≤
        M₀*(X*frequencyHeight v)^ε*X^((13 : ℝ)/2) := by
      have hi := hbound v hv X hX Qlow hQlow
      convert hi using 1
      apply Finset.sum_congr rfl
      intro y hy
      rw [hlowK y hy,div_one]
    have hexact : (∑ x ∈ Q, ‖completeCubicSum F (x.1*x.2^2) v‖) =
        ‖completeCubicSum F (t1*t2^2) v‖ *
          (∑ y ∈ Qlow, ‖completeCubicSum F (y.1*y.2^2) v‖) := by
      rw [Finset.mul_sum]
      rw [show (∑ y ∈ Qlow,
          ‖completeCubicSum F (t1*t2^2) v‖ * ‖completeCubicSum F (y.1*y.2^2) v‖) =
          ∑ x ∈ Q, ‖completeCubicSum F (t1*t2^2) v‖ *
            ‖completeCubicSum F ((low x).1*(low x).2^2) v‖ from
        Finset.sum_image (f := fun y : ℕ × ℕ =>
          ‖completeCubicSum F (t1*t2^2) v‖ * ‖completeCubicSum F (y.1*y.2^2) v‖) hinj]
      apply Finset.sum_congr rfl
      intro x hx
      simpa only [low,(hQ x hx).2.2.2.2.2.2.1,(hQ x hx).2.2.2.2.2.2.2,mul_comm] using
        norm_split h hF x.1 x.2 (hQ x hx).2.2.1 (hQ x hx).2.2.2.1
          (hQ x hx).2.2.2.2.1 v
    have hhigh := ConductorCoarsePointwise.complete_sum_bound h hF t1 t2 hsf1 hsf2 hcop v
    have hheightbound : (X*frequencyHeight v)^ε ≤
        (2 : ℝ)^ε*(D*frequencyHeight v)^ε := by
      calc
        _ ≤ (2*D*frequencyHeight v)^ε := Real.rpow_le_rpow (by positivity)
          (mul_le_mul_of_nonneg_right hXle hheight) hε.le
        _ = _ := by
          rw [mul_assoc,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity)]
    have hscale : H^((13 : ℝ)/2)*X^((13 : ℝ)/2) =
        (2 : ℝ)^((13 : ℝ)/2)*D^((13 : ℝ)/2) := by
      rw [← Real.mul_rpow hH.le hX0,mul_comm H X,hXH,
        Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by linarith : 0 ≤ D)]
    rw [hexact]
    calc
      _ ≤ (C^(t1.primeFactors.card+t2.primeFactors.card)*H^((13 : ℝ)/2)*
          NumericalConductor.K h t1 t2 v) *
          (M₀*(X*frequencyHeight v)^ε*X^((13 : ℝ)/2)) :=
        mul_le_mul hhigh hs (Finset.sum_nonneg fun y _ => norm_nonneg _)
          (by positivity)
      _ = (M₀*C^(t1.primeFactors.card+t2.primeFactors.card)*NumericalConductor.K h t1 t2 v)*
          (X*frequencyHeight v)^ε*(H^((13 : ℝ)/2)*X^((13 : ℝ)/2)) := by ring
      _ ≤ (M₀*C^(t1.primeFactors.card+t2.primeFactors.card)*NumericalConductor.K h t1 t2 v)*
          ((2 : ℝ)^ε*(D*frequencyHeight v)^ε)*
          ((2 : ℝ)^((13 : ℝ)/2)*D^((13 : ℝ)/2)) := by
        rw [hscale]
        gcongr
      _ = (M₀*(2 : ℝ)^ε*(2 : ℝ)^((13 : ℝ)/2))*(D*frequencyHeight v)^ε*D^((13 : ℝ)/2)*
          C^(t1.primeFactors.card+t2.primeFactors.card)*NumericalConductor.K h t1 t2 v := by ring
      _ ≤ _ := by
        gcongr
        exact le_max_right _ _
  · have he : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [he,Finset.sum_empty]
    have hM : 0 ≤ M := zero_le_one.trans (le_max_left _ _)
    positivity

end CubicTenVariables.ConductorLowModulusFiber
