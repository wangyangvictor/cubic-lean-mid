import CubicTenVariables.NumericalConductor
import CubicTenVariables.MicrolocalConductorDepth
import CubicTenVariables.GcdProductWindowSum
import CubicTenVariables.PrimeConstantEpsilonBound
import CubicTenVariables.PolynomialHeightDivisorBound

/-! The actual fixed-frequency inverse-conductor estimate. All local norm
estimates are supplied by the already proved common P/Q data; only the
polynomial-height divisibility certificates are used in the summation.
The result holds for any finite family of positive squarefree coprime pairs
with a*b²≤2D, so no dyadic decomposition is needed. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ConductorFixedFrequency
open MvPolynomial HessianTheorem11 TranslatedDepthSeven
open NumericalPrimeDepth ProjectiveMicrolocalData
open scoped BigOperators

def GoodFrequency {t : ℕ} (F : MvPolynomial (Fin 10) ℤ)
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10)
    (T : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1))
    (v : Fin 10 → ℤ) : Prop :=
  (fun i => (v i : ℚ)) ∈ MicrolocalPromotedPartition.part f
    (MicrolocalPartitionCounts.promotionFamily (fun i => (T i).open)) 0 ∧
  (fun i => (v i : ℚ)) ∈ MicrolocalSquarePartition.part f 0

def frequencyHeight (v : Fin 10 → ℤ) : ℝ := 2+‖fun i => (v i : ℝ)‖

private theorem height_one_le (v : Fin 10 → ℤ) : 1 ≤ frequencyHeight v := by
  dsimp [frequencyHeight]
  have h := norm_nonneg (fun i => (v i : ℝ))
  linarith

private theorem coordinate_le_height (v : Fin 10 → ℤ) (i : Fin 10) :
    |(v i : ℝ)| ≤ frequencyHeight v := by
  have h := norm_le_pi_norm (fun i => (v i : ℝ)) i
  rw [Real.norm_eq_abs] at h
  dsimp [frequencyHeight]
  linarith

/-- One constant precedes the frequency, real modulus scale, and arbitrary
finite positive squarefree coprime pair family. The summands are the actual
complete sums divided by the actual least-depth conductor. -/
theorem exists_inverse_bound {t : ℕ} {F : MvPolynomial (Fin 10) ℤ}
    {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
    {T : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)}
    {N : ℕ} {C : ℝ} {d : ℕ} {h : CoarseBounds F C}
    (hF : F.IsHomogeneous 3) (hc : MicrolocalConductorDepth.Conclusion F f T N C d h)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ v : Fin 10 → ℤ, GoodFrequency F f T v →
      ∀ D : ℝ, 1 ≤ D → ∀ Q : Finset (ℕ × ℕ),
        (∀ x ∈ Q, 1 ≤ x.1 ∧ 1 ≤ x.2 ∧ Squarefree x.1 ∧ Squarefree x.2 ∧
          x.1.Coprime x.2 ∧ (x.1 : ℝ)*(x.2 : ℝ)^2 ≤ 2*D) →
        (∑ x ∈ Q, ‖completeCubicSum F (x.1*x.2^2) v‖ /
          NumericalConductor.K h x.1 x.2 v) ≤
          M*(D*frequencyHeight v)^ε*D^((13 : ℝ)/2) := by
  classical
  obtain ⟨E,hE,hprime⟩ := PrimeConstantEpsilonBound.exists_two_factor_bound C h.constant_pos ε hε
  obtain ⟨L,hL,hdiv⟩ := PolynomialHeightDivisorBound.exists_product_bound C h.constant_pos d ε hε
  obtain ⟨R,hR,hwindow⟩ := GcdProductWindowSum.exists_bound
  let M : ℝ := max 1 (E*(2 : ℝ)^ε*R*L)
  refine ⟨M,le_max_left _ _,?_⟩
  intro v hv D hD Q hQ
  obtain ⟨Δ,hΔ,hΔheight,hΔprime⟩ := hc.prime_certificates 0 v hv.1
  obtain ⟨Θ,hΘ,hΘheight,hΘprime⟩ := hc.square_certificates 0 v hv.2
  have hτ : (Δ.divisors.card : ℝ)*(Θ.divisors.card : ℝ) ≤ L*(frequencyHeight v)^ε :=
    hdiv (frequencyHeight v) (height_one_le v) Δ Θ hΔ hΘ
      (hΔheight _ (height_one_le v) (coordinate_le_height v))
      (hΘheight _ (height_one_le v) (coordinate_le_height v))
  let w (x : ℕ × ℕ) : ℝ :=
    ((x.1 : ℝ)^((11 : ℝ)/2)*(Nat.gcd x.1 Δ : ℝ))*
      ((x.2 : ℝ)^11*(Nat.gcd x.2 Θ : ℝ)^2)
  have hw (x : ℕ × ℕ) : 0 ≤ w x := by dsimp [w]; positivity
  have hpoint (x : ℕ × ℕ) (hx : x ∈ Q) :
      ‖completeCubicSum F (x.1*x.2^2) v‖ / NumericalConductor.K h x.1 x.2 v ≤
        (E*(2*D)^ε)*w x := by
    obtain ⟨ha,hb,hsa,hsb,hab,hsize⟩ := hQ x hx
    have hbR : (1 : ℝ) ≤ x.2 := by exact_mod_cast hb
    have habD : ((x.1*x.2 : ℕ) : ℝ) ≤ 2*D := by
      rw [Nat.cast_mul]
      have hbs : (x.2 : ℝ) ≤ (x.2 : ℝ)^2 := by nlinarith
      exact (mul_le_mul_of_nonneg_left hbs (Nat.cast_nonneg x.1)).trans hsize
    have hcoeff : C^(x.1.primeFactors.card+x.2.primeFactors.card) ≤ E*(2*D)^ε :=
      (hprime x.1 x.2 ha hb).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) habD hε.le) (by linarith))
    have hl := NumericalConductor.norm_div_K_le_gcd h hF x.1 x.2 hsa hsb hab v Δ Θ
      (by simpa only [Fin.val_zero,zero_add] using hΔprime)
      (by simpa only [Fin.val_zero,zero_add] using hΘprime)
    calc
      _ ≤ C^(x.1.primeFactors.card+x.2.primeFactors.card)*w x := by
        convert hl using 1 <;> dsimp [w] <;> ring
      _ ≤ (E*(2*D)^ε)*w x := mul_le_mul_of_nonneg_right hcoeff (hw x)
  have hsum : (∑ x ∈ Q, w x) ≤ R*D^((13 : ℝ)/2)*
      (Δ.divisors.card : ℝ)*(Θ.divisors.card : ℝ) :=
    hwindow D hD Δ Θ hΔ hΘ Q (fun x hx =>
      ⟨(hQ x hx).1,(hQ x hx).2.1,(hQ x hx).2.2.2.2.2⟩)
  calc
    _ ≤ ∑ x ∈ Q, (E*(2*D)^ε)*w x := Finset.sum_le_sum hpoint
    _ = (E*(2*D)^ε)*(∑ x ∈ Q, w x) := (Finset.mul_sum ..).symm
    _ ≤ (E*(2*D)^ε)*(R*D^((13 : ℝ)/2)*(Δ.divisors.card : ℝ)*(Θ.divisors.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (E*(2*D)^ε*R*D^((13 : ℝ)/2))*
        ((Δ.divisors.card : ℝ)*(Θ.divisors.card : ℝ)) := by ring
    _ ≤ (E*(2*D)^ε*R*D^((13 : ℝ)/2))*(L*(frequencyHeight v)^ε) :=
      mul_le_mul_of_nonneg_left hτ (by positivity)
    _ = (E*(2 : ℝ)^ε*R*L)*(D*frequencyHeight v)^ε*D^((13 : ℝ)/2) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 0 ≤ D),
        Real.mul_rpow (by linarith : 0 ≤ D) (by have hh := height_one_le v; linarith)]
      ring
    _ ≤ M*(D*frequencyHeight v)^ε*D^((13 : ℝ)/2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg (mul_nonneg (by linarith)
          (by have hh := height_one_le v; linarith)) _)

/-- On a dyadic conductor band the actual unnormalized sum has the
required K0 loss. The bound has no radical cutoff or auxiliary coprimality. -/
theorem exists_band_bound {t : ℕ} {F : MvPolynomial (Fin 10) ℤ}
    {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
    {T : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)}
    {N : ℕ} {C : ℝ} {d : ℕ} {h : CoarseBounds F C}
    (hF : F.IsHomogeneous 3) (hc : MicrolocalConductorDepth.Conclusion F f T N C d h)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ v : Fin 10 → ℤ, GoodFrequency F f T v →
      ∀ D K0 : ℝ, 1 ≤ D → 1 ≤ K0 → ∀ Q : Finset (ℕ × ℕ),
        (∀ x ∈ Q, 1 ≤ x.1 ∧ 1 ≤ x.2 ∧ Squarefree x.1 ∧ Squarefree x.2 ∧
          x.1.Coprime x.2 ∧ (x.1 : ℝ)*(x.2 : ℝ)^2 ≤ 2*D ∧
          NumericalConductor.K h x.1 x.2 v < 2*K0) →
        (∑ x ∈ Q, ‖completeCubicSum F (x.1*x.2^2) v‖) ≤
          M*(D*frequencyHeight v)^ε*D^((13 : ℝ)/2)*K0 := by
  obtain ⟨M,hM,hbound⟩ := exists_inverse_bound hF hc ε hε
  refine ⟨2*M,by linarith,?_⟩
  intro v hv D K0 hD hK Q hQ
  have hs := hbound v hv D hD Q (fun x hx =>
    ⟨(hQ x hx).1,(hQ x hx).2.1,(hQ x hx).2.2.1,(hQ x hx).2.2.2.1,
      (hQ x hx).2.2.2.2.1,(hQ x hx).2.2.2.2.2.1⟩)
  have hpoint (x : ℕ × ℕ) (hx : x ∈ Q) :
      ‖completeCubicSum F (x.1*x.2^2) v‖ ≤
        (2*K0)*(‖completeCubicSum F (x.1*x.2^2) v‖ / NumericalConductor.K h x.1 x.2 v) := by
    have hk := NumericalConductor.K_pos h x.1 x.2 v
    have hh := mul_le_mul_of_nonneg_right ((hQ x hx).2.2.2.2.2.2.le)
      (div_nonneg (norm_nonneg (completeCubicSum F (x.1*x.2^2) v)) hk.le)
    have he : NumericalConductor.K h x.1 x.2 v *
        (‖completeCubicSum F (x.1*x.2^2) v‖ / NumericalConductor.K h x.1 x.2 v) =
        ‖completeCubicSum F (x.1*x.2^2) v‖ := by field_simp
    rwa [he] at hh
  calc
    _ ≤ ∑ x ∈ Q, (2*K0)*(‖completeCubicSum F (x.1*x.2^2) v‖ /
        NumericalConductor.K h x.1 x.2 v) := Finset.sum_le_sum hpoint
    _ = (2*K0)*(∑ x ∈ Q, ‖completeCubicSum F (x.1*x.2^2) v‖ /
        NumericalConductor.K h x.1 x.2 v) := (Finset.mul_sum ..).symm
    _ ≤ (2*K0)*(M*(D*frequencyHeight v)^ε*D^((13 : ℝ)/2)) :=
      mul_le_mul_of_nonneg_left hs (by linarith)
    _ = (2*M)*(D*frequencyHeight v)^ε*D^((13 : ℝ)/2)*K0 := by ring

end CubicTenVariables.ConductorFixedFrequency
