import TranslatedDepthSeven.Salberger2023PrimeCover
import TranslatedDepthSeven.Salberger2023CertificatePrimePool
import TranslatedDepthSeven.Salberger2023CurveCountNumerics

/-!
# Uniform global counting with polynomial logarithmic certificates

This theorem assembles the finite prime cover, the proved prime supply and
exponent absorption.  The component degree may vary up to `Cd (1+log V)`.
The threshold is uniform in that degree, the point set, the equation, and
the integer certificates.  The local geometric facts are exposed as
literal statements about residue packets, not supplied as a global point
count.  They are furnished for plane curves by the local determinant and
smooth-residue calculations.
-/

namespace TranslatedDepthSeven

noncomputable section

open Filter
open scoped BigOperators Topology

set_option maxHeartbeats 1500000

/-- Uniform count at a prescribed prime exponent.  Choosing this exponent
externally permits the actual projected-box threshold to be supplied with
the same exponent; the constants are still independent of the varying
curve degree and of the certificates. -/
theorem eventually_count_of_polylog_certificates_at_exponent
    (A Cd Ce ε β : ℝ) (k e : ℕ)
    (hA : 0 ≤ A) (hCd : 0 ≤ Cd) (hCe : 0 ≤ Ce)
    (hβ : 0 < β) (hβε : β < ε / 2) :
      ∀ᶠ V : ℝ in atTop,
        ∀ (N δ : ℕ), (δ : ℝ) ≤ Cd * (1 + Real.log V) →
        ∀ (S : Finset (IntVector N)) (D : IntVector N → ℤ)
          (R : ∀ p : ℕ, Finset (Fin N → ZMod p)),
        (∀ z ∈ S, (D z).natAbs ≠ 0 →
          ((D z).natAbs : ℝ) ≤ V ^ (A * (1 + Real.log V) ^ k)) →
        (((S.filter (fun z ↦ D z = 0)).card : ℝ) ≤
          Ce * (1 + Real.log V) ^ e) →
        (∀ p : ℕ, p.Prime → 4 * V ^ β < (p : ℝ) → (p : ℝ) ≤ 8 * V ^ β →
          (∀ z ∈ S, ¬ (p : ℤ) ∣ D z → integralResidueVector z ∈ R p) ∧
          (R p).card ≤ δ * p ∧
          ∀ rho ∈ R p, (integralResiduePacket S rho).card ≤ δ ^ 2) →
        (S.card : ℝ) ≤ V ^ (ε / 2) := by
  let Cpool : ℝ := (A + 1) / β + 1
  let Ctotal : ℝ := Ce + 8 * Cpool * Cd ^ 3
  let m : ℕ := max e (k + 3)
  have hCpool : 0 ≤ Cpool := by dsimp only [Cpool]; positivity
  have hCtotal : 0 ≤ Ctotal := by dsimp only [Ctotal]; positivity
  filter_upwards [eventually_exists_curveCertificatePrimePool k hA hβ,
    eventually_polylog_mul_rpow_le_rpow Ctotal β (ε / 2) m hCtotal hβε,
    eventually_gt_atTop (1 : ℝ)] with V hpool habsorb hV
  intro N δ hdegree S D R hheight hexceptional hlocal
  obtain ⟨P, hPcard, hPrimes, havoid⟩ := hpool
  have hP : ∀ p ∈ P, p.Prime := fun p hp ↦ (hPrimes p hp).1
  have hlocalP : ∀ p ∈ P,
      (∀ z ∈ S, ¬ (p : ℤ) ∣ D z → integralResidueVector z ∈ R p) ∧
      (R p).card ≤ δ * p ∧
      ∀ rho ∈ R p, (integralResiduePacket S rho).card ≤ δ ^ 2 := by
    intro p hp
    obtain ⟨hpPrime, hpLow, hpHigh⟩ := hPrimes p hp
    exact hlocal p hpPrime hpLow hpHigh
  have hnat := card_le_exceptional_add_prime_residue_packets_of_avoidance
    S D P hP R (fun _ ↦ δ ^ 2)
    (fun z hz hnz ↦ havoid (D z) hnz
      (hheight z hz (Int.natAbs_ne_zero.mpr hnz)))
    (fun p hp ↦ (hlocalP p hp).1)
    (fun p hp ↦ (hlocalP p hp).2.2)
  have hraw : (S.card : ℝ) ≤ ((S.filter (fun z ↦ D z = 0)).card : ℝ) +
      ∑ p ∈ P, ((R p).card : ℝ) * (δ : ℝ) ^ 2 := by
    exact_mod_cast hnat
  let l : ℝ := 1 + Real.log V
  have hl : 1 ≤ l := by
    have := Real.log_pos hV
    dsimp only [l]
    linarith
  have hVpow : 1 ≤ V ^ β := Real.one_le_rpow hV.le hβ.le
  have hδ : (δ : ℝ) ≤ Cd * l := hdegree
  have hsumTerm : ∀ p ∈ P, ((R p).card : ℝ) * (δ : ℝ) ^ 2 ≤
      (8 * Cd ^ 3) * l ^ 3 * V ^ β := by
    intro p hp
    have hR : ((R p).card : ℝ) ≤ (δ : ℝ) * p := by
      exact_mod_cast (hlocalP p hp).2.1
    calc
      ((R p).card : ℝ) * (δ : ℝ) ^ 2 ≤
          ((δ : ℝ) * p) * (δ : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hR (sq_nonneg _)
      _ = (δ : ℝ) ^ 3 * p := by ring
      _ ≤ (Cd * l) ^ 3 * (8 * V ^ β) := by
        gcongr
        exact (hPrimes p hp).2.2
      _ = (8 * Cd ^ 3) * l ^ 3 * V ^ β := by ring
  have hsum : (∑ p ∈ P, ((R p).card : ℝ) * (δ : ℝ) ^ 2) ≤
      (8 * Cpool * Cd ^ 3) * l ^ (k + 3) * V ^ β := by
    calc
      (∑ p ∈ P, ((R p).card : ℝ) * (δ : ℝ) ^ 2) ≤
          ∑ _p ∈ P, (8 * Cd ^ 3) * l ^ 3 * V ^ β :=
        Finset.sum_le_sum hsumTerm
      _ = (P.card : ℝ) * ((8 * Cd ^ 3) * l ^ 3 * V ^ β) := by simp
      _ ≤ (Cpool * l ^ k) * ((8 * Cd ^ 3) * l ^ 3 * V ^ β) :=
        mul_le_mul_of_nonneg_right hPcard (by positivity)
      _ = (8 * Cpool * Cd ^ 3) * l ^ (k + 3) * V ^ β := by
        rw [pow_add]
        ring
  have hePow : l ^ e ≤ l ^ m := pow_le_pow_right₀ hl (Nat.le_max_left _ _)
  have hkPow : l ^ (k + 3) ≤ l ^ m := pow_le_pow_right₀ hl (Nat.le_max_right _ _)
  have hbound : (S.card : ℝ) ≤ Ctotal * l ^ m * V ^ β := by
    calc
      (S.card : ℝ) ≤ Ce * l ^ e +
          (8 * Cpool * Cd ^ 3) * l ^ (k + 3) * V ^ β :=
        hraw.trans (add_le_add hexceptional hsum)
      _ ≤ Ce * l ^ m * V ^ β +
          (8 * Cpool * Cd ^ 3) * l ^ m * V ^ β := by
        apply add_le_add
        · calc
            Ce * l ^ e ≤ Ce * l ^ m := mul_le_mul_of_nonneg_left hePow hCe
            _ ≤ Ce * l ^ m * V ^ β := le_mul_of_one_le_right (by positivity) hVpow
        · gcongr
      _ = Ctotal * l ^ m * V ^ β := by dsimp only [Ctotal]; ring
  exact hbound.trans habsorb

/-- Uniform high-degree count once the small-equation construction gives
polynomial logarithmic certificate heights.  This proves the desired
numerical estimate without any uniformity assumption on varying degrees.
-/
theorem eventually_highCurve_count_of_polylog_certificates
    (A Cd Ce ε : ℝ) (k e : ℕ)
    (hA : 0 ≤ A) (hCd : 0 ≤ Cd) (hCe : 0 ≤ Ce) (hε : 0 < ε) :
    ∃ β : ℝ, 0 < β ∧ β < ε / 2 ∧
      (∀ δ : ℕ, ⌈16 / ε⌉₊ < δ → 8 / ((δ : ℝ) + 3) ≤ β) ∧
      ∀ᶠ V : ℝ in atTop,
        ∀ (N δ : ℕ), (δ : ℝ) ≤ Cd * (1 + Real.log V) →
        ∀ (S : Finset (IntVector N)) (D : IntVector N → ℤ)
          (R : ∀ p : ℕ, Finset (Fin N → ZMod p)),
        (∀ z ∈ S, (D z).natAbs ≠ 0 →
          ((D z).natAbs : ℝ) ≤ V ^ (A * (1 + Real.log V) ^ k)) →
        (((S.filter (fun z ↦ D z = 0)).card : ℝ) ≤
          Ce * (1 + Real.log V) ^ e) →
        (∀ p : ℕ, p.Prime → 4 * V ^ β < (p : ℝ) → (p : ℝ) ≤ 8 * V ^ β →
          (∀ z ∈ S, ¬ (p : ℤ) ∣ D z → integralResidueVector z ∈ R p) ∧
          (R p).card ≤ δ * p ∧
          ∀ rho ∈ R p, (integralResiduePacket S rho).card ≤ δ ^ 2) →
        (S.card : ℝ) ≤ V ^ (ε / 2) := by
  obtain ⟨β, hβ, hβε, hβdegrees⟩ := exists_uniform_highCurve_primeExponent hε
  exact ⟨β, hβ, hβε, hβdegrees,
    eventually_count_of_polylog_certificates_at_exponent
      A Cd Ce ε β k e hA hCd hCe hβ hβε⟩

end

end TranslatedDepthSeven
