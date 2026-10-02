import CubicTenVariables.FixedLeadingSurfaceLogarithmicAuxiliary
import CubicTenVariables.FixedLeadingSurfaceNormalizedPrimeCount
import CubicTenVariables.FixedPolynomialSubstitutionHeight

/-!
# Logarithmic auxiliaries for fixed-leading families

This combines the fixed normalization and finite-field point count with the
logarithmic auxiliary construction.  The exceptional integer is constructed
from the actual packet, as in `FixedLeadingSurfacePacketHeightAuxiliary`.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

namespace CubicTenVariables.FixedLeadingSurfaceLogarithmicPacketHeightAuxiliary

open MvPolynomial TranslatedDepthSeven Published
open FixedLeadingSurfaceCoordinateChoice FixedLeadingSurfaceCoordinateTransport
open FixedLeadingSurfaceNormalizedPrimeCount FixedPolynomialSubstitutionHeight

theorem exists_uniform_logarithmic_auxiliaryFamily_of_packet_height
    (integralityOpen : Literature.HomogeneousHypersurfaceIntegralityOpen)
    (curveWeil : Literature.AffinePlaneCurveWeil)
    {d e : ℕ} (hd : 2 ≤ d)
    (k₀ : MvPolynomial (Fin 3) ℤ) (hk₀ : k₀.IsHomogeneous d)
    (hirr : IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) k₀))
    (K : ℝ) (hK : 1 < K) (A : ℕ)
    (alpha : ℝ) (halpha : Real.sqrt K / Real.sqrt (d : ℝ) < alpha) :
    ∃ (a b : ℤ) (L : ℝ) (H₀ : ℕ),
      (coordinateMatrix a b).det = 1 ∧ 1 ≤ L ∧ 2 ≤ H₀ ∧
      ∀ (H B q : ℕ), H₀ ≤ H → 1 ≤ B → 1 ≤ q → q ≤ H ^ A →
      ∃ k : ℕ, 0 < k ∧
        (k : ℝ) ≤ 2 * L * Real.log (H : ℝ) *
          (1 + (B : ℝ) ^ alpha / (q : ℝ)) ∧
      ∀ (g : MvPolynomial (Fin 3) ℤ) (c : ℚ), c ≠ 0 →
        g.totalDegree ≤ d →
        map (Int.castRingHom ℚ) (homogeneousComponent d g) =
          C c * map (Int.castRingHom ℚ) k₀ →
        mvPolynomialCoefficientNatAbsMax g ≤ H ^ e →
        let F := projectiveEquiv a b (homogenize d g)
        ∀ (m S : ℕ) (u : Fin 3 → ℤ) (y : Fin S → Fin 3 → ℤ),
        m * q ≤ H ^ A → m ≠ 0 → Squarefree q →
        (∀ j i, (progressionHomogeneousPoint u m (y j) i).natAbs ≤ H) →
        (∀ j i, (y j i).natAbs ≤ B) →
        (∀ j, eval (progressionHomogeneousPoint u m (y j)) F = 0) →
        (∀ j, ∃ v, eval (fun i => u i + (m : ℤ) * y j i)
          (pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) ≠ 0) →
        (∀ p, p.Prime → p ∣ q → ¬ p ∣ m ∧
          ∃ (z : Fin 3 → ℤ) (v : Fin 3),
            (∀ j i, (p : ℤ) ∣ y j i - z i) ∧
            (eval (fun i => u i + (m : ℤ) * z i)
              (pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0) →
        ∃ Q : MvPolynomial (Fin 4) ℚ,
          Q.IsHomogeneous (d - 1 + k) ∧
          Q ∉ Ideal.span {map (Int.castRingHom ℚ) F} ∧
          ∀ j, eval (fun i => (progressionHomogeneousPoint u m (y j) i : ℚ)) Q = 0 := by
  obtain ⟨a, b, mu, D, hdet, hD, hmu, hnormal⟩ :=
    exists_normalized_prime_count integralityOpen curveWeil hd k₀ hk₀ hirr K hK
  obtain ⟨L, Haux, hL, hHaux, haux⟩ :=
    FixedLeadingSurfaceLogarithmicAuxiliary.exists_uniform_logarithmic_auxiliaryFamily
      (e := e + 1) (by omega : 0 < d) K hK.le (e + A + 1) alpha halpha
  let Cnorm := substitutionHeightConstant (coordinateEquiv a b).toAlgHom d
  let H₀ := max Haux (max Cnorm D)
  refine ⟨a, b, L, H₀, hdet, hL,
    hHaux.trans (Nat.le_max_left _ _), ?_⟩
  intro H B q hH hB hq hqheight
  have hHaux' : Haux ≤ H := (Nat.le_max_left _ _).trans hH
  have hCnorm : Cnorm ≤ H :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hH)
  have hDH : D ≤ H :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hH)
  have hH1 : 1 ≤ H := by omega
  have hqheight' : (q : ℝ) ≤ (H : ℝ) ^ ((e + A + 1 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hqheight.trans
      (Nat.pow_le_pow_right hH1 (by omega : A ≤ e + A + 1))
  obtain ⟨k, hk, hkbound, hfamily⟩ :=
    haux H B q hHaux' hB hq hqheight'
  refine ⟨k, hk, hkbound, ?_⟩
  intro g c hc hdegree htop hheight
  dsimp only
  intro m S u y hmqheight hm hsq hsource hbox hzero hgrad hlocal
  obtain ⟨hhom, hvariable, hchartDegree, hb, hbheight, hcount⟩ :=
    hnormal g c hc hdegree htop
  have hchartHeight : mvPolynomialCoefficientNatAbsMax
      (surfaceHypersurfaceFirstChartDehomogenize
        (projectiveEquiv a b (homogenize d g))) ≤ H ^ (e + 1) := by
    rw [firstChart_transformed_homogenize a b g hdegree]
    exact height_substitution_le_power (coordinateEquiv a b).toAlgHom d g hdegree
      hCnorm hheight
  let b₀ := ((homogeneousComponent d g).coeff mu).natAbs
  let Dex := D * b₀ * (m * q)
  have hb₀ : 0 < b₀ := Int.natAbs_pos.mpr hb
  have hDex : 0 < Dex :=
    Nat.mul_pos (Nat.mul_pos hD hb₀)
      (Nat.mul_pos (Nat.pos_of_ne_zero hm) (by omega))
  have hDexHeight : Dex ≤ H ^ (e + A + 1) := by
    calc
      Dex ≤ H * H ^ e * H ^ A :=
        Nat.mul_le_mul (Nat.mul_le_mul hDH (hbheight.trans hheight)) hmqheight
      _ = H ^ (e + A + 1) := by simp only [pow_add, pow_one]; ring
  have hmq : m * q ∣ Dex := dvd_mul_left _ _
  apply hfamily (projectiveEquiv a b (homogenize d g)) hvariable hchartDegree
    hchartHeight m S Dex u y hDex hDexHeight hmq hm (by omega) hsq
  · intro p hp hpDex
    exact hcount p hp (fun hpFixed => hpDex (hpFixed.trans (dvd_mul_right _ _)))
  · exact hsource
  · exact hbox
  · exact hzero
  · exact hgrad
  · exact hlocal

end CubicTenVariables.FixedLeadingSurfaceLogarithmicPacketHeightAuxiliary
