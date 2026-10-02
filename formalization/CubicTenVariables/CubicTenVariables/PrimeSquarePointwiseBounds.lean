import CubicTenVariables.PrimeSquareCoarseBound

/-! One all-prime constant for both actual ten-variable prime-square
bounds. At primes dividing the original incidence exclusion, the uniform
p^17 bound absorbs the sharper depth exponent using the fixed factor N^6.
The nonzero-reduction hypothesis is retained explicitly; no membership of
the origin in a depth locus, or original W-stratification identity, is claimed.
-/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PrimeSquarePointwiseBounds
open MvPolynomial HessianTheorem11
open BihomogeneousIncidenceFamily ProjectiveMicrolocalData

/-- Both bounds use one constant, before every prime, frequency and depth.
The depth locus belongs to the very same incidence certificate. -/
theorem of_data (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    {t : ℕ} (F : MvPolynomial (Fin 10) ℤ) (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (f : Fin t → Polynomial 10 10) (N B : ℕ) (hN : 1 ≤ N)
    (hgeo : Geometry F f) (hData : TenMicrolocalIncidence.Conclusion F f N B) :
    ∃ C : ℝ, 1 ≤ C ∧
      (∀ (p : ℕ) [Fact p.Prime] (v : Fin 10 → ℤ),
        ‖completeCubicSum F (p^2) v‖ ≤ C*(p : ℝ)^17) ∧
      ∀ (p : ℕ) [Fact p.Prime] (v : Fin 10 → ℤ),
        (fun i => (v i : ZMod p)) ≠ 0 → ∀ j : ℕ,
        ¬ ((j+1 : ℕ) : Dimension) ≤
          IntegralGeometricFiberDepth.geometricFiberDimension f (ZMod p)
            (fun i => (v i : ZMod p)) →
        ‖completeCubicSum F (p^2) v‖ ≤ C*(p : ℝ)^(11+j) := by
  obtain ⟨Cc,hCc,hcoarse⟩ := PrimeSquareCoarseBound.of_data
    pointcount F hhom hAn f N B hN hgeo hData
  obtain ⟨Cd,hCd,hdepth⟩ := PrimeSquareMicrolocalBound.exists_off_depth_bound
    pointcount hhom hData
  let C : ℝ := max Cd (Cc*(N : ℝ)^6)
  have hN6 : 1 ≤ (N : ℝ)^6 := one_le_pow₀ (by exact_mod_cast hN)
  have hCcC : Cc ≤ C := by
    apply le_trans _ (le_max_right _ _)
    nlinarith
  have hCdC : Cd ≤ C := le_max_left _ _
  refine ⟨C,hCd.trans hCdC,?_,?_⟩
  · intro p _ v
    exact (hcoarse p v).trans (mul_le_mul_of_nonneg_right hCcC (by positivity))
  · intro p hp v hv j hoff
    by_cases hbad : p ∣ N
    · have hpN : (p : ℝ) ≤ N := by
        exact_mod_cast Nat.le_of_dvd (by omega : 0 < N) hbad
      have hp6 : (p : ℝ)^6 ≤ (N : ℝ)^6 :=
        pow_le_pow_left₀ (by positivity) hpN 6
      have hp11 : (p : ℝ)^11 ≤ (p : ℝ)^(11+j) :=
        pow_le_pow_right₀ (by exact_mod_cast hp.out.one_lt.le) (by omega)
      calc
        ‖completeCubicSum F (p^2) v‖ ≤ Cc*(p : ℝ)^17 := hcoarse p v
        _ = (Cc*(p : ℝ)^6)*(p : ℝ)^11 := by ring
        _ ≤ (Cc*(N : ℝ)^6)*(p : ℝ)^11 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hp6 (by linarith)) (by positivity)
        _ ≤ (Cc*(N : ℝ)^6)*(p : ℝ)^(11+j) :=
          mul_le_mul_of_nonneg_left hp11 (by positivity)
        _ ≤ C*(p : ℝ)^(11+j) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    · exact (hdepth p hbad v hv j hoff).trans
        (mul_le_mul_of_nonneg_right hCdC (by positivity))

/-- The microlocal/model hypotheses and proved prime-field count interface
construct one shared incidence together with both all-prime bounds. No arithmetic or
incidence conclusion is left as an application hypothesis. -/
theorem exists_bounds (microlocal : Literature.ProjectiveMicrolocalCertificate)
    (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    (F : MvPolynomial (Fin 10) ℤ) (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ (t : ℕ) (f : Fin t → Polynomial 10 10) (N B : ℕ),
      1 ≤ N ∧ 1 ≤ B ∧ Geometry F f ∧ TenMicrolocalIncidence.Conclusion F f N B ∧
      ∃ C : ℝ, 1 ≤ C ∧
        (∀ (p : ℕ) [Fact p.Prime] (v : Fin 10 → ℤ),
          ‖completeCubicSum F (p^2) v‖ ≤ C*(p : ℝ)^17) ∧
        ∀ (p : ℕ) [Fact p.Prime] (v : Fin 10 → ℤ),
          (fun i => (v i : ZMod p)) ≠ 0 → ∀ j : ℕ,
          ¬ ((j+1 : ℕ) : Dimension) ≤
            IntegralGeometricFiberDepth.geometricFiberDimension f (ZMod p)
              (fun i => (v i : ZMod p)) →
          ‖completeCubicSum F (p^2) v‖ ≤ C*(p : ℝ)^(11+j) := by
  obtain ⟨t,f,N,B,hN,hB,hgeo,hData⟩ :=
    TenMicrolocalIncidenceData.exists_data microlocal F hhom hAn
  exact ⟨t,f,N,B,hN,hB,hgeo,hData,of_data pointcount F hhom hAn f N B hN hgeo hData⟩

end CubicTenVariables.PrimeSquarePointwiseBounds
