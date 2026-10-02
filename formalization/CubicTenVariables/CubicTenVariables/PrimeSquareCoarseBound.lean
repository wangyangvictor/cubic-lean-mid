import CubicTenVariables.PrimeSquareMicrolocalBound
import CubicTenVariables.PrimeSquareZeroBound
import CubicTenVariables.MicrolocalGoodCharacteristicDepthBound
import CubicTenVariables.PrimeSquareCoarseTransfer
import CubicTenVariables.TenMicrolocalIncidenceData

/-! The actual ten-variable prime-square sum is uniformly O(p^17), for
every prime and every integer frequency. Nonzero reductions use the same
microlocal incidence and its dimension-six bound; zero reductions use the
proved singular-residue count. A fixed exceptional integer is absorbed by
the elementary trivial bound. The microlocal/model hypotheses and proved
prime-field count interface stay explicit; no prime-square conclusion is assumed. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PrimeSquareCoarseBound
open MvPolynomial HessianTheorem11
open BihomogeneousIncidenceFamily ProjectiveMicrolocalData

/-- Assembly from one shared incidence witness. The resulting constant is
chosen before every prime and integer frequency, including bad primes and
frequencies divisible by the prime. -/
theorem of_data (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    {t : ℕ} (F : MvPolynomial (Fin 10) ℤ) (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (f : Fin t → Polynomial 10 10) (N B : ℕ) (hN : 1 ≤ N)
    (hgeo : Geometry F f) (hData : TenMicrolocalIncidence.Conclusion F f N B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : ℕ) [Fact p.Prime] (v : Fin 10 → ℤ),
      ‖completeCubicSum F (p^2) v‖ ≤ C * (p : ℝ)^17 := by
  obtain ⟨D,hD,hND,hdepth⟩ :=
    MicrolocalGoodCharacteristicDepthBound.exists_bound hgeo hhom hAn hData hN
  obtain ⟨C₁,hC₁,hbound⟩ := PrimeSquareMicrolocalBound.exists_bound pointcount F hhom f
  obtain ⟨C₀,hC₀,hzero⟩ := PrimeSquareZeroBound.exists_bound F hhom hAn
  apply PrimeSquareCoarseTransfer.exists_bound F D hD (max C₁ C₀)
    (hC₁.trans (le_max_left _ _))
  intro p _ hpD v
  by_cases hv : (fun i => (v i : ZMod p)) = 0
  · exact (hzero p v hv).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  · have hpN : ¬ p ∣ N := fun hd => hpD (hd.trans hND)
    have hb := hbound p (hData.good_incidence p hpN (ZMod p)) v hv 6
      (hdepth p hpD (ZMod p) (fun i => (v i : ZMod p)) hv)
    exact hb.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

/-- The unconditional-in-prime bound from the microlocal/model hypotheses
and the proved prime-field family count interface. The existence of the
actual incidence family is discharged here. -/
theorem exists_bound (microlocal : Literature.ProjectiveMicrolocalCertificate)
    (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    (F : MvPolynomial (Fin 10) ℤ) (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : ℕ) [Fact p.Prime] (v : Fin 10 → ℤ),
      ‖completeCubicSum F (p^2) v‖ ≤ C * (p : ℝ)^17 := by
  obtain ⟨t,f,N,B,hN,_,hgeo,hData⟩ :=
    TenMicrolocalIncidenceData.exists_data microlocal F hhom hAn
  exact of_data pointcount F hhom hAn f N B hN hgeo hData

end CubicTenVariables.PrimeSquareCoarseBound
