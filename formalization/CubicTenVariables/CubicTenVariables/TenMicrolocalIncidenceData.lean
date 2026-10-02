import CubicTenVariables.TenMicrolocalIncidence

/-! The geometric data and its ten-variable consequences with one shared
incidence witness. This adapter does not select an independently existing
geometry after proving the trace/depth conclusions: both come from the same
joint literature witness. All exact depth models use its enlarged common
bad-prime integer. No literature input is added. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.TenMicrolocalIncidenceData

open MvPolynomial HessianTheorem11
open BihomogeneousIncidenceFamily ProjectiveMicrolocalData
open ProjectiveMicrolocalModels RationalConeClosure
open ProjectiveFourierIdentity

/-- Assemble the previously proved conclusions from supplied geometric and
trace data and the nine exact models, all for the same incidence family. -/
theorem assemble_conclusion {t : ℕ} (F : MvPolynomial (Fin 10) ℤ)
    (hhom : F.IsHomogeneous 3) (hF : Anisotropic (map (Int.castRingHom ℚ) F))
    (f : Fin t → Polynomial 10 10) (N B : ℕ)
    (hgeom : Geometry F f) (hred : GoodReduction F f N B)
    (hmodels : ∀ i : Fin 9, ZDepthModel f (i.val+1) N) :
    TenMicrolocalIncidence.Conclusion F f N B := by
  constructor
  · exact ProjectiveMicrolocalModels.incidence_closed hgeom
  · exact incidence_point_scaling hgeom
  · exact incidence_normal_scaling hgeom
  · exact hgeom.incidenceAndGauss
  · exact hred.incidenceAndGauss
  · intro j hj hj9
    exact ⟨ProjectiveMicrolocalDepth.depth_closed hgeom (by omega),
      ProjectiveMicrolocalDepth.depth_cone hgeom j,
      ProjectiveMicrolocalDepth.depth_dimension_le hgeom (by omega)⟩
  · intro j hj hj9
    refine ⟨rationalDepth_closed j,rationalDepth_cone hgeom j,
      rationalDepth_subset hgeom (by omega),rationalDepth_points hgeom (by omega),?_⟩
    have hd := rationalDepth_dimension_le hgeom hF (j:=j) (by omega) (by omega)
    simpa only [show 10-(j+1) = 9-j by omega] using hd
  · intro j hj hj9
    obtain ⟨u,G,d,hd,hI,hIG,hpts,hrat,_⟩ :=
      exists_rational_depth_model hgeom hF (j:=j) (by omega) (by omega)
    exact ⟨u,G,d,hd,hI,hIG,hpts,hrat⟩
  · intro i
    exact hmodels i
  · intro K _ v
    exact ⟨ProjectiveMicrolocalNumericalDepth.depth_eq_max f K v,
      ProjectiveMicrolocalNumericalDepth.depth_le f K v⟩
  · intro p _ hp K _ _ _ ψ hψ v hv
    have hb := ProjectiveMicrolocalNumericalDepth.normalizedFourierSum_bound
      (by norm_num) F hhom (by norm_num) f N B hred p hp K ψ hψ v hv
    simpa only [Nat.cast_ofNat,show (10 : ℝ)-1 = 9 by norm_num] using hb
  · intro p _ hp v hv
    have hb := ProjectiveMicrolocalNumericalDepth.completeCubicSum_bound
      (by norm_num) F hhom (by norm_num) f N B hred p hp v hv
    simpa only [Nat.cast_ofNat,show (10 : ℝ)+1 = 11 by norm_num] using hb


/-- Joint geometric and numerical output from the two explicit literature
premises. The f appearing in Geometry and Conclusion is the same witness. -/
theorem exists_data
    (microlocal : Literature.ProjectiveMicrolocalCertificate)
    (F : MvPolynomial (Fin 10) ℤ) (hhom : F.IsHomogeneous 3)
    (hF : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ (t : ℕ) (f : Fin t → Polynomial 10 10) (N B : ℕ),
      1 ≤ N ∧ 1 ≤ B ∧ Geometry F f ∧ TenMicrolocalIncidence.Conclusion F f N B := by
  let FQ : AnisotropicCubic 10 := ⟨map (Int.castRingHom ℚ) F,hhom.map _,hF⟩
  have hne : F ≠ 0 := by
    intro hz
    have h := anisotropic_polynomial_ne_zero (by norm_num) FQ
    apply h
    simp [FQ,hz]
  obtain ⟨t,f,N₀,B,hN₀,hB,hgeom,hgood⟩ :=
    microlocal 10 3 (by norm_num) (by norm_num) F hne hhom
  obtain ⟨N₁,hN₁,hmodels⟩ := exists_uniform_ten_depth_models hgeom
  have hred : GoodReduction F f (N₀*N₁) B := by
    constructor
    · intro p _ hp K _ _
      exact hgood.incidenceAndGauss p
        (fun hdiv => hp (hdiv.trans (dvd_mul_right N₀ N₁))) K
    · intro p _ hp K _ _ _ v hv e he
      exact hgood.trace p (fun hdiv => hp (hdiv.trans (dvd_mul_right N₀ N₁))) K v hv e he
  refine ⟨t,f,N₀*N₁,B,by nlinarith,hB,hgeom,?_⟩
  exact assemble_conclusion F hhom hF f (N₀*N₁) B hgeom hred
    (fun i => (hmodels i).of_dvd (dvd_mul_left N₁ N₀))

end CubicTenVariables.TenMicrolocalIncidenceData
